# Iteration in Tensor Logic

This document records the design decisions for expressing iterative recurrences
in pyncd's tensor logic DSL. It covers motivation, syntax, and the compiler
consistency checks that make the design statically safe. §6 sketches how these
decisions map onto the `TL`, `TensorProgram`, and `ConstructedModule` machinery.

---

## 1. Motivation

A broad class of computations — gradient descent, RNNs, dynamic programming,
Viterbi, belief propagation — is defined by a recurrence relation: the value of
a tensor at step `l+1` depends on its own value at step `l`.

A naive reading of the DSL suggests writing this directly as a tensor equation:

```python
tl.H[i, l+1] = tl.H[i, l] + lr * tl.Grad[i, l]
```

This does not work, for two compounding reasons.

The first is representational: einops contraction strings have no notion of
shifted axes. `l` and `l+1` are the same axis offset by one position, but
einops treats axis labels as opaque symbols — there is no string that means
"output's `l`-axis is input's `l`-axis shifted by one." The existing
`bc_signature()` machinery would have to emit something like
`... i l, ... i l -> ... i l` (treating `l` as a free axis, since it appears on
both sides), which is a simple elementwise copy — not a recurrence.

The second reason is fundamental: even if shifted-axis einsums were
representable, einsum evaluates all output indices simultaneously from a fixed
set of input tensors. To compute `H[i, l+1]` for all `l` at once, you would
need `H[i, l]` for all `l` to already exist as a concrete tensor. But for
`l > 0`, `H[i, l]` is itself part of the output being computed. The dependency
is inherently sequential — step `l+1` cannot begin until step `l` is complete
— and no static tensor contraction can encode this ordering.

The `Block` morphism handles a special case, but is subject to a strict
`dom = cod` constraint: the body morphism `f` must have the same domain and
codomain so that `f ∘ f ∘ … ∘ f` type-checks. A recurrence step naturally has
domain `(H_l, Grad_l)` — the current state together with a per-step external
input — and codomain `H_{l+1}`, the updated state alone. These are not equal,
so `Block` cannot type-check the recurrence directly. Absorbing `Grad` as a
parameter to recover `dom = cod` does not help either, because `Block` applies
the *same* morphism at every step: a per-step varying input such as `Grad[:, l]`
cannot be accommodated (§6.2 analyses both cases and introduces `Scan`).

The goal is to extend pyncd's DSL with a first-class notation for recurrences
that:

- fits the existing equation model without introducing a parallel syntax,
- makes the iterative structure statically visible (not inferred from runtime
  control flow),
- allows the compiler to validate the recurrence before any tensor is
  allocated, and
- composes naturally with the existing Bool semiring / Iverson predicate
  machinery.

---

## 2. Design Decisions

### 2.1 Declaration on the tensor, not the axis

The iterative semantics belong to the tensor being defined recursively, not to
the index variable. An axis `l` may appear in several tensors simultaneously
with different roles: as the iteration variable in a recurrent tensor, and as a
plain slice index in a pre-loaded input tensor. Attaching the declaration to
the tensor preserves this distinction.

The chosen syntax mirrors the existing `.predicate()` declaration:

```python
tl.Out.predicate(i, j)        # marks Out as Bool-typed over (i, j)
tl.H.iteration_axis(l)        # marks H as iteratively defined over l
```

Just as `.predicate()` does not change what `l` means to other tensors,
`.iteration_axis(l)` does not change the type of `l` itself. `l` remains a
plain `real_axis` and may appear freely in non-recurrent equations.

A special `iter_axis` type is therefore not needed and not introduced.

This stands in contrast to Domingos' tensor logic, where the iteration axis is
marked with a `*` annotation on the axis itself — making the iterative role a
property of the index variable rather than of the tensor being defined. The
pyncd approach avoids the ambiguity that arises when the same axis appears in
multiple tensors with different roles, and keeps the declaration co-located with
the tensor it governs.

### 2.2 Base case as a tensor equation

The initial condition is expressed as a tensor equation with a literal integer
at the `l` slot:

```python
tl.H[i, 0] = tl.X[i]
```

This means "the 0-th slice of `H` along `l` equals `X`." It is a first-class
equation in the `TL` registry, collected alongside the recurrence equation. The
initial condition can be an arbitrary tensor equation — a linear map, a
normalisation, or a copy — without requiring a dedicated `init=` parameter on
`iteration_axis`.

The compiler identifies the base case by detecting a literal integer at the `l`
slot of the LHS, and the recurrence by detecting `l+1` at that slot.

### 2.3 Explicit `l+1` on the LHS

The recurrence equation uses `l+1` on the LHS to mark the step being defined:

```python
tl.H[i, l+1] = tl.H[i, l] + lr * tl.Grad[i, l]
```

This is the standard mathematical convention for difference equations
(`H_{l+1} = f(H_l)`) made explicit at the DSL level. Requiring it — rather
than inferring "next step" from context — keeps the iterative structure visible
at the definition site and allows the compiler to reject equations that use `l`
on the LHS without an offset (which would be an ambiguous write to an arbitrary
slice).

`l+1` is implemented by `RawAxis.__add__(int)`, which returns a typed
`IterNextRef` object that `__setitem__` recognises. It is only valid at the `l`
slot of the LHS of a tensor declared with `.iteration_axis(l)`.

The symmetric operation `RawAxis.__sub__(int)` returns an `IterPrevRef` for use
on the RHS, supporting two-term recurrences that read two previous steps:

```python
tl.H[i, l+1] = tl.H[i, l] + tl.H[i, l-1]   # Fibonacci-style
```

A two-term recurrence requires two base case equations (one for `l=0` and one
for `l=1`). The compiler infers that the inductive step must start at `l=1`
— not `l=0` — because reading `H[i, l-1]` at `l=0` would reference the
non-existent slice `H[:, -1]`. The rule is: the recurrence starts at
`l = max_lookback`, where `max_lookback` is the largest offset among all
`IterPrevRef` references on the RHS (here, 1). The compiler checks that
exactly `max_lookback` base case equations are present.

```python
l = real_axis('l', 10)
tl.H[i, l+1] = tl.H[i, l] + tl.H[i, l-1]   # no bound predicate needed
```

Multi-step look-back is noted as out of scope for the current static design
(§5) but the `IterPrevRef` type anticipates it.

### 2.4 Semantics of `l` on the RHS

Within a recurrence equation, plain `l` on the RHS has two different roles
depending on which tensor it indexes:

| Tensor | Role of `l` on RHS | Memory contract |
| --- | --- | --- |
| Recurrent (`H`) | read current step — the running state from the previous iteration | one slice in memory at a time |
| Non-recurrent (`Grad`) | slice index — read the `l`-th entry of a pre-loaded tensor | full `l` dimension must be pre-loaded by the caller |

The distinction is determined by the declaration: any tensor that appears with
`l` on the RHS but has not been declared with `.iteration_axis(l)` is treated
as a pre-loaded input. No additional annotation is needed on the non-recurrent
tensor.

### 2.5 Iteration bounds from the axis declaration

The iteration count is determined by the size declared on the axis itself:

```python
l = real_axis('l', 10)    # l ∈ {0, …, 9} — 10 steps
tl.H.iteration_axis(l)
tl.H[i, 0] = tl.X[i]
tl.H[i, l+1] = tl.H[i, l] + lr * tl.Grad[i, l]
```

This is consistent with how every other axis is declared in pyncd:
`real_axis('i', 16)` gives `i` sixteen values; `real_axis('l', 10)` gives `l`
ten values. The iterative nature of `l` is declared on the tensor via
`iteration_axis`; the range of `l` is a property of the axis itself.

`iteration_axis` therefore takes no bounds parameter. The compiler reads the
step count directly from `l._size._value`. The lower bound is 0 by convention
and is cross-checked against the base case literal (§4.2).

Dynamic iteration counts (where `L` is determined at runtime by an input
tensor's shape) are out of scope and require a separate mechanism.

### 2.6 Coupled recurrences use Jacobi-style updates

When two tensors are both declared with `.iteration_axis(l)`, their updates are
treated as simultaneous: all RHS reads within a step use the values from step
`l`, and all writes produce the values at step `l+1`.

```python
l = real_axis('l', 10)
tl.H.iteration_axis(l)
tl.G.iteration_axis(l)
tl.H[i, l+1] = tl.H[i, l] + tl.G[i, l]
tl.G[i, l+1] = tl.G[i, l] * tl.H[i, l]   # uses H[i, l], not H[i, l+1]
```

This follows directly from the `l` convention: `l` on the RHS always means
"the value at the current step," regardless of whether that tensor's own
recurrence has already been evaluated. Gauss-Seidel ordering (where a later
equation in the same step reads an already-updated value) is not expressible
and not supported. This is a deliberate restriction: it keeps the semantics
independent of equation order and makes the update well-defined.

---

## 3. Full Syntax Summary

```python
# Declare axes
i = real_axis('i', 16)
l = real_axis('l', 10)                     # l ∈ {0, …, 9} — 10 steps

# Declare iterative tensor
tl.H.iteration_axis(l)

# Base case (literal 0 at the l slot)
tl.H[i, 0] = tl.X[i]

# Inductive step
tl.H[i, l+1] = tl.H[i, l] + lr * tl.Grad[i, l]
```

`X` is a pre-loaded input of shape `(I,)`. `Grad` is a pre-loaded input of
shape `(I, 10)` — the full `l` dimension, which the caller must supply. The
step count is read directly from `l._size._value = 10`.
`H` is the running state. The compiled module:

1. Initialises `H[:, 0]` from `X`.
2. For `l` in `[0, 9]`: computes `H[:, l+1]` from `H[:, l]` and `Grad[:, l]`.
3. Returns `H` of shape `(I, 11)` — initial state plus one slice per step.

Whether the full history or only the final state is returned is addressed in
§6.4.

---

## 4. Compiler Consistency Checks

The following checks can all be performed statically, before any tensor is
allocated or any module is constructed.

### 4.1 Axis must carry a concrete size

For a tensor declared with `.iteration_axis(l)`, the axis `l` must be a
`real_axis` with a concrete integer size — i.e. `l._size` must be an `Integer`,
not an unsized placeholder. The step count is `l._size._value` and the
iteration range is `[0, l._size._value - 1]`. An unsized `l` is a static error.

### 4.2 Base case literal must match the axis lower bound

The iteration range starts at 0 by convention. The base case equation must
have the literal `0` at the `l` slot. A mismatch — e.g. a base case at `l=2`
— leaves steps `0` and `1` undefined and is rejected. For two-term recurrences
using `IterPrevRef`, a second base case at `l=1` must also be present; the
compiler derives the required number of base cases from the maximum look-back
offset among all `IterPrevRef` references in the recurrence equation.

### 4.3 Exactly one base case and one recurrence per iterative tensor

Each tensor declared with `.iteration_axis(l)` must have exactly:

- one equation whose LHS has a literal integer at the `l` slot (base case), and
- one equation whose LHS has `l+1` at the `l` slot (inductive step).

Zero, or more than one, of either is an error.

### 4.4 `l+1` on the RHS is a causality violation

Within any recurrence equation over `l`, an expression `H[..., l+1]` on the
RHS reads a step that has not yet been computed. This is a static error. The
compiler scans all RHS index tuples for `IterNextRef` objects and rejects any
that appear.

### 4.5 `l` is not a contraction axis within a recurrence equation

`l` is the iteration variable. Within the recurrence equation it appears either
as a positional read of the running state (`H[i, l]`) or as a slice index of a
pre-loaded tensor (`Grad[i, l]`). It must not appear as a contracted axis (one
that is present on the RHS but absent from the LHS without an offset). If `l`
appears in a tensor on the RHS but not on the LHS in any form, the compiler
rejects the equation and reports that `l` cannot be contracted within a
recurrence.

### 4.6 Coupled recurrences must share the same axis

If two tensors are both declared with `.iteration_axis(l)`, they must reference
the identical `l` axis object — same `uid` and same `_size`. Declaring two
separate axes with the same name but different sizes and coupling them is
rejected. Because the iteration count is encoded in the axis declaration, this
check reduces to a single `uid` comparison rather than requiring bound
extraction from multiple equations.

### 4.7 Non-recurrent tensors must supply the full `l` dimension

Any non-recurrent input tensor indexed with `l` in a recurrence equation must
have a concrete size along `l` equal to `l._size._value`. The compiler verifies
this against the axis size at signature construction time.

---

## 5. Out of Scope (Static Case)

The following are deferred and not addressed by this design:

**Dynamic iteration count.** When the number of steps is determined at runtime
by an input tensor's shape, the Iverson predicate cannot express it. A
`steps=` parameter on `iteration_axis`, or inferring `L` from a sized input
axis, would handle this case but is left for a later design iteration.

**Multi-step look-back.** Recurrences of the form `H[i, l+1] = f(H[i, l], H[i, l-1])`
require reading two previous steps. The DSL types (`IterPrevRef`, base case
counting) are sketched in §2.3, but compiler and morphism support for this case
are not part of the current implementation.

**Non-sequential iteration order.** The compiled execution always steps `l`
from lower to upper in unit increments. Reverse-mode, stride-2, or arbitrary
permutation orderings are not expressible.

**Parallel scan optimisation.** Linear recurrences of the form
`H[i, l+1] = a * H[i, l] + b` can be evaluated in parallel using
`torch.associative_scan`. Recognising and applying this optimisation is a
compiler pass, not a DSL concern, and is left for future work (see §6.5).

---

## 6. DSL Changes and Br Morphism Representation

This section sketches what implementing the design requires at the DSL level and
how iterated recurrences map into the Br categorical framework. It also
identifies the points of significant complexity.

### 6.1 Required DSL changes

**New index reference types.** `RawAxis.__add__(int)` must return a typed
`IterNextRef(axis, offset)` object rather than raising an error or returning an
integer. `__setitem__` on `TensorProxy` recognises `IterNextRef` at an axis slot
and records a recurrence equation. Symmetrically, `RawAxis.__sub__(int)` returns
`IterPrevRef(axis, offset)` for use on the RHS in two-term recurrences.

**Literal integer at the iteration axis slot.** `TensorProxy.__setitem__`
currently expects `RawAxis` objects as indices. It must be extended to accept a
plain `int` at the iteration axis slot and record the resulting equation as a
base case, keyed by the literal value.

**`TensorProxy.iteration_axis(l)`.** A new method analogous to `.predicate()`.
It records `l` as the iteration axis for that tensor on the `TL` registry.

**Multiple equations per tensor.** The `TL` registry currently associates at
most one equation per LHS tensor name. Iterative tensors require two: the base
case and the recurrence. The registry must permit this for tensors declared with
`.iteration_axis()` and validate at `bc_signature()` time that exactly one of
each is present.

**Step count from axis size.** The iteration count is read directly from
`l._size._value`. No predicate extraction is required. The compiler validates
that `l` carries a concrete `Integer` size at `bc_signature()` time.

### 6.2 Block vs Scan: two categorical cases

The appropriate Br morphism depends on whether the recurrence body refers to any
non-recurrent tensor indexed by `l`.

**Pure state recurrence** — the RHS contains only the recurrent tensor and
constants:

```python
l = real_axis('l', 10)
tl.H[i, l+1] = f(tl.H[i, l])
```

The step body `f: H_slice → H_slice` has `dom = cod`. This fits the existing
`Block` morphism directly. The compiled module is `nn.Sequential` of `N` copies
of the step body, which is already supported.

**Recurrence with per-step external inputs** — the RHS also reads a pre-loaded
tensor at slice `l`:

```python
l = real_axis('l', 10)
tl.H[i, l+1] = tl.H[i, l] + lr * tl.Grad[i, l]
```

The natural step body takes `(H_slice, Grad_slice) → H_next_slice`, so
`dom = (State, InputSlice) ≠ cod = State`.

One might recover `dom = cod` by augmenting the state to carry the full `Grad`
tensor and a step counter, with the step body performing
`Grad_full[:, l_counter]` to extract the current slice. This is technically
valid but introduces dynamic integer indexing and counter increment — neither
of which is expressible as a `TensorEquation` einsum. New operator types would
be required in Br, and the complexity would exceed that of adding `Scan`
directly. The augmented state also inflates every step of the `nn.Sequential`
chain with a full tensor and a bookkeeping scalar that have no mathematical
meaning at the step level.

`Scan` is the honest abstraction: `dom ≠ cod` at the step level is resolved by
lifting the domain and codomain to the outer level
(`(StateInit, InputSequence) → StateSequence`), where the shape mismatch is
natural. A new `Scan` morphism is required (see Appendix for its categorical
status in Br and its interaction with weaves and reindexings; §6.6 for
rendering):

```python
@dataclass
class Scan(Morphism):
    step: Morphism   # (State, InputSlice) → State
    steps: int       # l._size._value
```

`Scan` is directly analogous to the functional programming primitives `foldl`
and `scanl`. `foldl f z [x_0, …, x_{N-1}]` computes
`s_{l+1} = f(s_l, x_l)` starting from `s_0 = z` and returns only the final
accumulator `s_N`; `scanl` returns the full sequence `[s_0, …, s_N]`. `Scan`
uses `scanl` semantics — always returning the full state history — for the
reasons given in §6.4.

`Block` is then the degenerate fold over a sequence of `N` unit inputs:
`foldl f z (repeat () N)` — the step body ignores its second argument, giving
`dom(step) = cod(step) = State`. The two morphisms unify as fold/scan with
different input sequences; `Block` is the special case where no per-step
external input exists.

`Scan` has domain `(StateInit, InputSequence)` and codomain `StateSequence`
(full state history; see §6.4). The base case morphism maps from the
base case inputs to `StateInit` and is composed before `Scan`:

```text
X ── BaseCase ──► H_0 ──┐
                        ├── Scan(step, N) ──► H
Grad ───────────────────┘
```

`Block` remains unchanged. `Scan` is a new sibling morphism and requires a new
`ConstructedScan` registered in `torch_compile`.

### 6.3 Step body extraction

The central algorithmic challenge is deriving the step body morphism from the
recurrence equation. Given:

```text
H[i, l+1] = H[i, l] + lr * Grad[i, l]
```

the compiler must produce a body morphism whose signature is:

- Input weaves: `[Weave(H_state, (i,)), Weave(Grad_slice, (i,))]`
- Output weaves: `[Weave(H_out, (i,))]`
- Operator: `TensorEquation` for `H_out[i] = H_state[i] + lr * Grad_slice[i]`

The transformation is a single rewriting pass: every tensor reference
`T[..., l, ...]` becomes `T_local[...]` with the `l` slot removed. The role
of each stripped reference is determined by the tensor's `iteration_axis`
declaration and the form of the `l` reference:

- `l+1` on the LHS → output proxy
- plain `l` on a tensor declared with `.iteration_axis(l)` → state input
- plain `l` on any other tensor → per-step input

This classification determines the input weave structure of the step body.

### 6.4 Compilation to PyTorch

`ConstructedScan.__init__` builds one compiled sub-module and records one
integer:

- `self.step` — a `ConstructedModule` compiled from the step body extracted
  in §6.3, mapping `(H_l, Grad_l) → H_{l+1}`. It is a regular Br morphism
  with its own weaves and reindexings.
- `self.steps` — the step count `N = l._size._value`, fixed at construction
  time from the recurrence axis declaration.

The base case morphism is **not** part of `ConstructedScan`. As shown in the
§6.2 diagram, it is compiled separately and composed before `Scan` in the
enclosing `ConstructedComposed` chain: the caller receives `H_0` already
computed and passes it directly to `ConstructedScan.forward`.

Unlike `ConstructedTensorEquation`, no reindexing constants are stored as
buffers. The recurrence axis L is managed dynamically: at each iteration `l`,
`Grad[..., l]` realises the element morphism `⟨l| : 1 → L`, selecting the
l-th input slice. Because `l` advances at runtime rather than being fixed at
construction time, this is not a static `StrideMorphism` and cannot appear as
a weave entry or reindexing constant (see Appendix A.4). The step body
extraction in §6.3 is responsible for ensuring L occupies the trailing axis
of each per-step input tensor, so that `tensor[..., l]` is always the correct
slice; symmetrically, `torch.stack(states, dim=-1)` places L' on the trailing
axis of the output.

`ConstructedScan.forward` for the single-state, single-input case:

```python
def forward(self, H_0, Grad):
    # H_0 is the initial state, already produced by the base case morphism
    states = [H_0]
    for l in range(self.steps):           # N iterations
        H_0 = self.step(H_0, Grad[..., l])   # ⟨l|: l-th input slice
        states.append(H_0)
    return torch.stack(states, dim=-1)    # shape (*S, N+1) = S⊗L'
```

**Multiple per-step inputs.** If the recurrence reads more than one
non-recurrent tensor indexed by `l` (e.g. both `Grad[i, l]` and `LR[l]`),
`forward` receives one sequence tensor per such input and slices each at `l`:

```python
H_0 = self.step(H_0, Grad[..., l], LR[..., l])
```

**Coupled recurrences.** When two tensors are both declared with
`.iteration_axis(l)`, the step body returns a tuple of states. `states`
becomes a list of tuples, and the stack must be applied per tensor:

```python
def forward(self, H_0, G_0, Grad):
    state = (H_0, G_0)
    states = [state]
    for l in range(self.steps):
        state = self.step(*state, Grad[..., l])
        states.append(state)
    return tuple(
        torch.stack([s[k] for s in states], dim=-1)
        for k in range(len(states[0]))
    )
```

All three variants return the full state history. In the ML context pyncd
targets, `scanl` semantics are the common case: sequence models need `H[:, l]`
at every position, attention mechanisms contract over the full state sequence,
and DP algorithms require traceback through all intermediate states. Even when
the forward pass uses only the final state, backpropagation through time
requires all intermediates to be stored anyway — PyTorch's autograd does this
regardless of what `Scan` returns. The simplest correct default is for `Scan`
to always return `StateSequence` of shape `(I, N+1)` and allow downstream
equations to index or contract over `l` as needed. Final-state-only output
(`StateFinal` of shape `(I,)`) can be recovered as a compiler optimisation when
use analysis confirms the full history is never consumed, but it is not required
for correctness and need not block the initial implementation.

### 6.5 Complexities

**Step body extraction is the core difficulty.** The `l` axis appears in the
outer `TensorProgram` but must be absent from the step body's weave types.
Implementing this requires a rewriting pass over the `TensorEquation` that
renames tensor references, removes the `l` slot from their index tuples, and
rebuilds the `bc_signature` of the body without the iteration axis. This is
substantially more involved than any existing morphism construction.

*Resolution.* The step body is produced by a static rewriting pass over the
recurrence `TensorEquation` inside `bc_signature()`: each tensor reference is
renamed to a stripped proxy and its index tuple is projected to remove the `l`
slot — references using `l` on recurrent tensors become state-input proxies,
those using `l` on non-recurrent tensors become per-step-input proxies, and
the reference using `l+1` on the LHS becomes the output proxy. The resulting
stripped equation feeds directly into the existing `ConstructedTensorEquation`
machinery without any new compilation path.

**`Block` vs `Scan` determination requires tensor classification.** The compiler
must inspect all RHS tensor references in the recurrence equation, classify each
as recurrent (state) or non-recurrent (per-step input), and select the
appropriate morphism. A recurrence equation with only recurrent tensors on the
RHS maps to `Block`; any non-recurrent tensor indexed by `l` forces `Scan`. The
classification must account for tensors that appear in both the base case and
the recurrence with different roles.

*Resolution.* A single pass over all RHS tensor references in the recurrence
equation at `bc_signature()` time consults the TL registry: references to
tensors with an `iteration_axis` declaration are classified as state inputs;
references to tensors without it that are indexed by `l` are classified as
per-step inputs. The base case equation is a separate registry entry keyed by
the literal integer, and plays no role in this classification. If the
per-step-input set is empty the compiler emits `Block`; otherwise it emits
`Scan`.

**Coupled recurrences require a product step body.** When `H` and `G` are both
declared with `.iteration_axis(l)`, their recurrence equations must be assembled
into a single step body with product output `(H_next, G_next)`. The step body
classification and extraction must handle multiple simultaneous LHS tensors.
This can be modeled using the existing `ProductOfMorphisms` structure, but the
assembly logic is new.

*Resolution.* When multiple tensors share the same iteration-axis `uid`
(guaranteed by §4.6), the extraction pass runs over all their recurrence
equations simultaneously with input sets unioned; the result is a
`ProductOfMorphisms` step body whose factors are the stripped `TensorEquation`
for each recurrent tensor, one per LHS. `ConstructedProduct` handles runtime
dispatch for the product step body without modification; the only new logic is
the multi-equation variant of the extraction pass.

**`torch.compile` transparency.** A Python `for` loop in `ConstructedScan.forward`
is not FX-graph-transparent. `torch.compile` will attempt to trace through it,
either unrolling (safe for small `N`, produces large graphs for large `N`) or
treating it as a loop (graph break). For large `N`, the preferred strategy is
`torch.associative_scan` for linear recurrences, but recognising linearity
requires a separate structural analysis pass and is out of scope for the initial
implementation. The sequential loop is correct in all cases and is the
appropriate starting point.

*Resolution.* Apply `torch._dynamo.disable` to `ConstructedScan.forward` to
produce a predictable graph break rather than unbounded loop unrolling. A
subsequent compiler pass may lower to `torch.associative_scan` (with
`combine_mode='generic'` for CPU compatibility) when a structural check on the
step body's `TensorEquation` confirms linearity of the form
`H_next = A * H + b`; linear recurrences expressed as affine maps are
associative and are exactly the use case `associative_scan` targets. This path
can be added without changing the `ConstructedScan` interface and is explicitly
deferred from the initial implementation.

**Composition with the base case morphism.** The full `Scan` pipeline composes
the base case morphism (`X → H_0`) with the scan proper (`(H_0, Grad) →
H_sequence`). In Br, this requires a `Composed` or `ProductOfMorphisms`
wrapper that routes `X` through the base case and passes `Grad` directly to
`Scan`. The base case morphism is itself a `TensorEquation` compiled normally;
the complication is the routing plumbing.

*Resolution.* The routing follows a fixed pattern: `ProductOfMorphisms(BaseCase,
id_Grad)` maps `(X, Grad)` to `(H_0, Grad)` and is placed before `Scan` in a
`Composed` chain. `id_Grad` is a `Rearrangement` identity on the per-step
inputs — an existing combinator requiring no new type. The compiler
auto-generates this wrapper using the input partition already computed during
the `Block`/`Scan` selection pass: base-case inputs feed `BaseCase`; per-step
inputs become `id_Grad`. Bypassing an early stage with an identity is the
standard `Composed` pattern and introduces no `Scan`-specific plumbing.

### 6.6 Visual rendering

`Block` is rendered by `BlockBox` as a padded rectangle with an optional title
annotation and `[` `]` brackets annotated with the repetition count. `Scan`
cannot reuse this convention unchanged because two things differ:

1. *The step body's wire types do not match `Scan`'s outer wire types.* The
   step body diagram shows wires of type `([a, S], [b, X])` on the left and
   `[a, S]` on the right. `Scan`'s outer left wires are `([a, S], [b, X⊗L])`
   and its outer right wire is `[a, S⊗L']`. The L and L' axes exist only at
   the `Scan` level — they do not appear inside the step body box. A `ScanBox`
   must render the outer L and L' axis labels on the enclosing bracket, not on
   the inner wires.

2. *The state feedback is the defining visual content.* In `Block`, the wires
   pass straight through because `dom = cod`. In `Scan`, the state wire is
   carried from the step body's right side back to its left side at the next
   step — a feedback loop. This needs a distinct visual marker: a curved or
   looped arrow on the state wire inside the bracket, absent from `Block`.

A `ScanBox` should therefore draw the same padded rectangle and bracket
notation as `BlockBox` (reusing `block_padding`, `draw_left_bracket`,
`draw_right_bracket`), augment the bracket annotation with the step count N
and the recurrence axis label L, and add a feedback arrow on the state wire
within the bracket to visually distinguish it from `Block`.

---

## Appendix: Categorical Status of `Scan` in Br

### A.1 The core axioms `Scan` satisfies

Let `a` and `b` be Br datatypes (e.g. `Reals()`), let `S, X ∈ Ob(St)` be
shapes, and let `step: ([a, S], [b, X]) → [a, S]` be the **step morphism** —
a Br morphism taking a state of type `[a, S]` and a per-step input of type
`[b, X]` and producing an updated state of the same type. Let `N ≥ 1` be the
step count and `L` the **recurrence axis** with `|L| = N`; let `L'` be a
fresh axis with `|L'| = N+1`. The input sequence stacks the `N` per-step
inputs along `L`, giving type `[b, X⊗L]`. In the running example,
`a = b = ℝ`, `S = X = (i,)`, and `step` is the update
`H[i] ↦ H[i] + lr · Grad[i]`.

`Scan(step, N)` has:

- domain `([a, S], [b, X⊗L])` — initial state and full input sequence
- codomain `[a, S⊗L']` — full state history over `N+1` positions

Both are valid Br objects — products of typed arrays — so `Scan` is a
well-typed morphism.

The core product-category axioms hold:

**Identity and associativity.** `Scan` is a construction rule with definite
`dom()` and `cod()`. It composes with other Br morphisms before and after,
and sequential composition is associative because the semantics are a pure
function. ✓

**Bifunctoriality** `(f;g) ⊗ (h;k) = (f⊗h);(g⊗k)`. `Scan` operates on a
disjoint wire bundle from `h`, so the monoidal product interleaves with
composition correctly. ✓

**Elemental property.** Elements of `Scan`'s domain and codomain are tuples
of array values; the element-determination property is unaffected. ✓

`Scan` therefore fits the ProdCategory grammar as a new construction rule:

```python
type ProdCategory[L, M: Morphism] = (
    M
    | Rearrangement[L]
    | Composed[L, ProdCategory[L, M]]
    | ProductOfMorphisms[L, ProdCategory[L, M]]
    | Block[L, ProdCategory[L, M]]
    | Scan[L, ProdCategory[L, M]]   # new
)
```

### A.2 The structural property `Scan` fails — the batch lift independence axiom

Br carries a key structural axiom for the batch lift (theory.md Eq. 3):

$$[f, P] \mathbin{;} [Y, q] = [X, q] \mathbin{;} f \qquad \forall\, q : \mathbf{1} \to P$$

This says slicing the output at position `q` after applying `f` equals slicing
the input at `q` first, then applying `f`. It guarantees position-independence:
every `q ∈ P` is computed from only its own input slice.

`Scan` cannot satisfy this for L because of the sequential dependency. A
`Broadcasted` morphism with degree L would require (Def. 11, Eq. 2) that the
output at each position l depends only on the l-th input slices — the
morphism factors into `|El(L)|` independent copies of the step body, with no
data flow between positions. But `H_l` depends on `H_0, …, H_{l-1}`: the
output at position l is a function of ALL preceding positions, not just the
l-th input slice. `Scan` is therefore not expressible as a `Broadcasted` root
morphism with L as part of the degree.

For any **fixed** N, `Scan(step, N)` can be unrolled into a `Composed` of N
distinct `Broadcasted` morphisms — one per step, each using a different fixed
reindexing into the Grad sequence. What cannot be expressed within the
existing grammar is `Scan` for variable N: no single construction rule
produces a morphism parameterised by N without unrolling.

Batch lifting over axes **orthogonal** to L is well-defined: `[Scan(step,N), P]`
for a batch axis P independent of L runs the scan independently for each `p ∈ P`,
and each such run satisfies the independence axiom over P. The sequential
dependency is within each trajectory over L, not between batch positions
(see §A.4 for the weave/reindexing treatment).

### A.3 Why `Block` does not already cover `Scan`

`Block` is a degenerate fold — `foldl f z (repeat () N)` where the step
ignores its second argument, giving `dom(step) = cod(step) = State`. This is
why theory.md describes `Block` as "transparent to the categorical semantics":
it passes `dom()` and `cod()` through from the body unchanged.

`Scan` changes the type. `dom(step) = ([a, S], [b, X])` and `cod(step) = [a, S]`,
whereas `dom(Scan(step, N)) = ([a, S], [b, X⊗L])` and
`cod(Scan(step, N)) = [a, S⊗L']`. The input sequence `[b, X⊗L]` and the
output history `[a, S⊗L']` have no counterpart in `step`'s signature. This
type change is the formal signal that `Scan` is a new combinator, not a
special case of `Block`.

One might try to express `Scan` as `Composed([step_0, step_1, …, step_{N-1}])`
— one copy of `step` per time step, each with a different fixed Grad slice
baked in via a `StrideMorphism` reindexing. This works for fixed N and gives
O(N) morphisms, but it loses the structural invariant that all steps are the
same operation. `Scan(step, N)` is the compact, structurally-aware form.

### A.4 Interaction with weaves and reindexings

The weave/reindexing apparatus is designed for static, uniform, parallel
broadcasting: a tiling axis is one where every degree position `p ∈ P` receives
its own independent input slice via a fixed affine reindexing `η: P → Q`,
with no data flow between positions. The recurrence axis L fits neither
requirement.

**Within the step body.** `step` is an ordinary Br morphism with its own
weaves and reindexings. The state axes S and per-step input axes X are target
axes for the step body; any additional axes the step body broadcasts over are
tiling axes with the usual static reindexings. Nothing here is special to
`Scan`.

**The recurrence axis L.** L cannot appear in any weave or reindexing of
`Scan` itself, for two reasons:

- *Input side.* At step `l`, `Scan` reads `[b, X⊗L]` via the element
  morphism `⟨l|: 1 → L`. This is a dynamic reindexing — `l` advances each
  iteration. A `Broadcasted` reindexing must be a fixed affine map determined
  at morphism-construction time; it cannot depend on the running step index.

- *Output side.* The output history axis L' is created by the sequential
  iteration — states are accumulated one at a time. A tiling axis in a
  `Broadcasted` morphism is pre-existing in both input and output weaves and
  drives which slice is written where. L' has no counterpart in `step`'s
  signature and so cannot be described by a weave at all.

L therefore sits outside the weave/reindexing framework and is managed by
`Scan`'s sequential iteration logic.

**Batch lifting over orthogonal axes P.** For a batch axis P independent of
L, `[Scan(step, N), P]` applies the scan independently for each `p ∈ P`.
The step body becomes `[step, P]`, and the standard machinery applies: each
input weave gains TILED entries for the P axes, and each reindexing extends
from `η_i: P_step → Q_i` to `id_P ⊗ η_i: P⊗P_step → P⊗Q_i`. The
independence axiom holds over P — different batch positions have no data flow
between them.

| Axis | Role in weave | Reindexing |
| --- | --- | --- |
| State axes S | Target in step body | — |
| Per-step input axes X | Target in step body | — |
| Recurrence axis L | Not a weave axis — sequential dependency | Not a reindexing — dynamic element access |
| Output history axis L' | Not a weave axis — created by iteration | — |
| Orthogonal batch axis P | TILED in lifted step body | `id_P ⊗ η_i` |

### A.5 Summary

| Property | Holds for `Scan`? |
| --- | --- |
| Well-typed domain and codomain in Br | ✓ |
| Identity and associativity axioms | ✓ |
| Bifunctoriality with `ProductOfMorphisms` | ✓ |
| Elemental determination property | ✓ |
| Batch lift independence over recurrence axis L | ✗ |
| Expressible as `Broadcasted` root morphism | ✗ |
| Expressible via `Composed` for fixed N | ✓ (O(N) unrolling) |
| Expressible via single construction rule for variable N | ✗ |
| Batch lift well-defined over orthogonal axes P | ✓ |
| Recurrence axis L expressible as tiling axis | ✗ |
| Recurrence axis L accessible via static reindexing | ✗ |
| Step body weaves and reindexings unaffected | ✓ |
| Orthogonal batch axes extend via standard weave/reindexing | ✓ |

`Scan` satisfies the core categorical axioms and can be added to the
ProdCategory grammar as a valid construction rule. It cannot be expressed as
a `Broadcasted` root morphism for two independent reasons: on the input side,
the element access `⟨l| : 1 → L` is dynamic and cannot be expressed as a
fixed affine reindexing; on the output side, the state history `[a, S⊗L']`
is accumulated sequentially, so output at position l depends on all preceding
positions, violating the independence property (Def. 11). For any fixed N it
can be unrolled into a `Composed` of N operations, but this loses the uniform
N-parameterised structure and cannot serve as a general recurrence primitive.
`Scan` must therefore be a new construction rule rather than derived from
existing Br operations.
