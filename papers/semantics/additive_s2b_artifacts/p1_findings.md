# S2b prototype P1: carrier abstraction for the Source oracle (findings)

Branch `proto-s2b-p1` (scratch, off `worktree-additive-s2b-tropical-carriers` at 5e9bfdf0). Prototype
files: `leanncd/LeanNCD/Semantics/Source/Carrier.lean` (new), `Oracle.lean` (generic), test
`leanncd/test/Semantics/SourceOracleCarrierTest.lean` (new, added to the `Tests` globs). Probe:
`leanncd/spikes/S2bCarrierProbe.lean` (gitignored, not committed).

## Q1. Max-plus carrier

Observed (`lean-file.sh` on the probe, this Mathlib):

| Probe | Result |
|---|---|
| `#synth CommSemiring (Tropical (WithTop ℚ))` (min-plus) | succeeds (`Tropical.instCommSemiring`) |
| `#synth DecidableEq (Tropical (WithTop ℚ))` | succeeds |
| `#synth Repr (Tropical (WithTop ℚ))` | FAILS: no `Repr` for `Tropical` (need our own) |
| `#synth CommSemiring (Tropical (WithTop ℚᵒᵈ))` | fails (as in design note §3) |
| `#synth CommSemiring (Tropical (WithBot ℚ)ᵒᵈ)` | fails out of the box |

Why it fails: Mathlib's `CommSemiring (Tropical R)` needs `LinearOrderedAddCommMonoidWithTop R`. For
`R = (WithBot ℚ)ᵒᵈ` every parent is already synthesized (`AddCommMonoid`, `LinearOrder`,
`OrderTop`, and `IsOrderedAddMonoid` once `Mathlib.Algebra.Order.Monoid.OrderDual` is imported);
only the class's own two fields are missing: `top_add'` and `isAddLeftRegular_of_ne_top`.

Options:

- **(b') chosen: `Tropical (WithBot ℚ)ᵒᵈ` plus one 6-line instance** supplying the two fields from
  `WithBot.bot_add` and `WithBot.add_left_cancel`. After it, `CommSemiring` synthesizes; the semiring
  laws are Mathlib's. `+` is `max`, `*` is `+`, `0` is `-∞` (`⊥`), `1` is `0`. Observed `#eval`:
  `2 ⊕ 5 = 5`, `2 ⊗ 5 = 7`, `0 = -inf`, `1 = 0`.
- (c) max-plus as min-plus transported along negation (`def MaxPlusNeg := Tropical (WithTop ℚ)`,
  semiring by `inferInstanceAs`, 0 proof lines). Rejected: every stored value is the negation of the
  meaning, so `ofRat`, display, the Core-leg input store, observation and differential comparison
  all need a sign flip, and a missed one is a silent wrong answer. Proof saving is only 6 lines.
- (a) own `WithBot ℚ` type with hand-proved laws: not built. Cost evidence from the toy Boolean
  carrier (below): a hand-proved `CommSemiring` on a 2-element type is 21 lines of case splits; on
  `WithBot ℚ` distributivity of `+` over `max` needs real case analysis, estimated 60-100 lines. No
  advantage over (b').

Recommendation: (b'). Total max-plus carrier cost in `Carrier.lean`: 6 lines instance + 1 `def` +
2 instance lines (`CommSemiring`, `DecidableEq` via `inferInstanceAs`) + 4 lines `Repr` + 2 lines
carrier record = 15 lines. Min-plus: 9 lines (no proof). Both are nominal `def`s (`MinPlus`,
`MaxPlus`) so the `Repr` instances are ours, not orphans on Mathlib's `Tropical`.

Gotcha: `decide` on `MaxPlus.ofRat 2 * MaxPlus.ofRat 5 = MaxPlus.ofRat 7` gets stuck in the kernel
(`Rat.add` does not reduce); `#guard` (compiled evaluation) works. Fixtures must use `#guard`.

## Q2. Carrier interface

```lean
structure Carrier (K : Type) where
  agg : AggOp        -- the source aggregation this carrier interprets (admission/selection key)
  ofRat : ℚ → K      -- embedding of a finite rational input value
```

with `[Semiring K]` supplied separately; the oracle takes `zero/one/add/mul` from the semiring, NOT
from record fields. Reason: `AdmittedSource.program` (Core leg) already takes `[Semiring K]` and
lowers through `semiringOps` (`⟨0, 1, (· + ·), (· * ·)⟩`); taking the oracle's arithmetic from the
same instance makes "oracle and Core use the same algebra" true by construction, where record
fields could drift from the instance. `DecidableEq K`/`Repr K` are needed only by the derived
instances of the result structures.

The oracle structures (`Tensor`, `ReadValue`, `Occurrence`, `TermFiber`, `Contribution`, `Result`)
gained a type parameter with a DEFAULT, `(K : Type := ℚ)`. Observed: Lean accepts default structure
parameters, `Oracle.Tensor` still means `Oracle.Tensor ℚ`, and every downstream mention compiles
unchanged. `Oracle.run` is `runWith Carrier.real`. Net diff to `Oracle.lean`: +47/-38 lines, all
type annotations plus `values.map C.ofRat` at the input store and the new `run` wrapper.

Proposed later addition (not built, needed by S2b's differential): `observe : K → ExtValue` where
`ExtValue` is one shared extended-rational observation type (`finite ℚ | posInf | negInf`), so that
Observation/Differential/Diagnostics change their value type ONCE, not once per carrier.

Per-file table (counts from `rg -c` on this branch; "RR" = `RationalReference`, "ES" =
`elaborateSource`/`LoweredSource`):

| File | ℚ | RR | ES | Must change for S2b? | Why |
|---|---|---|---|---|---|
| Oracle.lean | 9 -> generic | 0 | 0 | done here | evaluation loops, value fields |
| Program.lean | 0 | 2 | 2 | yes, small | `LoweredSource`/`elaborateSource` fixed at `RationalReference`; need `elaborateSourceAt K` with an empty registry (unary ops stay refused); `AdmittedSource.program` itself is already generic |
| Schedule.lean | 0 | 15 | 38 | yes | `sourceInputBinding` is typed `InputBinding (K := RationalReference.Carrier)` and binds ℚ buffers; `runSource` runs at `RationalReference.ops`; needs `K`, the carrier's `ofRat`, and `semiringOps` |
| Observation.lean | 8 | 4 | 14 | yes | event/tensor/accumulator observations carry `ℚ` from the Core run at `elaborateSource`; parity (Core vs oracle) for tropical needs these at `K` or at `ExtValue` |
| ProgramCorrespondence.lean | 0 | 5 | 11 | yes, if proofs extend to tropical | theorems stated at `RationalReference.ops/registry`; the generic `K` part already exists in Program.lean |
| RawSemanticConnection.lean | 0 | 4 | 9 | no for S2b executable work; yes for a tropical semantic-connection theorem | same as above |
| Permutation.lean | 0 | 3 | 8 | can stay | permutation invariance stated at ℚ; tropical version optional |
| NumericalProfile.lean | 16 | 0 | 0 | yes, real-only logic must be split | re-evaluates products/sums with a bounded-integer envelope (`limit = 2^20`) and `expectedBits` for finite integers; tropical needs ∓∞ bit patterns and a sum-of-bounded-integers bound (products become sums) |
| Differential.lean | 1 | 0 | 0 | yes | `found : List ℚ` accumulator payload and production-vs-oracle comparison need ∓∞ |
| Diagnostics.lean | 2 | 0 | 0 | yes | `Option ℚ` cell payloads need ∓∞ |
| Adapter.lean | 3 | 1 | 0 | no | input buffers stay finite ℚ by decision (inputs are finite rationals); `ofRat` embeds them |
| Admission.lean | 0 | 0 | 0 | yes | refuses `agg != .sum` (`admitStatement`, lines 662/882; `StatementFields` pins `rhs.agg = .sum`, line 686); needs agg recorded per statement plus the single-sort rule (`mixedSorts`) |

## Q3. Vertical cut and observed outputs

Built: `Carrier.lean` (record + real/min-plus/max-plus instances), `Oracle.lean` generic
(`runWith`), `run` unchanged in behaviour. Program.lean untouched (not needed for the oracle cut).

Test `SourceOracleCarrierTest.lean` (agg = sum source programs, evaluated under each carrier; inputs
`X = [1,2,3,4]`, `W = [1,10,100]`):

| Program | Carrier | Observed `Y` (all `#guard`ed against hand values) |
|---|---|---|
| `Y[a] := X[a] * W[b]` | real | `[111, 222, 333, 444]` |
| `Y[2*a] := X[a]`, `\|k\| = 7` | real | `[1, 0, 2, 0, 3, 0, 4]` |
| `Y[a] := X[a] * W[b]` | max-plus | `some [101, 102, 103, 104]` (X + max W) |
| `Y[2*a] := X[a]` | max-plus | `some [1, -inf, 2, -inf, 3, -inf, 4]` (empty fibers give `-inf`) |
| `Y[a] := X[a] * W[b]` | min-plus | `[2, 3, 4, 5]` (X + min W) |
| `Y[2*a] := X[a]` | min-plus | `some [1, +inf, 2, +inf, 3, +inf, 4]` (empty fibers give `+inf`) |
| both | `OrAnd` (toy) | all `true`; strided `[t, f, t, f, t, f, t]` |

The three `some [...]` rows are `#guard_msgs` captures of `#eval` output (the `Repr` instances print
`±inf`). Real-instance regression: every existing test module, including `SourceOracleTest`,
`SourceOracleAffineTest`, `SourceProgram*Test`, `SourceDifferential*Test`, and
`SourceDiagnostic*Test`, built unchanged against the generic oracle (full default build; the only
failure on the first run was the toy `OrAnd` instance in the new test, since fixed). No existing
fixture or expected value was edited.

## Extensibility check (fourth carrier)

Added in the TEST FILE only: Boolean (or, and) semiring `OrAnd` (a fresh structure, since Mathlib's
`Bool` ring is XOR). Cost: 3 lines type, 4 lines `Zero/One/Add/Mul` instances, 17 lines
hand-proved `CommSemiring` (`nsmulRec` with `rfl` laws, the rest `rintro <;> rfl` case splits), 1 line
`Carrier.orAnd := ⟨.max, fun q => ⟨q != 0⟩⟩`. Pitfall hit: `nsmulRec` needs `Zero`/`Add` declared
as instances BEFORE the `CommSemiring` structure, and a hand `nsmul_succ` via `simp [HAdd.hAdd]`
hits max recursion. Zero edits to
`Oracle.lean` or `Carrier.lean`. Observed: contraction gives all `true`, strided empty cells give
`false`.

Finding: `agg : AggOp` is too coarse as the admission key for a fourth carrier. `AggOp` is closed
(`sum | max | min`); `OrAnd` had to reuse `.max`, which collides with max-plus. A real fourth carrier
needs the key to include the destination's DSL element type (the `elementType` that
`NumericalProfile.checkStructure` already reads), e.g. `admits : AggOp → <element type> → Bool` with
Boolean `max` → `OrAnd`, or a new `AggOp` constructor (DSL change). Recommend the predicate form in S2b so
the selection table, not the oracle, grows.

## Residual risks

1. Core leg at tropical `K` is unbuilt: `elaborateSource` and the Schedule/Observation layer are fixed
   at `RationalReference` (38 + 14 mentions). Parity (oracle vs Core executor) for tropical fixtures
   needs that generalization; it is the largest remaining item.
2. Selection is unbuilt: no code yet maps an admitted program to a carrier; admission still refuses
   non-sum. The single-sort rule and its refusal (`mixedSorts`) are S2b admission work.
3. Kernel `decide` cannot evaluate rational tropical arithmetic; proofs about concrete tropical
   fixtures need `#guard`/`native_decide`-free evaluation or `norm_num`-style lemmas.
4. `NumericalProfile` duplicates the real arithmetic (its own `product`/`total` loops); for tropical
   it must either be made carrier-generic or get a sibling. Not prototyped.
5. The empty-reduction value is the semiring `0` (∓∞) by construction (`let mut total : K := 0`);
   production must agree (max over empty = -inf). Not yet checked against production.

## Estimate of remaining S2b work

| Item | Size |
|---|---|
| Admission: record `agg` per statement, admit max/min, single-sort rule + `mixedSorts` refusal, update `StatementFields`/`admitStatement_fields` | 1 task, ~6 refusal/admission fixtures |
| Carrier selection table (`admits` predicate) | small, fold into the admission task |
| Core leg at `K`: `elaborateSourceAt`, Schedule input binding via `ofRat`, empty registry | 1 task |
| Observation/Differential/Diagnostics value type → `ExtValue` (+ `observe`) | 1 task, touches real fixtures' expected payloads (type only) |
| NumericalProfile tropical rules (∓∞ bits, sum bound) | 1 task, ~4 fixtures |
| Parity fixtures: oracle vs Core for max-plus and min-plus (contraction, empty fiber, collision, multi-statement) | ~8 fixtures |
| Differential vs production for single-factor max/min (agrees) and record the known multi-factor divergence (§6) | ~4 fixtures |
| Mutation cycles for the new admission refusals and carrier selection | ~4-6 cycles |
