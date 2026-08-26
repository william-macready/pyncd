# Archived design: scheduled nonlinearity-pair reconstruction

**Status:** Permanently superseded. Do not implement this design.

The former proposal retained `splitNonlins` before the shared scheduler:

```text
Y := f(E)
  ->
%nlN := E
Y    := f(%nlN)
  ->
ScheduledProgram
```

Eval compilation would validate each adjacent producer/consumer pair, reconstruct one logical
operation, and lower it directly to:

```text
assign E -> pointwise/axiswise f
```

The proposal also extended this reconstruction to scan base and recurrence lists, kept generated
preactivations private, published only result slots, and retained separate categorical contraction
and nonlinearity generators.

## Why it was superseded

The pair representation is a route-specific physical encoding, not a neutral semantic schedule.
Using it as shared IR requires every logical consumer to recover information that an earlier phase
deliberately erased:

- Plan compilation must recognize generated names, adjacency, coordinates, aggregation ownership,
  and single-consumer structure.
- Legacy scan evaluation must recombine the pair before seeded-axis projection; executing the split
  statements directly produced incorrect leading-axis pointwise and interleaved-axiswise histories.
- The independent oracle must understand the same generated protocol, weakening its independence.
- Generated names require namespace, collision, error-precedence, and publication rules unrelated to
  source semantics.

Subsequent route-fragment spikes demonstrated a smaller boundary: retain one logical unsplit
`ScheduledProgram`, then create private physical contraction/nonlinearity fragments immediately
before categorical routing. That design preserves the same categorical generators without exposing
their route-local connection to Eval consumers.

The canonical replacement is
[`nonlinearity_split_pair_direct_lowering.md`](nonlinearity_split_pair_direct_lowering.md).

## Retained insights

The superseded work established several requirements carried into the replacement:

- contraction and nonlinearity remain separate `BrBase` generators;
- Eval uses assignment plus pointwise/axiswise steps, never a fused assignment operator;
- preactivation slots remain private;
- scan block IR supports assign, pointwise, and axiswise nodes;
- only nonlinear results may be published or written into state;
- retained local axes require positional remapping after iteration axes are removed;
- nonlinear scatter remains out of scope pending explicit placement/reduction semantics.
