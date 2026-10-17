# P2b observed values (additive collection, slice 1)

Every value below is from a real run on branch `proto-additive-slice1-p2b`. Probes were scratch files
run with `lake +leanprover/lean4:v4.30.0 -d <worktree>/leanncd env lean <file>` after a current
`lake-build.sh … LeanNCD` (the harness pattern `chk.lean`; `lake env lean` from the worktree root picks
the wrong toolchain and reports `incompatible header`). Probe printer: `TLProgram.compile` run at fresh
state 0, printing `tc.steps.map (·.op)`, `tc.routing`, `tc.nExternal`.

## T3 probe, BEFORE the route change (tip `72fde8c8`)

Programs (axis `i : ℕ = 2`): P1 = `T:=A; U:=T; T:=B`; P2 = `T:=A; T:=B; U:=T`.

- `compileToScheduled` reorders P1 to the same schedule as P2: writes `[[T],[T],[U]]`, reads
  `[[A],[B],[T]]` (P1's inference "reordered by `schedule` to `[T,T,U]`" CONFIRMED).
- `route`, both P1 and P2, both default-f32 (as written) and `explicitF64`: `ROUTE OK steps=3
  ops=[contract, contract, contract] routing=[[external 0], [external 1], [internal 1 0]] nExt=2`.
  The reader `U` is wired to step 1 (`T := B`) only; step 0 (`T := A`) is a dead step whose output no
  wire reads. P1's inference "silent last-wins through `buildNameToStep`" CONFIRMED by observation, for
  both source orders and both storage kinds.

## T3 probe, AFTER the route change

- P1 and P2, default-f32 and `explicitF64`: `ROUTE OK steps=4 ops=[contract ×4] routing=[[external 0],
  [external 1], [internal 0 0, internal 1 0], [internal 2 0]] nExt=2` (private writers `T#1`,`T#2`;
  collector reads both; `U` reads the collector).
- P4 neighbour `T:=A; U:=T; S:=B`: schedule writes `[[T],[U],[S]]`; `steps=3 ops=[contract ×3]
  routing=[[external 0], [internal 0 0], [external 1]]` (unchanged by collection).
- P5 `T:=relu(A); T:=B; U:=T`: `steps=5 ops=[contract, relu, contract, contract, contract]
  routing=[[external 0], [internal 0 0], [external 1], [internal 1 0, internal 2 0], [internal 3 0]]`.
- P6 `T:=A; T:=B; T:=C; U:=relu(T)`: `steps=6 ops=[contract ×5, relu] routing=[[external 0],
  [external 1], [external 2], [internal 0 0, internal 1 0, internal 2 0], [internal 3 0],
  [internal 4 0]] nExt=3`.
- Probe side-finding: a `tensor f64 T(i)` declaration does not parse inside `tlprog!` (`unexpected token
  'T('; expected '(' or tl_named_shape`); the same line with `Y` parses (C4b). The fixtures use `Y`.

## T3 first attempt: `route` calling `collectDefinitions` (rejected)

With `route` calling `collectDefinitions` (the wrapper that adds the `isTopoOrdered` assertion),
`DSL.Pipeline.RouteFragmentDiagnosticTest` failed three guards: `#guard routeErrorIs (selfRef
.identity) cyclicRouteMsg 7 7`, `#guard routeErrorIs (selfRef (.pointwise .relu)) cyclicRouteMsg 7 7`,
`#guard routeErrorIs preScheduledCycle cyclicRouteMsg 7 7` (each `Expression … did not evaluate to
true`): the wrapper's assertion fires first, so the payload moves from `cyclicDataflow "routeCore:
cyclic dataflow (topoSort fallback)"` to the wrapper's message. Final code calls `desugarMultiWriters`;
all three pass again.

## T3 fixtures (`test/DSL/Pipeline/CollectTest.lean`, section "Route integration")

| Fixture | Program (axis i = 2) | Expected `(ops, routing)` | Donor |
|---|---|---|---|
| RT1 pin | `Y:=A; U:=Y; Y:=B` (default f32) | `collectedRoute` = 4×contract, `[[e0],[e1],[i0 0,i1 0],[i2 0]]` | C1 + reader; P1 probe |
| RT2 pin | `Y:=A; Y:=B; U:=Y` | `collectedRoute` | clone RT1 |
| RT3 pin | RT1 with `tensor f64 Y(i)` | `collectedRoute` | clone RT1 + C4b decl |
| RT4 accept-neighbour | `Y:=A; U:=Y; S:=B` | 3×contract, `[[e0],[i0 0],[e1]]` | clone RT1, rename |
| RT5 pin | `Y:=relu(A); Y:=B; U:=Y` | `[contract, relu, contract, contract, contract]`, `[[e0],[i0 0],[e1],[i1 0,i2 0],[i3 0]]` | clone RT2 |
| RT6 pin | `Y:=A; Y:=B; Y:=C; U:=relu(Y)` | `[contract×5, relu]`, `[[e0],[e1],[e2],[i0 0,i1 0,i2 0],[i3 0],[i4 0]]` | clone RT2 |

Acset (`test/Bridge/AcsetCodecTest.lean`): fixture 10, round trip of RT5's program (clone of fixture
8), plus a guard that its `steps.length = 5`.

### Mutation M1 (route skips collection: `match physicalizeForRoute logical with`), restored

Build of `DSL.Pipeline.CollectTest Bridge.AcsetCodecTest`:
- `test/DSL/Pipeline/CollectTest.lean` RT1: `Expression\n  routed rt1 == some collectedRoute\ndid not
  evaluate to \`true\``; RT2, RT3 the same text with `rt2`/`rt3`; RT5 and RT6 `Expression\n  routed rt5
  ==\n    some\n      ([BrOp.contract, BrOp.relu, …` (resp. `rt6`) `did not evaluate to \`true\``.
- RT4 (accept-neighbour) PASSED under the mutation, as intended.
- `test/Bridge/AcsetCodecTest.lean`: the `steps.length = 5` guard failed (`Expression\n  decide\n
  ({\n steps := …`). The round-trip guard itself still passed: it is a codec witness (it holds for any
  routed `tc`), not a pin of the route change.
- Restored; both modules green again.

## T4 fixtures (oracle profile lift)

Values were checked by building `Semantics.SourceDifferentialPolicyTest`,
`Semantics.SourceDiagnosticAdmissionTest` and `Semantics.SourceDifferentialGeometryTest`, which were green
on the final tree. The bit patterns are binary64 values of the expected integers, and they are confirmed
by those guards passing: 7 = `0x401C000000000000`, 13 = `0x402A000000000000`,
12 = `0x4028000000000000`, 22 = `0x4036000000000000`, 6 = `0x4018000000000000`.

| Fixture | Program | Now asserts | Donor |
|---|---|---|---|
| F14 (flipped) | `multiDefinition`: `Y:=A; Y:=B`, f64, A=[5,9], B=[2,4] | `valueCompared`: `fourLegParity`, profile ok with `definitions = [(3,out 0),(3,out 1)]`, native `shared` the same, legacy+checked `.compared (.ok .agreement)`; legacy/checked bits = [7,13] | was `overwriteRefusal` |
| F15 (flipped) | `duplicateDefinition`: `Y:=A; Y:=B; Y:=A` | `valueCompared` with 3 origins; `checkStructure` of the reversed permutation is `.ok` with `definitions = [(3,out 2),(3,out 1),(3,out 0)]`; bits = [12,22] | same |
| F14f32 (new, f32 neighbour) | F14 with undeclared-typed `.tensor` decls (default f32) | `knownContractDifference (usedDType (out 0) "Y" .f32)`, profile `.error (.structural …)` with the same condition, oracle Y = [7,13] | clone F14 + F13's `defaultF32` |
| D10 `acceptedNonshared` (flipped) | scalar `Y:=A; Y:=A`, A=3 | `fourLegParity`, profile `definitions` lists both statements, oracle Y=6, legacy/checked bits `0x4018000000000000` (6) | was a `crossStatementOverwrite` refusal |

Accept-neighbours already present: F13 `f64Neighbor` and D12 `explicitF64Neighbor` (single definition,
`fourLegParity`, bits 3). Also checked: F14f32 is the f32 neighbour of F14.

Note: my first D10 edit used a global string replace that also changed D12 `explicitF64Neighbor`'s
expected bits (3 → 6). D12 then failed with `SourceDiagnosticAdmissionTest.lean:306:0 Expression D12 did
not evaluate to true`. I restored that guard to 3. This shows that a single-definition program still
evaluates to 3, not 6 (it is not doubled).

### Mutation M2 (adds back a second-definition refusal in `checkStructure` through `usedDType`; restored)

- `SourceDifferentialPolicyTest.lean:329:0: Expression\n  F14\ndid not evaluate to \`true\``
- `SourceDifferentialPolicyTest.lean:331:0: Expression\n  F15\ndid not evaluate to \`true\``
- `SourceDiagnosticAdmissionTest.lean:175:0: Expression\n  D10\ndid not evaluate to \`true\``
- F13, F14f32, D11 and D12 PASSED under M2, which is what the neighbours and the f32 twin should do.

### Mutation M3 (removes the OUTPUT dtype check in `checkStructure`; restored)

- `SourceDifferentialPolicyTest.lean:328:0: Expression\n  F13\ndid not evaluate to \`true\``
- `SourceDifferentialPolicyTest.lean:330:0: Expression\n  F14f32\ndid not evaluate to \`true\``
- F14 and F15 passed: they are f64 programs and do not depend on this check.

## Mutation-cycle count

3 cycles: M1 (route), M2 (oracle refusal), M3 (oracle dtype order). All were restored, and the
restored tree was rebuilt green.
