# P1 observed values (additive collection, slice 1)

All values come from real runs on branch `proto-additive-slice1-p1` (2026-10-14): either a passing
`#guard` in the shipped test files, or the scratch probe `p1probe.lean` (`lake env lean`, after the
LeanNCD build). Mutation strings are the exact first line(s) Lean printed; every mutant was restored
and the final tree rebuilt green (`LeanNCD`, `Eval.CollectEvalTest`, `DSL.Pipeline.CollectTest`,
`Eval.Plan.ContractTest`, `DSL.Pipeline.RouteFragmentCorpusTest`).

Test files: `leanncd/test/DSL/Pipeline/CollectTest.lean` (structure, readiness),
`leanncd/test/Eval/CollectEvalTest.lean` (values, rejections). Programs below are `tlprog!` bodies;
evaluator runs use `.explicitF64` (every undeclared name declared `tensor f64`).

## Structural fixtures (`CollectTest.lean`, `desugarMultiWriters` on `compileToScheduled`)

| Id | Program | Observed | Donor | Accept-neighbour |
|---|---|---|---|---|
| C1 | `Y[i]:=A[i]; Y[i]:=B[i]` | dests `[Y#1, Y#2, Y]`; reads Y#1←A, Y#2←B, Y←[Y#1,Y#2]; generated `[Y#1,Y#2]` | F14 `multiDefinition` | C3 |
| C2 | C1 + `Y[i]:=C[i]; Z[i]:=Y[i]` | dests `[Y#1,Y#2,Y#3,Y,Z]`, all distinct | clone C1 | — |
| C3 | `Y[i]:=A[i]; Z[i]:=Y[i]` | generated `[]`, stmts and decls equal to input | — | (identity) |
| C4 | `predicate Y(i)` + C1 | decls named Y*: `[Y, Y#1, Y#2]`, all `.predicate` | clone C1 | — |
| C4b | `tensor f64 Y(i)` + C1 | element types `[f64, f64, f64]` | clone C4 | — |
| C5 | `S[2*i]:=X[i]; S[2*i + 1]:=Y[i]` | `multiWriterScatter "S"` | note probe | C1 |
| C6 | `Y[i]:=maxreduce(A[i,j]); Y[i]:=maxreduce(B[i,j])` | `multiWriterAlgebra "Y"` | clone C1 | C1 |
| C7 | `Y[i]:=A[i]; Y[j]:=B[j]` (`axis i,j : ℕ = 2`) | `writerShapeMismatch "Y" 2 0` | clone C1 | C1 |
| C8 | hand-built `[Y#1:=A, Y:=B, Y:=C]` | `reservedNameCollision "Y#1"` | — | C8b: rename to `Q` → generated `[Y#1,Y#2]` |

## Readiness fixtures (`CollectTest.lean`)

| Id | Program | Observed | Accept-neighbour |
|---|---|---|---|
| R1 | `T[i]:=A[i]; U[i]:=T[i]; T[i]:=B[i]` (surface) | `schedule` order `[T, T, U]` | — |
| R2 | same order, hand-built direct schedule | `isTopoOrdered = false` | R2b `[T,T,U]` → `true` |
| R3 | `T[i]:=A[i]; T[i]:=T[i]·B[i]` | `cyclicDataflow "schedule: cyclic dataflow"` | R3b `U[i]:=T[i]·B[i]` → `[T, U]` |
| R4 | RC10 + column face `G[0,c]:=Q[c]` (2-D scan), plain reader appended by hand | scan `outputs = [G, G]`; `isTopoOrdered = true` | — (surface absorbs a plain reader into the scan: probe `p1scan.lean` printed `[scan G outputs=[G, G]]` with `T[j]:=G[j,1]` gone) |

## Value fixtures (`CollectEvalTest.lean`, `TLProgram.eval ∘ explicitF64`, bit-exact)

| Id | Program | Inputs | Observed | Donor |
|---|---|---|---|---|
| V1 | `Y:=A; Y:=B` | A=[5,9], B=[2,4] | Y=[7,13]; env keys `[A,B,Y]` (no `Y#k`) | F14 (spec [7,13]) |
| V2 | `Y:=A; Y:=B; Y:=A` | same | Y=[12,22] | F15 (spec [12,22]) |
| V3 | `Y:=X; Y:=X` | X=[1.5,2.5] | Y=[3,5] (spec §9.1 2X) | clone V1 |
| V4 | `predicate R(i); R:=A; R:=B` | A=[1,0], B=[1,1] | R=[1,1] (count would be [2,1]) | clone V1 |
| V4' | same | A=[1,0], B=[0,1] | R=[1,1] (old overwrite [0,1]) | note probe |
| V5 | `Y:=A; Y:=B; Y:=C` (`i = 1`) | 0.1, 0.2, 0.3 | bits 4603579539098121012 (0x3FE3333333333334) | — |
| V5r | `Y:=C; Y:=B; Y:=A` | same | bits 4603579539098121011 (0x3FE3333333333333) | reversed V5 |
| V6 | `T:=A; U:=T; T:=B` | A=[1,2], B=[10,20] | T=U=[11,22] (old: U=[1,2]) | note probe |
| V7 | `Y:=relu(A); Y:=relu(B)` | A=[-1,2], B=[3,-4] | Y=[3,2] (relu(A+B) would be [2,0]) | clone V1 |
| V8 | `Y:=A` (single writer) | A=[5,9], B=[2,4] | Y=[5,9]; keys `[A,B,Y]` | accept-neighbour of V1 |
| J1 | `T:=A; T:=T·B` | — | `compile failed: LeanNCD.CompileError.cyclicDataflow "schedule: cyclic dataflow"` | R3 |
| J2 | `Y[i]:=A[i]; Y[j]:=B[j]` (i=2, j=3) | A len 2, B len 3 | `compile failed: LeanNCD.CompileError.writerShapeMismatch "Y" 2 0` (old: silent truncation) | C7 |
| J3 | C5 | X=[1,2], Y=[10,20] | `compile failed: LeanNCD.CompileError.multiWriterScatter "S"` (old: [0,10,0,20]) | C5 |
| J4 | C6 | 2×2 A, B | `compile failed: LeanNCD.CompileError.multiWriterAlgebra "Y"` | C6 |
| J5 | V8 with input `Y` supplied | A=[1,2], Y=[7,7] | `evalScheduled: supplied input Y names a tensor the program defines` | B3 |
| J5b | V8 with extra input `Unused` | Unused=[7] | Unused returned unchanged = [7] | ContractTest `extraInputProg` |

Migrated existing fixtures (old behaviour asserted, flipped by P1):
- `test/Eval/Plan/ContractTest.lean` `repeatAssignProg` (`Y:=A; Y:=B; Z:=Y`, reference evaluator): baseline
  Y=Z=[101,202] (A=[1,2], B=[100,200]); first-write mutation A[0]=999 → Y=[1099,202]. Passing.
- `test/DSL/Pipeline/RouteFragmentCorpusTest.lean` G21 (8 `%nl0` collision cases): the OLD regression leg
  now fails at `schedule` with `cyclicDataflow "schedule: cyclic dataflow"` (minted `%nl0` is a second
  writer that reads `%nl0`) instead of `routeCore: cyclic dataflow (topoSort fallback)`. Observed failure
  before migration: `G21 collision transition (8 cases): 8 FAILURES, ids [97, ..., 104]`.
- `test/Eval/Plan/CompileTest.lean` ordered-twin direct run: the reference now refuses the supplied `Z`
  (observed `ordered topology direct evaluation failed: evalScheduled: supplied input Z names a tensor the
  program defines`); the direct call now passes `topologyInputs.erase "Z"`.

Probe-only observations (not shipped as fixtures):
- f32 (default dtype): `tensor f32 Y(i)` + two writers, and the undeclared (f32-default) V1 program, both
  give `unsupported dtype: tensor A is declared f32, ...` in the reference — the first f32 used name is the
  external `A`, never a private `Y#k`.

## Mutation controls

| Mutation (file, change) | Fixture(s) that failed | Exact observed failure |
|---|---|---|
| Collect: reversed writer numbering `k := length - idxOf i` | C1, C2 (T1); V5, V5r (T3) | `CollectTest.lean:57:0: Expression … did not evaluate to true` (also :58, :59, :72); `CollectEvalTest.lean:96:0: Expression bitsOf v5 v5In "Y" == some [4603579539098121012]` and :97 |
| Collect: no declaration clones (`decls := sched.decls`) | C4, C4b (T1); every multi-writer value fixture (T3) | `CollectTest.lean:95:0: Expression match desugared c4 with …` and :109; `CollectEvalTest.lean` :48 :50 :59 :67 :77 :79 :96 :97 :107 :108 :117 (undeclared `Y#k` default to f32, so evaluation fails before any predicate counting can show) |
| Collect: collector `agg := .max` | V1, V2, V3 … | `CollectEvalTest.lean:48:0: Expression bitsOf v1 v1In "Y" == some (bits [7, 13])` (also :59, :67) |
| Collect: last-wins regression (`if true then return (sched, [])`) | V1, V2, V3 … | `CollectEvalTest.lean:48:0: Expression bitsOf v1 v1In "Y" == some (bits [7, 13])` (also :59, :67) |
| Eval: hiding removed (`env := env`) | V1 keys | `CollectEvalTest.lean:50:0: Expression keysOf v1 v1In == some ["A", "B", "Y"]` |
| ScheduledValidation: any-writer readiness restored | R1, R2, R3 | `CollectTest.lean:176:0: Expression scheduledDests r1 == some ["T", "T", "U"]`; `:181:0: Expression !isTopoOrdered r2Stmts r2Stmts`; `:194:0: Expression match EStateM.run r3.compileToScheduled 0 with` |
| ScheduledValidation: `publications := sc.outputs` (no eraseDups) | R4 | `CollectTest.lean:215:0: Expression match scheduled r4 with` |

Cycle count: 9 mutation cycles (T1: 2; T2: 2; T3: 5, two of which re-ran T1 mutations at evaluator level),
each restored and rebuilt.
