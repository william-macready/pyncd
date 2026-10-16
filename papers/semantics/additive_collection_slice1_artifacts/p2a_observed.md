# P2a observed values (additive collection, slice 1)

Branch `proto-additive-slice1-p2a` (on `proto-additive-slice1-p1`, tip `5861a282`), 2026-10-14/15. Every
expected value below is either a passing `#guard` / `run_cmd` in a shipped test file or the first line
Lean printed for a mutant. Mutation strings are the EXACT first line(s) printed (an `||` joins the
expression line to the first continuation lines of one error; a `.lean:NNN:0` position is that of the
final shipped file). Each mutant was restored (`git status` clean) before the next.

Test files: `leanncd/test/DSL/Pipeline/CollectTest.lean` (T0),
`leanncd/test/Eval/Plan/CollectPlanTest.lean` (NEW, registered in `lakefile.toml`; T1/T2 f64 + f32),
migrated `test/Eval/Plan/CompileTest.lean`, `DifferentialTest.lean`, `Adapter32Test.lean`.

Naming: "f64" fixtures go through `TLProgram.explicitF64` and are compared bit-for-bit against
`evalScheduled`; "f32" fixtures go through `prepareEvalPlan` + `ofDenseInputs32ForDecls` +
`runPreparedDense32` / `pack32` / `unpack32` (both declared `tensor f32` and UNDECLARED = default f32).
f32 bit patterns are observed from the checked plan, never narrowed from binary64.

## T0: `multiWriterScan` (CollectTest, hand-built schedules; surface syntax cannot reach them)

Donor for the scan: R4 (`iter r = 2, c = 2; G[r,0]:=Z[r]; G[0,c]:=Q[c]; G[r+1,c+1]:=G[r,c]·W[r,c]`),
whose collected schedule is one scan node writing `G`.

| Id | Schedule | Observed | Accept-neighbour |
|---|---|---|---|
| C9 | R4's scan + plain `G := A` | `multiWriterScan "G"` | C9c |
| C9b | R4's scan twice (scan + scan) | `multiWriterScan "G"` | C9c |
| C9c | R4's scan + plain `T := A` | accepted, generated `[]` | (is the neighbour) |

Reachability (`ScanStmt.writes`): `routeWrites` dedups, so one scan writing `G` in both base and
recurrence halves is ONE writer (no false rejection: C9c). A plain statement absorbed as scratch by the
surface never reaches `desugarMultiWriters` as a second writer, so C9/C9b exist only hand-built; the
`.scanPre` node counts as a scan node.

Mutations (CollectTest only; 3 cycles):

| Mutation (Collect.lean) | Failed | Exact string |
|---|---|---|
| `scanWriterConflict?` call replaced by `none` | C9, C9b | `CollectTest.lean:235:0: Expression scanErrorOf [ScanStmt.plain (copyStmt "G" "A")] == some (CompileError.multiWriterScan "G") did not evaluate to true`; `:237:0: … scanErrorOf [] true == some (CompileError.multiWriterScan "G")` |
| scan-vs-scan dropped (also require a plain writer) | C9b | `CollectTest.lean:237:0: Expression scanErrorOf [] true == some (CompileError.multiWriterScan "G") did not evaluate to true` |
| `writers.length ≥ 1` (reject single scan writers) | C9c | `CollectTest.lean:240:0: Expression scanErrorOf [ScanStmt.plain (copyStmt "T" "A")] == none did not evaluate to true`; `:241:0: Expression match Option.map …` |

Also green after T0 (targeted, no regression of scan programs): `DSL.Pipeline.RouteFragmentCorpusTest`,
`RouteWeaveTest`, `ScanAffineTest`, `Eval.ScanTest`, `Eval.CollectEvalTest`,
`Eval.Portfolio.RecurrenceTest`.

## T1: hiding (CollectPlanTest unless stated)

| Id | Program | Observed | Donor | Accept-neighbour |
|---|---|---|---|---|
| H1 f64 | `Y[i]:=A[i]; Y[i]:=B[i]` (i=2), A=[5,9], B=[2,4], `explicitF64` | plan env keys `[A,B,Y]` == reference keys; Y bits == `[7.0,13.0]` == reference; `materializedNames == #["Y"]`; `privateSlots.size == 2`; signatures `#[("Y", f64)]` | CollectEvalTest V1 | H1s `Y:=A` single writer: keys `[A,B,Y]`, Y=[5,9], `privateSlots == #[]` |
| H1 f32 declared | `tensor f32 A(i), B(i), Y(i)` + H1 | keys `[A,B,Y]`; Y bits == f32 `[7.0,13.0]`; `matNames == #["Y"]`; `privateSlots.size == 2`; signatures `#[("Y", f32)]`; `unpack32` (fed the worker's positional result) keys `[A,B,Y]` | H1 f64, change decl | H1s through `prepare32`: keys `[A,B,Y]`, `privateSlots == #[]` |
| H1 f32 undeclared | H1 without declarations (default f32) | keys `[A,B,Y]`; Y f32 `[7,13]`; `matNames == #["Y"]`; `unpack32` keys `[A,B,Y]` | H1 f32 declared, drop decl | H1s |
| H2 f64 | `Y:=A; Y:=B; Y:=W`, i=1, A=0.1, B=0.3, W=0.4 | Y bits `4605380978949069210` (== reference); reversed (`W,B,A`) `4605380978949069209` (== reference); they differ; `(0.1+0.3)+0.4` as a literal fold gives the first | CollectEvalTest V5 | reversed program is the discriminator |
| H2 f32 undeclared | same, f32 | `1061997773`; reversed `1061997774` (differ) | H2 f64 | — |
| H2 f32 declared | `tensor f32 A(i), B(i), W(i), Y(i)` + H2 | `1061997773` | H2 f32 undeclared | — |
| H3 f64 | `predicate R(i); R:=A; R:=B`, A=[1,0], B=[0,1], `explicitF64` | R bits == `[1.0,1.0]` == reference; keys `[A,B,R]`; signatures `#[("R", bool)]` | CollectEvalTest V4' | H3s `R:=A`: R=[1,0] |
| H3 f32 | same, A,B undeclared (default f32 schedule) | R f32 bits `[1.0,1.0]`; keys `[A,B,R]`; signatures `#[("R", bool)]` | H3 f64 | H3s: R=[1,0] |
| H4 f64 | `tensor f64 A(i), B(i), Y(i)` + H1 | prepares; Y=[7,13] | H1 f64 | the f64 mutation below |
| H4 f32 | H1 f32 declared | prepares | H1 f32 | the f32 mutation below |

H2 inputs `0.1, 0.3, 0.4` were found by search: they are non-integral and their two fold orders differ in
BOTH precisions. (`0.1, 0.2, 0.3`, the V5 triple, folds to the same f32 bits in both orders, so it cannot
discriminate order in f32 and is not used there.)

Migrated fixtures (new expectations all from real runs; old behaviour asserted two `Y` entries):

| File / fixture | Old | New (observed) |
|---|---|---|
| `CompileTest` `repeatPrepared` | `materializedNames == ["Y","Y","Z"]`, two distinct Y slots | `["Y","Z"]`; `privateSlots.size == 2`, distinct, disjoint from the public slots; `definedNames == #["Y#1","Y#2","Y","Z"]`; accept-neighbour `singleWriterPrepared` (drop the second writer): `["Y","Z"]`, `privateSlots == #[]` |
| `CompileTest` `repeatPredPrepared` | signatures `Y bool, Y bool, Z f64`; `tensorSigs.size == 5` | `#[("Y",bool),("Z",f64)]`; `tensorSigs.size == 6` (2 inputs + `Y#1`,`Y#2`,`Y`,`Z`) |
| `CompileTest` `repeatPredBadSlot` / `TrailingBadSlot` | `slotOutOfRange 99 5` / `7 5` | `slotOutOfRange 99 6` / `7 6` |
| `CompileTest` `repeatPredMissingPublication` | `take 1 ++ drop 2` (the middle entry) | `drop 1` (a public entry): `publicationSlots expected actual` with `expected` = the producer's visible slots |
| `CompileTest` NEW hidden-slot checks | — | (a) valid plan with `privateSlots := #[]`: `publicationSlots` with `expected.size == 4`; (b) `privateSlots` + input slot `0`: `privateSlotUnpublished 0`; (c) accept-neighbour: producer output passes `checkPreparedBindings` |
| `DifferentialTest` repeated-assignment | Y = Z = B = [100,200] | plan Y = Z = `[101.0, 202.0]` == `evalScheduled`; env size 4 on both (no `Y#k`) |
| `Adapter32Test` fixture 4 (`tensor f32`, `Y:=A; Y:=B; Z:=Y`, A=[1,2], B=[100,200]) | `["Y","Y","Z"]`, Y bits of 100/200 | `["Y","Z"]`; two hidden distinct slots; Y = Z = bits `[1120534528, 1128923136]` (101, 202); env size 4 with no `Y#1`/`Y#2`; signatures `#[("Y",f32),("Z",f32)]`. The old assertion `["Y","Y","Z"]` cannot pass under the new producer; P1 did not observe it failing (not investigated why) |

Mutations (T1; build targets `CollectPlanTest`, `CompileTest`, `Adapter32Test`, `DifferentialTest`; the
harness prints at most the first 12 errors, so each row lists a sample):

| Mutation | Failed | Exact strings (sample) |
|---|---|---|
| Compile.lean Step F: no partition (`materializedNames := materializedAcc`, `privateSlots := #[]`) | CompileTest repeat block, CollectPlanTest H1 | `CompileTest.lean:630:0: Expression Option.map (fun p => Array.map (fun x => x.name) p.bindings.materializedNames) repeatPrepared == some #["Y", "Z"] did not evaluate to true`; `:634:0 … privateSlots.size) repeatPrepared == some 2`; `CollectPlanTest.lean:100:0: Expression keysOf <$> plan64 h1 h1In == some ["A", "B", "Y"] did not evaluate to true`; `:104:0 matNames (prepared64 h1 h1In) == some #["Y"]`; `:122:0 keysOf <$> plan32 h1f32 h1In32 == …`; `:124:0` |
| Prepared.lean: `expected := published` (privateSlots ignored) | every run through the checker | `CompileTest.lean:670:0: Expression match matSigsOf repeatPredPrepared with …`; `:752:0 … (checkPreparedBindings p).toOption.isSome repeatPredPrepared == some true`; `CollectPlanTest.lean:100:0 keysOf <$> plan64 h1 h1In == …`; `:101:0 bits64 (plan64 h1 h1In) "Y" == f64bits #[7.0, 13.0]`; `:123:0 bits32 (plan32 h1f32 h1In32) "Y" == f32bits #[7.0, 13.0]`; `:128:0 bits32 (plan32 h1 h1In32) "Y" == …` |
| Prepared.lean: drop the `privateSlotUnpublished` check | the junk-hidden-slot fixture | `CompileTest.lean:744:0: Expression match repeatPredPrepared with | some valid =>` |
| Collect.lean: no declaration clones | f64-declared Y: CompileTest `repeatSched` (explicitF64), CollectPlanTest f64 H1/H2/H3 | `CompileTest.lean:624:0: Expression (prepareEvalPlan repeatSched repeatSig).toOption.isSome did not evaluate to true`; `CollectPlanTest.lean:100:0 keysOf <$> plan64 h1 h1In == …`; `:101:0`; `:104:0`; `:139:0 matDtypes (prepared64 h1 h1In) == some #[("Y", ScalarDType.f64)]`; `:187:0 bits64 (plan64 h2 h2In) "Y" != bits64 (plan64 h2r h2In) "Y"` (H4 f64 is in the truncated tail) |
| Collect.lean: clone of a `.typedTensor` always `.f64` (f32 storage conflict) | f32-declared fixtures only | `Adapter32Test.lean:138:0: f32 repeat: prepare failed: capability: LeanNCD.Eval.Plan.CapabilityError.unsupportedDtype "Y#1: mixed f32/f64 storage in one schedule"`; `CollectPlanTest.lean:122:0 keysOf <$> plan32 h1f32 h1In32 == some ["A", "B", "Y"]`; `:140:0 matDtypes (prepared32 h1f32 h1In32) == …f32)]`; `:149:0 unpack32Keys h1f32 h1In32 == …`; `:196:0 bits32 (plan32 h2f32 h2In32) "Y" == some #[1061997773]`; `:245:0 (prepared32 h1f32 h1In32).isSome` |

The second row's absent cousin: the UNDECLARED f32 fixtures (H1 f32 undeclared, H2 f32 undeclared) do not
fail under the no-clone mutation. That is the §C.4 argument observed from the other side (undeclared `T`
and undeclared `T#k` are both default f32, so no storage conflict can arise); it is why the f64 fixtures
and the declared-f32 conflict mutant carry the clone-path coverage.

`mixedStorageKinds` is not an identifier in this codebase: the observed form of a mixed schedule is
`CapabilityError.unsupportedDtype "<first conflicting name>: mixed f32/f64 storage in one schedule"`
(Compile.lean Step 0b). Fixture H4 pins "no such error for `T#k`".

## T2: B3 on the checked side

New error: `InputBindingError.inputIsDefined (name : String)` (`Eval/Plan/Error.lean`), the family of the
existing input-binding errors reported by `pack`/`packBodyOf` (`missingEnvBinding`, `shapeMismatch`,
`storageMismatch`, `storageKindMismatch`). `runPreparedDense*` reports it as `PlanRunFailure.cause =
.binding (.inputIsDefined nm)`; a direct `unpack`/`unpack32` reports `PlanRunCause.binding (.inputIsDefined
nm)` (reusing the existing `binding` constructor). The name is the first of `PlanBindings.definedNames`
(`(sched.stmts.flatMap ScanStmt.writes).eraseDups`, schedule write order) that the supplied environment
holds: the same order the reference's `find?` uses, so both name the same tensor.

Observers: reference `evalScheduled` (`EvalError.inputIsDefined`), `runPreparedDense`, direct `unpack`,
direct `pack` (f64); `runPreparedDense32`, direct `unpack32`, direct `pack32` (f32; the reference refuses
f32). Tuple order below is (ref, run, unpack, pack) for f64 and (run, unpack, pack) for f32.

| Id | Program / supplied | Observed | Donor | Accept-neighbour |
|---|---|---|---|---|
| B3.1 f64 | H1s (`Y:=A`), supplied `Y` | `(some "Y", some "Y", some "Y", some "Y")` | CollectEvalTest J5 | same program, no `Y`: `(none, none, none, none)`; with unrelated `Unused`: `(none, none, none, none)` |
| B3.1 f32 | H1s undeclared, supplied `Y` | `(some "Y", some "Y", some "Y")` | B3.1 f64 | no `Y`: `(none, none, none)`; `Unused`: `(none, none, none)` |
| B3.1 f32 declared | `tensor f32` H1 (two writers) supplied `Y` | `(some "Y", some "Y", some "Y")` | B3.1 f32 | — |
| B3.2 f64 | H1 (`Y:=A; Y:=B`), supplied `Y` / `Y#1` / both | `Y` -> all `"Y"`; `Y#1` -> all `"Y#1"`; both -> all `"Y#1"` (write order: `Y#1,Y#2,Y`) | B3.1 | no supplied defined name: all `none` |
| B3.2 f32 | same, undeclared | `Y` -> `"Y"`; `Y#1` -> `"Y#1"`; both -> `"Y#1"` | B3.2 f64 | all `none` |
| B3.3 f64 | `ScanCompileTest.scratchSched` (explicitF64), supplied block-local scratch `T` | `(some "T", some "T", some "T", some "T")` | scratchSched | without `T`: all `none` |
| B3.3 f32 | same schedule undeclared (f32 default), f32 inputs | `(some "T", some "T", some "T")` | B3.3 f64 | without `T`: all `none` |
| twin | `CompileTest` ordered twin (`Y:=A·Z; Z:=B`, explicitF64), supplied `Z` | reference `inputIsDefined "Z"`; `runPreparedDense` `.binding (.inputIsDefined "Z")`; `unpack … #[]` same | CompileTest "Fixture 10's ORDERED twin" | the existing agreement run, now on `topologyInputs.erase "Z"` for BOTH backends (the twin used to supply `Z` to the plan) |

Parity statement: `PlanBindings.definedNames` is computed from the same schedule list the reference
checks (`checked.program` after collection), so the two sets are equal by construction; the fixtures pin the
reported name for plain outputs, collector outputs, private `T#k` and scan scratch.

Mutations (T2):

| Mutation | Failed | Exact strings (sample) |
|---|---|---|
| Adapter.lean `packBodyOf`: B3 check removed | direct-`pack` observers ONLY (the runner still refuses through `unpackBodyOf`; the `runPreparedDense`/`CompileTest` twin results are unchanged — the same "per-door line is invisible through the composite" trap as the storage-kind guards) | `CollectPlanTest.lean:329:0: Expression (s1.bind fun x => verdict64 x h1In yIn) == some (some "Y", some "Y", some "Y", some "Y") did not evaluate to true`; `:334:0 … verdict32 … == some (some "Y", some "Y", some "Y")`; `:341:0`, `:342:0`, `:343:0`, `:345:0`–`:347:0`; `:357:0 verdict64 scratchS64 …`; `:360:0 verdict32 ScanCompileTest.scratchSched …` |
| Adapter.lean `unpackBodyOf`: B3 check removed | direct-`unpack` observers and the CompileTest twin | `CompileTest.lean:1667:0: ordered twin with supplied Z: unpack reported Except.error (LeanNCD.Eval.Plan.PlanRunCause.resultStore (LeanNCD.Eval.Plan.PositionalInputError.storeArityMismatch 4 0))`; plus the same `CollectPlanTest.lean:329:0 … :360:0` set |
| Compile.lean: `definedNames` = public outputs only | private-name and scratch refusal | `CompileTest.lean:638:0: Expression Option.map (fun x => x.bindings.definedNames) repeatPrepared == some #["Y#1", "Y#2", "Y", "Z"] did not evaluate to true`; `CollectPlanTest.lean:342:0 (s1m … y1In) == some (some "Y#1", …)`; `:343:0`; `:346:0`; `:347:0`; `:357:0` (scratch f64); `:360:0` (scratch f32) |

Cycle count: T0 3 (+1 baseline guard check), T1/T2 9 mutation builds (no-partition, ignore-privateSlots,
drop-unpublished-check, no-clones x2 [first run truncated at 12 lines, rerun on CollectPlanTest only], f32
clone type, pack door, unpack door, definedNames), each restored; 12 mutation builds in total.
