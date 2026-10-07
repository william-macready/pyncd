# Site table: the "undeclared or plain `tensor` meets the binary64 carrier" family (f32 flip, slice 2)

Deliverable of Task 6 (plan section 3). One row per module this slice touched; columns are the
entry-point cases of the plan's section-3 table. Sources: `plan_modules.md` (per-module classification,
result and site tables), the slice-2 log, and for DifferentialTest the build/diff of this task.

Cell legend (class of the site under the flip):

- **R** required: the site pairs an undeclared / plain name with the binary64 carrier; fixed by wrapping
  (`p.explicitF64`, `explicitF64Sched`, `evalScheduledF64`) or by re-spelling `f64` at source. The
  parenthesis names the fix.
- **F** forbidden: the site pins the default itself (binary32); it must stay undeclared / plain. Class
  (ii) re-pins and new default probes live here.
- **S** silently ignored: no wrap and the test still passes (candidate instance N+1; listed below).
- `-` no such site in the module; `ok` site exists and is already explicit (`f64` / `f32` declared).

Provenance caveat: the SignatureTest, Scatter*, CompileTest, ScanCompileTest, AdapterTest and Adapter32Test
cells are transcribed from `plan_modules.md`; NonlinCompileTest line numbers and the DifferentialTest row come
from a grep/diff of the committed files; the StructuralTest and ComplexElementTypeTest rows come from their
commit messages and the slice-2 log (`a646311`, `5ac707c`), not a fresh line-level grep.

Cases: C1 `compileToScheduled` then `prepareEvalPlan` with `ofDenseInputs env`; C2 hand-built
`ScheduledProgram` decls + `ofDenseInputs`; C3 `TLProgram.eval` legacy; C4 `evalScheduled` direct; C5
`ofDenseInputsForDecls` / `...32ForDecls`; C6 `dtypeOfDecl` / `storageConstraintOfDecl` pins; C7
bool-only plans through the `Float` runner; C8 scan state names (`stateSigs` fallback).

| Module | C1 | C2 | C3 | C4 | C5 | C6 | C7 | C8 |
|---|---|---|---|---|---|---|---|---|
| SignatureTest | R (`gn2Prog.explicitF64`) | - | - | - | R (`conversionInputs` declared `f64` at source) + F (new undeclared neighbour pinned `storageKindMismatch`) | F (5 re-pins to f32/`.float32`; `.typedTensor .f64` named as the binary64 spelling) | - | - |
| ScatterCompileTest | R (`schedOf`, `assertScatterParity`: `.explicitF64`) | - | - | R (reuses the wrapped `sched`) | - | - | - | - |
| Scatter32OracleTest | ok (f32 legs declare `tensor f32`) | - | - | - | R (`run64` twins: `tensor f64` at source in O1/O5 `contrast64`) | - | - | - |
| NonlinCompileTest | R (`sourceCompileCauseOf`, `compiledEqB`, `reluProg`, `softmaxProg`: `.explicitF64`, lines 40/65/264/283) | R (`axiswiseSched`: `explicitF64Decls`, line 93) | R (`legacyAccepts`, `legacyErrorOf`, `sourceEvalOf`: `TLProgram.eval p.explicitF64`, lines 48/54/347) | - | - | - | - | - |
| CompileTest | R (`warnProg.explicitF64` x2) | R (local `explicitF64Sched` on ~12 literals; 8 more re-spelled `.typedTensor .f64` at source) + S (13 rejection-only literal families, see below) | - | R (reference legs of the 4 `assert*Parity` helpers ride the wrapped schedules) | - | F (15 class (ii) re-pins in 4b: plain/undeclared pinned f32, `f64` neighbours kept) | - | R (`scanPredSched*`, `rankScanSched` via `explicitF64Sched` over `ScanStmt.sourceStmts`) |
| ScanCompileTest | R (`prepared`, `withPrepared`, `t4run`, `s6Accept`, assert helpers, 11 direct sites: `explicitF64Sched`) | R (`rejSched`/`rej2Sched`/`s6Schedule` constructors) | - | R (`t4diff` reference leg `evalScheduledF64`) | - | F (new pin: undeclared playground has every `tensorSigs` entry `.f32`; `rejF32` control; 6 re-homed rejection fixtures run UNWRAPPED against `rejSigF32`) | - | R (`explicitF64Sched` declares scan-body `X`/`S`; `scratchF32Sched` re-spells `S` `f64`) + S (2 capability fixtures, below) |
| AdapterTest | R (4 `tlprog!` defs `.explicitF64`) | R (5 scan call sites `explicitF64Sched`) + S (`scanWarnSched` stays undeclared on purpose, below) | R (`zeroCoeffProg`, `warnProg`: lever on the def) | R (`scratchSched`, `scanWarnSched` wrapped at the call) | - (carrier is the held-fixed side) | - | `predIdentityProg`: unchanged (declares its predicate) | R (Check 16 loop wraps `sched`) |
| Adapter32Test | R (4 binary64 twins: `tensor f64` at source) ; f32 legs ok | - | R (`warnProgF64` declared `tensor f64` at source) | - | R (`f64ReductionProg`, `expOobProgF64`, `f64AttnProg` twins: `tensor f64` at source; f32 legs ok) | - (no `.float64`-default pin; every dtype pin sits on an explicit `f32` program) | - | - |
| DifferentialTest | R (`checkEntry`, `envOf`, 8 other compile sites, alpha pair: `p.explicitF64`) | R (`scanParityCheck`, `scanParity2`: `explicitF64Sched`; 5 direct `prepareEvalPlan`/`evalScheduled` sites wrapped; 3 hand-built `.tensor "X"` decls re-spelled `.typedTensor .f64`) | - (Gen's own guard uses `p.explicitF64`) | R (`envOf`, 3 direct sites, via the wrapped scheds) | R (declared `f64` in the predicate/scatter/bool-scalar corpora; `AT12`, `SA6`-`SA8`: `tensor f64` at source) | - (module pins nothing of the default) | R (`checkBoolScalar` compile wrapped, a no-op on the declared predicate) | R (`ScanGen` 17-case corpus through `c.prog.explicitF64`) |
| StructuralTest | - (DSL elaboration only; no evaluator entry point) | - | - | - | - | F (`b` untyped pinned `.float32`; new `b'` explicit `f64` pinned `.float64`; `d` spelled `f64`) | - | - |
| ComplexElementTypeTest | - | - | R* (neighbour programs declare `f64`; complex rows stay rejected, untouched) | R* (same) | R (neighbour decls `f64`) | - | - | R (`evalScan` neighbour declares `X` and `S` `f64`) |

## Confirmation: modules that already use the lever or are unaffected (grep, not assumed)

`rg -n "explicitF64|ofDenseInputs\b" <file> --max-count 5` and a per-file count of the section-3 tokens:

| file | section-3 tokens | lever use | verdict |
|---|---|---|---|
| `test/Eval/PropertyOracle/Oracle.lean` | 3 `TLProgram.eval` | all 3 pass `.explicitF64` (lines 14, 20, 25) | already uses the lever |
| `test/Eval/PropertyOracle/Gen.lean` | 2 | guard at line 165: `TLProgram.eval p.explicitF64 env` over all of `enumPrograms` | already uses the lever (the pinned 3832 corpus is defined by this guard) |
| `test/Eval/PropertyOracle/ScanGen.lean` | 3 `TLProgram.eval` | lines 150, 202, 218 all `.explicitF64` | already uses the lever |
| `test/Eval/PropertyOracle/ScanOracle.lean` | 6 | `evalScheduledF64` (lines 53, 121) and `explicitF64Decls` at the one direct `evalScheduled` (line 171); the remaining tokens are `schedOfCase` defs/prose | already uses the lever |
| `test/Eval/PropertyOracle/ScanUnroll.lean` | 20 | `independentRun` wraps both `evalScheduled` calls with `explicitF64Decls` (lines 872, 892); the rest are docs/defs | already uses the lever at its evaluator calls; `schedOfCase` (line 918) itself returns an undeclared schedule, see S below |
| `test/Eval/PropertyOracle/Compare.lean` | 0 | none needed | unaffected (no entry-point site) |
| `test/Eval/Portfolio/Harness.lean` | 7 `TLProgram.eval` | all 7 `prog.explicitF64` (lines 29, 42, 59, 69, 89, 98, 105) | already uses the lever |

## S cells found (candidate instance N+1)

1. CompileTest, 13 rejection-only literal families (`acceptedSched`, `unsizedSched`, `predicateSourceSched`,
   `predicateAggSched`, `outOfOrderSched`, `selfReadSched`, `dupDeclSched`, `predDupSched`/`predUnreadableSched`/
   `predTwoStmtSched`, `rank*Sched` rejections, `scanAxisKindSched`, `dtypeSourceOrderSched`). Not wrapped: the
   pinned error is raised before the storage/dtype pass, so wrapping would change which pass reports it.
   Cost to harden: 0 dispatches for the pins (exact earlier cause is asserted); a vacuity risk exists only if a
   pass is ever reordered past the dtype check, which the exact-cause assertions would then catch.
2. ScanCompileTest, the two capability fixtures (`capabilityBeforeInputScatter` with `emptySig`): decided
   before any dtype check, so default-insensitive (mutation-confirmed silent in Task 5b). Cost: 0.
3. AdapterTest `scanWarnSched`: public def deliberately left undeclared (reused by DifferentialTest line 759);
   every consumer wraps (`AdapterTest` 552/559, `DifferentialTest` via `scanParityCheck`). A new unwrapped
   consumer would see an f32 schedule against the f64 carrier, but would fail loudly (`dtypeMismatch`), not
   silently. Cost: 0 now; parking only.
4. `PropertyOracle/ScanUnroll.lean:918 schedOfCase` (public) returns an undeclared schedule. In-file consumers
   at 929/973/997 are structural and pass; evaluators downstream wrap (ScanOracle `evalScheduledF64`,
   `independentRun`, DifferentialTest `scanParityCheck`). Not verified vacuous or non-vacuous line by line.
   Cost to resolve: ~1 small dispatch (wrap or declare in `schedOfCase`; touches a shared module, so it is a
   Rule 14 scope-gate item, parked).
5. DifferentialTest itself: the mutation (`dtypeOfDecl` arms back to `.f64`) produces no failure and no changed
   output (`total=3832 accepted=3832`, `total=17 accepted=17` identical). The module is explicit `f64` after the
   fix, so it is default-insensitive by construction; the pin of the default lives in SignatureTest,
   CompileTest, ScanCompileTest and DefaultF32Test. Not a defect; recorded so the silence is not misread.

No S cell was found in AdapterTest/Adapter32Test beyond item 3, nor in Scatter*/Signature/Nonlin/Structural.
