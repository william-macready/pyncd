# Axis A — boundary / invariant re-establishment audit (findings only)

Base: `worktree-pre-scatter-audit` @ `2159d28`. Build green at **8660 jobs** before and after; no
production code was changed (`git diff 2159d28 HEAD -- leanncd/LeanNCD/` empty).

Construction evidence lives in `leanncd/spikes/AxisABoundaryProbe.lean` (tracked in git via a
`leanncd/.gitignore` exception, off the default build) with its verbatim run recorded in
`leanncd/spikes/AxisABoundaryProbe.output.txt`. Spike blocks are cited below as `S1`…`S11`. (`S11`'s
index contrast is not sound evidence for any claim in this fragment — see BND-05, §4.6 — and is not
cited below.)

## 1. Scope

### In scope

| Boundary family | Entry points examined |
|---|---|
| Named↔positional runtime seam | `packChecked`, `unpackChecked`, `pack`, `unpack`, `runPreparedDense` (`Adapter.lean`) |
| Positional runtime seam | `runDensePlan`'s input loop and store allocation (`EvalPlan.lean`) |
| Prepared-plan type set | `RequiredBindings`, `PlanBindings`, `PreparedPlan`, `CheckedPreparedBindings`, `checkBindings`, `checkPreparedBindings`, `materializedWith`, `materializedSignatures` (`Prepared.lean`) |
| JAX executable phase | `checkJaxAssignSupport`, `jaxAssignSupported`, `JaxExecutableCandidate`, `stepTiedToPreparedStep`, `preparedBindingsTied`, `JaxExecutableWellFormed`, `validateAndConstructExecutable` (`Executable.lean`) |
| Signature producers | `InputSignature.ofDenseInputs`, `InputSignature.ofDenseInputsForDecls`, `dtypeOfDecl` (`Signature.lean`) |
| Post-consolidation schedule authority | one bounded row only: does `prepareEvalPlan` or `evalScheduled` read a raw `sched` field after `validateScheduled`? |

### Out of scope — deliberately not audited

- **This audit does NOT close `leanncd/AGENTS.md`'s UNAUDITED flag on semantic-payload finding #6.**
  The four boundary decoders that finding names — `realizeStMat`, `realizeBrBaseP`, `AcsetCodec`,
  and `realizeSBr` — were not examined here at all, and nothing in this fragment may be read as
  evidence about them. They remain UNAUDITED.
- `experiments/jax_bridge/EvalPlanCodegen.lean` and the other `experiments/jax_bridge` modules.
  Only the LeanNCD-side gates they call are covered, via `Executable.lean`.
- `LeanNCD/Eval/Plan/Scan.lean`'s write-geometry predicates — Task B's territory.

## 2. Verified facts

| Claim | How it was verified |
|---|---|
| Baseline and post-audit builds are green at 8660 jobs | `[built]` `cd leanncd && lake build` → `Build completed successfully (8660 jobs).` |
| The repo has **12** `private mk ::` declaration sites, not 16 | `[read]` `grep -rn --include=*.lean -E "^\s*(structure .* where )?private mk ::" .` (excluding `.lake`) returns 12 declaration lines; the remaining `private mk ::` grep hits are prose inside doc comments. Ten are under `Eval/Plan` (`CheckedAssignPlan`, `CheckedPointwisePlan`, `CheckedAxiswisePlan`, `CheckedScanPlan`, `CheckedPlanBlock`, `CheckedEvalPlan`, `RequiredBindings`, `CheckedPreparedBindings`, `JaxKernel`, `JaxExecutable`); the other two are `CheckedScheduledProgram` and `RouteFragments.lean`'s. No other constructor-privatization idiom is used anywhere. |
| The hand-constructible checked-surface set audited as its own boundary family here is **three** types, and other public hand-constructible types were excluded with reason | `[read]` type census of `Eval/Plan` minus the ten `private mk ::` types. Public-constructor types whose fields include an already-validated payload, audited directly as their own boundary family: `PreparedPlan`, `PlanBindings`, `JaxExecutableCandidate`. **`JaxKernelCandidate`** — a public inductive over the public structures `OrderedAffineTableKernelCandidate` and `EinsumExperimentKernelCandidate` — is also hand-constructible, and its `tables`/`operands`/`outputAxes` fields are genuinely unconstrained; it is not omitted from the audit, only from this list of three, because it is covered as row E9 (`re-checked`, via `validateAffineTable`/`validateEinsum`), and both S8 and S11 hand-build it directly as scaffolding for their own constructions. **`SomeJaxKernel` and `SomeJaxExecutable` are also public-constructor wrappers over `private mk ::` payloads and are deliberately excluded**, not overlooked: each has a dependent second field (`kernel : JaxKernel evidence`, `executable : JaxExecutable evidence`) that forces the exposed index to be the one a validated payload was built with, so the wrapper admits no state its payload does not already permit. The brief named only `PreparedPlan` and `JaxExecutableCandidate`; `PlanBindings` is the one it omitted, and it is the type on which every finding below rests. |
| The unchecked-name axis is a **documented, test-pinned deliberate decision**, recorded in four places | `[read]` (a) `Prepared.lean`, `checkPreparedBindings`'s doc comment: "Names remain deliberately unauthenticated: positional raw IR can prove slots and required-name uniqueness, not origins."; (b) `LeanNCD/Eval/AGENTS.md`, the `Prepared.lean` row: "Raw plans prove slots but cannot authenticate names."; (c) `test/Eval/Plan/CompileTest.lean`, comment "Exact publication is structural slot identity, not name authentication … changing only names is valid", and a live `#guard` later in the same section asserting `checkPreparedBindings` returns `.ok` on a plan whose every `materializedNames` entry has been renamed to `"renamed"`; (d) `experiments/jax_bridge/README.md`: "Every named codegen entry first validates the prepared binding sidecar against the raw plan's exact publication slots; raw IR cannot authenticate the user-visible names themselves." |
| Every production `PreparedPlan` consumer in `LeanNCD/` routes through `checkPreparedBindings` | `[read]` the complete consumer list is `pack`, `unpack`, `runPreparedDense`, `packChecked`, `unpackChecked`, `materializedSignatures`, `preparedBindingsTied`, `stepTiedToPreparedStep`, and `checkPreparedBindings` itself; each either calls it or receives the `CheckedPreparedBindings` a caller obtained from it |
| No function anywhere takes `PlanBindings` as a parameter | `[read]` `grep -rn --include=*.lean "PlanBindings" LeanNCD/ experiments/` returns **16 hits**: one `structure` declaration, one `PreparedPlan.bindings` field, and fourteen mentions inside doc comments. None is a parameter binder — the type is reachable only through `PreparedPlan.bindings`, which is why its own invariants are checked, if at all, by `PreparedPlan`'s consumers rather than by anything it owns. |
| `packChecked`'s and `runDensePlan`'s `raw.tensorSigs.getD` defaults are unreachable | `[snippet]` S9 — `checkPlan { raw with inputSlots := #[99] }` → `PlanStepError.assign (PlanError.slotOutOfRange 99 3)`. The bound is `checkStepGraph`'s first loop (`unless s < n`), which runs before any `CheckedEvalPlan` exists |
| `runDensePlan`'s `Array.replicate` placeholder can never be read | `[snippet]` S9 — adding an unproduced `tensorSigs` slot gives `PlanError.missingProduction 3` from `checkStepGraph`'s final loop |
| `runDensePlan`'s `inputs[i]!`, `store.set! slot` are in range | `[snippet]` S7 — `runDensePlan plan #[]` is rejected (`arityMismatch`), and slot bounds come from the same `checkStepGraph` bound above |
| `runDensePlan` re-checks shape and storage exactly as `packChecked` does | `[snippet]` S7 — wrong shape and wrong storage are both rejected; `[read]` the two loops apply the same two `unless` comparisons against `sig.shape`, in two independent copies |
| `packChecked`'s `| none => .missingEnvBinding` arm is **dead code** | `[snippet]` S2 — a `PreparedPlan` pairing a validly-checked one-input `RequiredBindings` against a two-slot `raw.inputSlots` is rejected earlier by `checkPreparedBindings` with `PreparedBindingsError.requiredInputs (BindingsError.notAPermutation #[0, 1] #[0])`. `checkPreparedBindings` re-runs `checkBindings` against `raw.inputSlots`, ignoring `RequiredBindings`' own stored field |
| A name↔slot *pairing* swap in `requiredInputs` is accepted and silently changes the answer | `[snippet]` S1 — `checkBindings`, `checkPreparedBindings`, and `preparedBindingsTied` all accept it; `runPreparedDense` returns `.ok` with `W = #[110.0, 220.0]` where the correct value is `#[30.0, 300.0]` |
| **No test covers the `requiredInputs` pairing swap (BND-01's axis)** | `[read]` `AdapterTest.lean` Check 5 reverses the `requiredInputs` **array** while preserving each binding's own name↔slot pair, and asserts the *correct* result; that fixture is about array-position-vs-`.slot` resolution. Nothing in the suite perturbs the pairing itself. |
| **A test DOES cover the `materializedNames` rename (BND-02's axis) — and pins acceptance as intended** | `[read]` `test/Eval/Plan/CompileTest.lean`'s `#guard` on `checkPreparedBindings` applied to `materializedNames.map fun b => { b with name := "renamed" }` asserts `.ok`. BND-02 is therefore not an untested gap but a *deliberately pinned* one; any fix must retire that `#guard`. |
| Renaming a materialized binding to an input's name is accepted and clobbers that input | `[snippet]` S3 — `runPreparedDense` returns `.ok`, `env["A"]` becomes the computed output `#[30.0, 300.0]`, and `W` is absent from the result environment |
| **The input-dtype candidate is REFUTED** — checked and reference backends agree on non-binary data through a Boolean destination | `[snippet]` S4 — a `predicate P(i)` destination over `X = [0.5, 0.25]`, `Y = [0.75, 0.1]` gives `CHECKED P = #[0.5, 0.25]` and `LEGACY P = #[0.5, 0.25]`, identical |
| An **input** slot's `bool` dtype tag changes no Dense behavior at all | `[snippet]` S5 — the same Float data through a `bool`-signature input slot and an `f64`-signature input slot both give `Q = #[0.25, 9.0]` |
| The declaration-blind signature producer is caught downstream, loudly | `[snippet]` S6 — `prepareEvalPlan sched (InputSignature.ofDenseInputs …)` on a program declaring a `predicate` input fails with `InputSignatureError.dtypeMismatch "Z" bool f64` at Step B |
| A validated JAX kernel cannot be re-used at a non-`.assign` step index | `[snippet]` S8 — `Y[i] := relu(X[i])` lowers to `#["assign", "pointwise"]`; a candidate whose step-0 einsum kernel is repeated at index 1 is rejected as `JaxExecutableValidationError.invalidCandidate` — with no step index and no underlying cause |
| `PreparedPlan.warnings` can be silently emptied AND silently fabricated | `[snippet]` S10 — a plan whose producer recorded one real `paddedAccess` warning runs `.ok` with `warnings reported = 0` after `warnings := []`; a plan whose producer recorded none runs `.ok` reporting a borrowed warning about a read that does not exist in it |
| The plan-level JAX executable path discards `checkJaxAssignSupport`'s located cause; the gate itself is correctly located at every real caller | `[snippet]` S8 — reusing a validated JAX kernel at a `.pointwise` step yields `JaxExecutableValidationError.invalidCandidate`, with no step index and no underlying cause; `[read]` `jaxSupportOk` hardcodes `checkJaxAssignSupport sigs 0` and returns only a `Bool`, and `validateAndConstructExecutable`'s well-formedness branch throws bare `.invalidCandidate`. `checkJaxAssignSupport` itself is a plain public `def`, correctly located, and is reached with a real outer step index by `EvalPlanCodegen.requireJaxSupport` at a plan-level call site (`renderAffineNode`); `validateAndConstructKernel`'s own hardcoded `0` is the documented standalone-entry convention, not a defect — `requireJaxSupport`'s doc states "0 at a standalone one", and `test/Eval/Plan/ExecutableTest.lean` pins exactly this: its `step1BoolAssign` fixture (commented as step 1 of the two-step `step1BoolRaw` plan) is validated in isolation via `affineOutcome`/`jaxOutcome`/`validateAndConstructKernel`, and the `#guard rejectedBy (.unsupported (.sourceDType 0 0 0 .bool))` asserting index `0` there is green. |
| Neither `prepareEvalPlan` nor `evalScheduled` reads a cached `sched` field after validation | `[read]` `prepareEvalPlan` binds `checked.declEnv`, `checked.explicitSizes`, `checked.extNames`; `evalScheduled` binds `checked.explicitSizes`. The only raw reads on either side are `sched.decls`/`sched.stmts`, which `ScheduledProgram`'s own contract makes authoritative (not cached products), and which are the exact values `validateScheduled` validated |
| `evalPlain sched.decls` and `checked.declEnv` provably cannot disagree | `[read]` `buildDeclEnv` rejects a second tensor-bearing declaration of a name (`CompileError.duplicateTensorDecl`), so `combineFor`'s first-match `decls.find?` and a `DeclEnv` lookup see the same declaration for every name that survives validation |

## 3. Boundary inventory

Columns: `Boundary` | `Consumed type` | `Constructor` | `Invariant` | `Producer establishes` | `Consumer re-checks` | `Verdict` | `Failure mode` | `Scatter` | `Severity`

**One departure from the closed Failure-mode vocabulary, stated up front.** Rows **A7** and **C6**
carry `n/a (no invariant)` rather than one of the five vocabulary values. Both concern the claim
"input tensor values are 0/1 when the slot's signature dtype is `bool`". Nothing establishes it and
nothing checks it, so the Verdict is honestly `assumed-unchecked` — but the system does not *hold*
that claim (`Check.lean`'s `admittedAlgebraBool` doc comment and `Eval/AGENTS.md` Contract (c) both
state the opposite explicitly), so there is no violation for a failure mode to describe. Assigning
one of the five values would either overstate harm (S4 proves both backends agree) or import a
different consumer's behavior. **Consequence for finding arithmetic: these two rows are
`assumed-unchecked` but are NOT findings, and §4's reconciliation table accounts for them
explicitly.**

### 3.1 `Adapter.packChecked` / `pack`

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| A1 | `PreparedPlan` | public | every `raw.inputSlots` slot has a bound name | `prepareEvalPlan` (`inputSlotsAcc`/`requiredInputsAcc` built together) | `checkPreparedBindings` → `checkBindings` (`Perm` against `raw.inputSlots`) | `re-checked` | loud typed error | direct | — |
| A2 | `PreparedPlan` | public | `raw.tensorSigs.getD slot` is in range | `checkStepGraph`'s input bound | `checkPlan` (before `CheckedEvalPlan` exists) | `enforced-by-type` | loud typed error | direct | — |
| A3 | `NamedDenseEnv` | public | each bound name is present in `env` | — | `packChecked`'s `env[name]?` → `InputBindingError.missingEnvBinding` | `re-checked` | loud typed error | direct | — |
| A4 | `DenseTensor` | public | tensor shape = signature shape | — | `packChecked` `unless t.shape == tsig.shape.toList` | `re-checked` | loud typed error | direct | — |
| A5 | `DenseTensor` | public | `data.size = ∏ shape` | — | `packChecked` `unless t.data.size == …foldl (· * ·) 1` | `re-checked` | loud typed error | direct | — |
| **A6** | `PlanBindings` | public | each `requiredInputs` binding's NAME is the name the schedule gave THAT slot | producer discipline only (`prepareEvalPlan` pushes `{name := nm, slot}` in one step); documented as deliberate in `checkPreparedBindings`' doc comment and `Eval/AGENTS.md` | none — `checkBindings` checks the slot multiset and name uniqueness, never the pairing | `assumed-unchecked` | silently-wrong-answer | direct | **S1** |
| A7 | `DenseTensor` | public | values are 0/1 when the slot's signature dtype is `bool` | nothing — and the system does not hold this claim (`admittedAlgebraBool` doc comment; `Eval/AGENTS.md` Contract (c) states values are deliberately unrestricted) | nothing | `assumed-unchecked` | *n/a (no invariant)* | adjacent | S4 |
| A8 | `PreparedPlan` | public | `requiredInputs.inputSlots` = the enclosing plan's `raw.inputSlots` | producer discipline (per four files' doc comments) | `checkPreparedBindings` — it ignores the stored field and re-runs `checkBindings` against `raw.inputSlots` | `re-checked` | loud typed error | direct | — |

### 3.2 `Adapter.unpackChecked` / `unpack` / `runPreparedDense`

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| B1 | `Array DenseTensor` | public | store arity = `raw.tensorSigs.size` | `runDensePlan` returns exactly that | `unpackChecked`'s exact-equality guard → `PositionalInputError.storeArityMismatch` | `re-checked` | loud typed error | direct | — |
| B2 | `PlanBindings` | public | every `materializedNames` slot is in the table | `prepareEvalPlan` allocates each in `tensorSigs` | `rawMaterializedWith` → `PlanError.slotOutOfRange` (via `checkPreparedBindings` and again via `materializedWith`) | `re-checked` | loud typed error | direct | — |
| B3 | `PlanBindings` | public | the materialized slot SEQUENCE is the raw plan's publication sequence | `prepareEvalPlan`'s per-statement push order | `checkPreparedBindings` vs `rawPublicationSlots` → `PreparedBindingsError.publicationSlots` | `re-checked` | loud typed error | direct | — |
| **B4** | `PlanBindings` | public | each `materializedNames` binding's NAME is the name the schedule assigns that slot | producer discipline only; documented as deliberate, and a `CompileTest.lean` `#guard` pins acceptance of a wholesale rename | none — only the slot sequence is compared; names are unconstrained | `assumed-unchecked` | silently-wrong-answer | direct | **S1** |
| B5 | `PreparedPlan` | public | metadata and execution resolve the same bindings | one shared `rawMaterializedWith` behind `CheckedPreparedBindings.materializedWith`, used by both `unpackChecked` and `materializedSignatures` | n/a — shared, not duplicated | `enforced-by-type` | loud typed error | direct | — |
| B6 | `PreparedPlan` | public | `pack` and `unpack` inside one run see the same checked view | `runPreparedDense` calls `checkPreparedBindings` once and threads the result | n/a | `enforced-by-type` | loud typed error | direct | — |

### 3.3 `EvalPlan.runDensePlan` positional input loop

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| C1 | `Array DenseTensor` | public | `inputs.size = raw.inputSlots.size` (guards `inputs[i]!`) | `packChecked` pushes exactly that many | `runDensePlan`'s `arityMismatch` guard | `re-checked` | loud typed error | direct | — |
| C2 | `CheckedEvalPlan` | `private mk ::` + `checkPlan` | `raw.tensorSigs.getD slot` and `store.set! slot` in range | `checkStepGraph`'s `unless s < n` | — (not re-derived; the type carries it) | `enforced-by-type` | loud typed error | direct | — |
| C3 | `CheckedEvalPlan` | `private mk ::` + `checkPlan` | every store slot is written before it is read, so the `Array.replicate` placeholder is never observed | `checkStepGraph`'s forward-read check + `missingProduction` | — | `enforced-by-type` | loud typed error | direct | — |
| C4 | `DenseTensor` | public | shape = signature shape | — | `runDensePlan`'s own `shapeMismatch` guard | `re-checked` | loud typed error | direct | — |
| C5 | `DenseTensor` | public | `data.size = ∏ shape` | — | `runDensePlan`'s own `storageMismatch` guard | `re-checked` | loud typed error | direct | — |
| C6 | `DenseTensor` | public | data respects the slot's `bool` dtype tag | nothing — and the system does not hold this claim (see A7) | nothing (S5: the tag is behaviorally inert here) | `assumed-unchecked` | *n/a (no invariant)* | adjacent | S4 |
| C7 | `CheckedEvalPlan` | `private mk ::` | the signature table executed under is the table checked against | `runDensePlan` reads `c.raw.tensorSigs`; there is no caller-supplied table to disagree with (unlike `runDenseScan`, which needs and has `signatureContextMismatch`) | n/a | `enforced-by-type` | loud typed error | direct | — |

### 3.4 `Prepared.lean` type set

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| D1 | `RequiredBindings` | `private mk ::` + `checkBindings` | binding slots are a `Perm` of its own `inputSlots`, names `Nodup` | `checkBindings` | — | `enforced-by-type` | loud typed error | direct | — |
| D2 | `CheckedPreparedBindings` | `private mk ::` + `checkPreparedBindings` | the whole sidecar has been validated against the plan's own raw slots | `checkPreparedBindings` | — | `enforced-by-type` | loud typed error | direct | — |
| D3 | `PreparedPlan` | public | every consumer sees a validated sidecar | — | every production consumer calls `checkPreparedBindings` (complete list in §2) | `re-checked` | loud typed error | direct | — |
| **D4** | `PlanBindings` | public | name↔slot pairings — BOTH axes: `requiredInputs` (see A6) and `materializedNames` (see B4) | producer discipline only, documented as deliberate | none | `assumed-unchecked` | silently-wrong-answer | direct | **S1** |
| **D5** | `PreparedPlan` | public | `warnings` are the preparation's own | producer discipline only | none — a hand-built plan can carry any warning list, or drop them | `assumed-unchecked` | silent no-op | none | S4 |

### 3.5 `Executable.lean`

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| E1 | `Array TensorSignature` | public | the caller-supplied table really describes the assignment | — | `checkJaxAssignSupport` re-runs `checkAssign` → `JaxSupportError.invalidSignatureContext` | `re-checked` | loud typed error | none | — |
| E2 | `CheckedAssignPlan` | `private mk ::` | the assignment is JAX-renderable (dest dtype, algebra, context, source dtype, unary) | `checkAssign` admits all of these | `jaxAssignSupported`, in the declared order | `re-checked` | loud typed error | none | — |
| E3 | `JaxExecutableCandidate` | public | step count = the prepared plan's raw step count | — | `JaxExecutableWellFormed`'s first conjunct | `re-checked` | loud typed error | adjacent | — |
| E4 | `JaxExecutableCandidate` | public | each kernel's stored table = the prepared plan's own | — | `stepTiedToPreparedStep`'s first conjunct | `re-checked` | loud typed error | adjacent | — |
| E5 | `JaxExecutableCandidate` | public | each kernel's assignment is THAT step's checked assignment (and a non-`.assign` step gets none) | — | `stepTiedToPreparedStep`'s `| _ => false` arm | `re-checked` | loud typed error | adjacent | — |
| E6 | `JaxExecutableCandidate` | public | declared evidence = the aggregation of its steps' | the `aggregated : evidence = …` proof field | `validateAndConstructExecutable`'s `decide`, and the fourth `JaxExecutableWellFormed` conjunct | `enforced-by-type` | loud typed error | none | — |
| E7 | `JaxExecutableCandidate` | public | the source's own bindings describe its own raw plan | — | `preparedBindingsTied` → the same `checkPreparedBindings` | `re-checked` | loud typed error | adjacent | — |
| **E8** | `JaxExecutableCandidate` | public | which NAME belongs to which slot in the source's `PlanBindings` | producer discipline only (documented as deliberately not re-derivable — `raw` carries no names; see `Executable.lean`'s `JaxExecutableWellFormed` note and `experiments/jax_bridge/README.md`) | none — `preparedBindingsTied` inherits `checkPreparedBindings`' blind spot (S1: it returns `true` on a name-swapped plan) | `assumed-unchecked` | silently-wrong-answer | adjacent | **S1** |
| E9 | `JaxKernelCandidate` | public | tables/operands are the ones the checked factor maps mean | — | `validateAffineTable`/`validateEinsum` recompute from the checked factors | `re-checked` | loud typed error | none | — |
| **E10** | `JaxExecutableCandidate` | public | the located rejection reason and step index survive to the caller | `checkJaxAssignSupport` takes and carries a real `nodeIndex` | none — `validateAndConstructKernel` hardcodes `nodeIndex 0`, `jaxSupportOk` discards the located cause entirely, and `validateAndConstructExecutable` collapses every per-step failure into bare `invalidCandidate` | `assumed-unchecked` | silent no-op | adjacent | S4 |

### 3.6 `Signature.lean`

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| F1 | `InputSignature` | public | every signature dtype is admitted by the plan layer | `ofDenseInputs` (always `f64`), `ofDenseInputsForDecls` (`dtypeOfDecl`) | `prepareEvalPlan` Step B → `InputSignatureError.dtypeNotAdmitted` | `re-checked` | loud typed error | none | — |
| F2 | `InputSignature` | public | signature dtype = the declaration's dtype | `ofDenseInputsForDecls` via the shared `dtypeOfDecl`; `ofDenseInputs` does NOT | `prepareEvalPlan` Step B → `InputSignatureError.dtypeMismatch` (S6) | `re-checked` | loud typed error | none | — |
| F3 | `List Decl` | public | the declaration list is itself well-formed | — | `ofDenseInputsForDecls` re-runs the shared `buildDeclEnv` → `CompileError.duplicateTensorDecl`; `ofDenseInputs` consults no declaration and so has nothing to degrade | `re-checked` | loud typed error | none | — |
| F4 | `InputSignature` | public | signature shapes match the tensors later bound at run time | producer discipline when the caller uses either `ofDense*` constructor on the same map | `packChecked`/`runDensePlan` shape+storage guards | `re-checked` | loud typed error | direct | — |

### 3.7 Post-consolidation schedule authority (single bounded row)

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| G1 | `ScheduledProgram` | public | neither execution entry consults a cached `sched` field after validation | `validateScheduled` projects `declEnv`/`explicitSizes`/`extNames` onto `CheckedScheduledProgram` | both entries bind only those projections; the only raw reads are `sched.decls`/`sched.stmts`, which are authoritative rather than cached, and `Eval.lean`'s `evalPlain sched.decls` provably agrees with `checked.declEnv` because `buildDeclEnv` already rejected the one disagreement (`duplicateTensorDecl`) | `re-checked` | loud typed error | adjacent | — |

**The known instance named in the brief is confirmed present and benign.** `Eval/Eval.lean` does pass
`sched.decls` into `evalPlain`/`evalScan` rather than `checked.declEnv`, but `sched` there is
`checked.program` and `declEnv` is a total function of `decls` that `validateScheduled` already
computed; the historical disagreement (`combineFor`'s first-match scan vs the env's last-wins
lookup) is exactly what `duplicateTensorDecl` closes. This is a style/authority inconsistency, not a
defect: it costs nothing today and is worth one line of cleanup if `DeclEnv` ever gains a field
`decls` cannot re-derive.

## 4. Findings

### 4.1 Reconciliation with the brief's mechanical rule

The rule: a finding is a row where Verdict = `assumed-unchecked` AND Failure mode ≠
`loud typed error`. **Amendment:** the rule presupposes an invariant that is assumed-but-unchecked —
it has no subject to apply to on a row whose Invariant column records no invariant at all. Rows
carrying `n/a (no invariant)` (A7, C6; see §3's preamble) therefore fall outside the rule entirely,
regardless of whatever value happens to sit in their Failure-mode column — this is a clause on the
rule's own domain, not an extra verdict value or an ad hoc third exception. Applied to the remaining
rows:

| Rows with Verdict `assumed-unchecked` | Failure mode | Finding under the rule? | Number |
|---|---|---|---|
| A6 | silently-wrong-answer | yes | BND-01 |
| B4 | silently-wrong-answer | yes | BND-02 |
| D4 | silently-wrong-answer | yes | BND-01 **and** BND-02 (D4 is the `Prepared.lean` face of both name axes) |
| E8 | silently-wrong-answer | yes | BND-01 (its `Executable.lean` face) |
| D5 | silent no-op | yes | BND-04 |
| E10 | silent no-op | yes | BND-05 |
| A7 | *n/a (no invariant)* | **no** — outside the rule's domain (amendment above); also §3 preamble | — |
| C6 | *n/a (no invariant)* | **no** — outside the rule's domain (amendment above); also §3 preamble | — |

**8 `assumed-unchecked` rows; 6 of them are findings under the rule; those 6 map to 4 distinct
defects (BND-01, BND-02, BND-04, BND-05)**, because one defect spans several consumers of the same
type.

**BND-03 is deliberately outside the rule and is labelled so.** It sits on row **A8**, whose verdict
is `re-checked` / `loud typed error` — not a finding by the mechanical rule. It is recorded anyway,
under a BND number for continuity with the review thread, because it is a documentation defect that
actively misdirects an implementer at this exact seam. A controller counting `assumed-unchecked`
rows should expect **4** rule-derived findings and see BND-03 listed as a fifth, explicitly
out-of-rule entry.

### 4.2 BND-01 — a `requiredInputs` name↔slot pairing is never re-established, and swapping it silently feeds the wrong tensor to the wrong slot

- **Rows:** A6, D4, E8. **Severity S1** (silently-wrong-answer). **Scatter: direct.**
- **Boundary:** `Adapter.packChecked`; propagates to `Executable.preparedBindingsTied`.
- **What is unchecked:** `checkBindings` establishes exactly two properties of a `RequiredBindings` —
  the binding slots are a `List.Perm` of `inputSlots`, and the binding names are `Nodup`. Swapping
  the *pairing* (`A→0, B→1` becomes `B→0, A→1`) preserves both. `checkPreparedBindings` adds only the
  tie to `raw.inputSlots`, which the swapped multiset also satisfies. Nothing anywhere compares a
  name against the slot the schedule actually allocated for it.
- **This is a documented deliberate decision, not an oversight.** `checkPreparedBindings`' own doc
  comment states it ("Names remain deliberately unauthenticated: positional raw IR can prove slots
  and required-name uniqueness, not origins"), `LeanNCD/Eval/AGENTS.md` carries it as a contract
  ("Raw plans prove slots but cannot authenticate names"), and `experiments/jax_bridge/README.md`
  repeats it. The row is nevertheless classified by observed behavior, per the brief's Rule-12
  instruction — "deliberate" is not one of the verdict values, and the consequence below is real
  regardless of intent.
- **Construction and observed output** (`S1`), on `W[i] := A[i] · B[j]` with `A = [10, 100]`,
  `B = [1, 2]`:

  ```
  S1 producer bindings   : #[{ name := "A", slot := 0 }, { name := "B", slot := 1 }]
  S1 raw.inputSlots      : #[0, 1]
  S1 checkBindings ACCEPTED the name swap
  S1 checkPreparedBindings on swapped plan: true
  S1 preparedBindingsTied on swapped plan: true
  S1 runPreparedDense .ok  W = shape=[2] data=#[110.000000, 220.000000]  (correct is shape=[2] data=#[30.000000, 300.000000])
  S1 baseline (unswapped)  W = shape=[2] data=#[30.000000, 300.000000]
  ```

  `runPreparedDense` returns `.ok`. No warning, no diagnostic. `110/220` is `B · ΣA`; the correct
  answer is `A · ΣB = 30/300`.
- **Reachability, not hypothetical:** `PlanBindings` and `PreparedPlan` both have public
  constructors, `checkBindings` is the public builder, and `AdapterTest.lean` already builds these
  values by struct update. The swap above uses only public API.
- **Test coverage:** none. `AdapterTest.lean` Check 5 reverses the `requiredInputs` *array* while
  preserving each binding's own name↔slot pair, and asserts the correct result; that fixture is
  specifically about array-position-vs-`.slot` resolution. The pairing itself is untested.
- **Why it matters before Scatter:** Scatter + affine LHS writes adds destination-side geometry that
  will need its own binding-sidecar entries. Any new sidecar field added beside `requiredInputs`
  inherits this same "checked-shape, unchecked-pairing" posture unless the pairing question is
  settled first.

### 4.3 BND-02 — a `materializedNames` binding's NAME is never re-established, so an output can be published under an input's name

- **Rows:** B4, D4. **Severity S1** (silently-wrong-answer). **Scatter: direct.**
- **Boundary:** `Adapter.unpackChecked`; the same blind spot in `checkPreparedBindings`.
- **What is unchecked:** `checkPreparedBindings` compares `materializedNames.map (·.slot)` against
  `rawPublicationSlots raw` for exact equality — a genuinely strong slot-sequence check — and
  `rawMaterializedWith` bounds every slot. The `name` field is compared against nothing.
- **This axis is not merely undefended; acceptance is PINNED BY A LIVE TEST.**
  `test/Eval/Plan/CompileTest.lean` carries the comment "Exact publication is structural slot
  identity, not name authentication. … changing only names is valid", followed by a `#guard`
  asserting `checkPreparedBindings` returns `.ok` on a plan whose every `materializedNames` entry
  has been renamed to `"renamed"`. So unlike BND-01, this is not an untested gap — it is a tested,
  intended one, and any fix necessarily turns that green `#guard` red.
- **Construction and observed output** (`S3`), same fixture, renaming the single materialized
  binding from `W` to `A` (an input's name) while keeping its slot:

  ```
  S3 producer materializedNames: #[{ name := "W", slot := 2 }]
  S3 checkPreparedBindings on renamed: true
  S3 .ok  A = shape=[2] data=#[30.000000, 300.000000] (input A was shape=[2] #[10.0, 100.0])
  S3 .ok  W = <absent>
  ```

  `runPreparedDense` returns `.ok`, the caller's own input `A` is overwritten by the plan's output,
  and the declared output name `W` is simply absent from the returned environment. A caller that
  reads `env["W"]?` gets `none`; a caller that reads `env["A"]?` gets a value that looks like a
  legitimate tensor.
- **Note on scope:** this is not the out-of-range-slot defect the round-4 review already fixed. Slots
  are fully checked now (`slotOutOfRange`, `publicationSlots`, `storeArityMismatch` — all confirmed
  live in `AdapterTest`). It is the orthogonal *name* axis, which that fix did not touch.
- **Retire list — required if BND-01/BND-02 are ever fixed.** Landing a name-authenticity check for
  either axis turns currently-green documentation and a currently-green test red, and both must be
  retired in the same commit as the fix, not left for a later agent to discover. Cited here, not
  edited, per this audit's constraints:
  1. `test/Eval/Plan/CompileTest.lean` — the `#guard` asserting `checkPreparedBindings` accepts
     `materializedNames.map fun b => { b with name := "renamed" }`, and its comment above it ("Exact
     publication is structural slot identity, not name authentication … changing only names is
     valid"). The build goes red the moment a name check is added if this is not retired in the same
     commit.
  2. `Prepared.lean` — `checkPreparedBindings`'s doc sentence "Names remain deliberately
     unauthenticated: positional raw IR can prove slots and required-name uniqueness, not origins."
  3. `LeanNCD/Eval/AGENTS.md` — the `Prepared.lean` row's contract line "Raw plans prove slots but
     cannot authenticate names."
  4. `experiments/jax_bridge/README.md` — "raw IR cannot authenticate the user-visible names
     themselves."
  5. Re-grep for further siblings of (1) before assuming this list is complete — see §5 item 5.

### 4.4 BND-03 — four doc comments make a stale producer-discipline claim, and two misname the shared resolver (documentation defect, **outside the mechanical rule**)

- **Row:** A8 (`re-checked` / `loud typed error`). **Severity S4** (diagnostic-quality).
  **Scatter: direct.** Recorded despite not meeting the finding rule; see §4.1.
- **The stale claim.** Four doc comments state that alignment of `requiredInputs.inputSlots` against
  the enclosing `PreparedPlan.plan.raw.inputSlots` is producer discipline that the type does not
  enforce, and describe `packChecked`'s `| none => throw (.missingEnvBinding …)` arm as the loud
  fallback that catches a mismatch:
  1. `Adapter.lean`, `packChecked`'s doc comment;
  2. `Adapter.lean`, the inline comment inside `packChecked`'s slot loop;
  3. `Prepared.lean`, `RequiredBindings`' doc comment ("IMPORTANT SCOPE NOTE");
  4. `Error.lean`, `InputBindingError`'s doc comment ("If that coupling were ever broken by a
     hand-built `PreparedPlan`, `pack` still fails loud — a `.missingEnvBinding` naming the unmatched
     slot").
- **Why it is stale.** `checkPreparedBindings` re-runs `checkBindings` **against `raw.inputSlots`**,
  discarding `RequiredBindings`' own stored `inputSlots` field, and every path into `packChecked`
  goes through it. `S2` attempts exactly the construction those comments describe — a two-slot plan
  carrying a one-input plan's validly-checked `RequiredBindings` — and observes:

  ```
  S2 pack rejected with: LeanNCD.Eval.Plan.InputBindingError.invalidPreparedBindings
    (LeanNCD.Eval.Plan.PreparedBindingsError.requiredInputs
      (LeanNCD.Eval.Plan.BindingsError.notAPermutation #[0, 1] #[0]))
  ```

  The `missingEnvBinding` arm is dead code for this cause, and `checkBindings` is the identifier that
  blocks it.
- **Two further sites misname the shared resolver.** `Adapter.lean`'s `unpackChecked` doc and
  `Error.lean`'s `PlanRunCause.materialization` doc both say resolution goes "through the shared
  `PlanBindings.materializedWith`". No such function exists; it is
  `CheckedPreparedBindings.materializedWith`, and the difference is exactly the point of the round-4
  fix — resolution is reachable only *after* validation, not off a bare `PlanBindings`.
- **Corrected rationale for recording this at finding weight** (the first version of this fragment
  argued, wrongly, that the comments "say nothing about the name pairing"; they do — see below).
  `checkPreparedBindings`' own doc comment, ~100 lines further down the same file, states the name
  gap explicitly. The defect is not silence about the name axis but **misdirection about the slot
  axis**: an implementer reading `packChecked` or `InputBindingError` is told the slot alignment is
  the fragile, producer-discipline-only property and that `missingEnvBinding` is its safety net.
  Both halves are false, and the effort that claim invites — hardening a coupling that is already
  re-checked — is effort not spent on the axis that genuinely is unchecked. Four stale sites plus
  two misnamed ones, all in the seam Scatter will extend, is more than a stray comment.

### 4.5 BND-04 — `PreparedPlan.warnings` is unvalidated, so a real diagnostic can be dropped and a false one invented

- **Row:** D5. **Severity S4** (diagnostic-quality). **Scatter: none.**
- **What is unchecked:** `PreparedPlan.warnings : List EvalWarning` is a public field with no
  validator. `runPreparedDense` faithfully propagates whatever it finds through every outcome path
  — which is the documented, correct behavior for a producer-built plan, and exactly the wrong
  behavior for a hand-built one.
- **Construction and observed output** (`S10`), on `Y[i, j] := X[2 * i + j]` with a 6-element `X`
  (a genuine out-of-range read, so the producer records one real `paddedAccess` warning):

  ```
  S10 producer warnings count: 1 [padded-access warning: X[…] max-index 8 ≥ dim 6; out-of-range reads will be zero-padded]
  S10 checkPreparedBindings on silenced plan: true
  S10 silenced run .ok, warnings reported = 0 (a real paddedAccess warning was dropped, Y = shape=[4, 3] data=#[1.0, 2.0, 3.0, 3.0, 4.0, 5.0, 5.0, 6.0, 0.0, 0.0, 0.0, 0.0])
  S10 clean plan producer warnings: 0
  S10 fabricated run .ok, warnings reported = 1 [padded-access warning: X[…] max-index 8 ≥ dim 6; …]
  ```

  Both directions are silent. In the first, `Y`'s trailing zeros are genuinely zero-padded reads and
  the warning that would have explained them is gone. In the second, a plan with no padded read at
  all reports a padded-access warning about a read it does not contain.
- **Judgement:** real, reachable, and silent — hence a finding under the rule — but low severity.
  Warnings are outcome data, not correctness (`Eval/AGENTS.md`, Wave E 4i), and there is no obvious
  check to add short of making `warnings` a projection of the checked artifact rather than a field.
  Recorded so a fix wave can decide deliberately rather than discover it.

### 4.6 BND-05 — the plan-level JAX executable path discards `checkJaxAssignSupport`'s located cause

- **Row:** E10. **Severity S4** (diagnostic-quality). **Scatter: adjacent.**
- **What is unchecked:** `checkJaxAssignSupport` is carefully located — it takes a `nodeIndex` and
  every `JaxSupportError` constructor carries it, and it is correctly threaded at every real caller:
  `EvalPlanCodegen.requireJaxSupport` passes the real outer step index at its plan-level call site
  (`renderAffineNode`, and its `einsum`-mode sibling), and an explicit index at a standalone call.
  The locator loss is one layer up, in the plan-level validators: `jaxSupportOk` (the `Bool` view
  those validators use) hardcodes `checkJaxAssignSupport sigs 0` and discards the located cause down
  to a `Bool`; `validateAndConstructKernel` likewise hardcodes `checkJaxAssignSupport sigs 0` for its
  own single-candidate check — the correct convention there, see below, but it means nothing upstream
  of it ever receives a per-step index either; and `validateAndConstructExecutable` collapses every
  per-step tie or well-formedness failure — including `stepTiedToPreparedStep`'s own per-step
  `mapIdx` check, which does know which index failed — into a bare `invalidCandidate`, with no index
  and no cause.
- **`0` at a standalone entry is a documented convention, not a bug.** `requireJaxSupport`'s doc
  comment states it directly: "Located at `nodeIndex` — the real outer step index at a plan-level
  caller, `0` at a standalone one." `test/Eval/Plan/ExecutableTest.lean` pins exactly this: its
  `step1BoolAssign` fixture is commented as step **1** of the two-step `step1BoolRaw` plan, but the
  `#guard rejectedBy (.unsupported (.sourceDType 0 0 0 .bool))` that checks it validates it in
  isolation, through the standalone `affineOutcome`/`jaxOutcome`/`validateAndConstructKernel` path —
  and asserting index `0` there is intended and green. An earlier version of this finding read that
  `0` (from `validateAndConstructKernel`'s own hardcoded call) as evidence the locator is "wrong at
  every public entry"; it is not — a standalone entry has no outer step to report, `0` is its
  documented sentinel, and `checkJaxAssignSupport` itself is reached correctly-located by
  `requireJaxSupport` at the one production entry that is NOT standalone. A future reader should not
  re-derive this contrast as a defect.
- **Construction and observed output** (`S8`): a validated JAX kernel, built and validated at step 0
  of an assign/pointwise plan, reused at step 1 (a `.pointwise` step) is rejected as
  `JaxExecutableValidationError.invalidCandidate` — no step index, no underlying cause.
- **Judgement:** diagnostic-quality only — nothing incorrect executes, since every one of these paths
  correctly *rejects*. But `validateAndConstructExecutable`'s collapse throws away information
  `stepTiedToPreparedStep`/`JaxExecutableWellFormed` already compute, and it is the layer a Scatter
  lowering would extend with new rejection constructors.

### 4.7 BND-01-candidate (input dtype at the runtime input boundaries) — **REFUTED**

The brief's unconfirmed candidate was that a `predicate`-declared input bound to a tensor of `0.5`s
would pass `pack`, be fed to the Boolean `(min, max)` algebra, and give a silently wrong answer.
Investigated first, by construction, and refuted on three independent counts:

1. **Both backends agree.** `S4` runs `predicate P(i); P[i] := X[i] · Y[j]` (a Boolean-algebra
   destination, `admittedAlgebraBool` selected) over `X = [0.5, 0.25]`, `Y = [0.75, 0.1]`:
   `CHECKED P = #[0.5, 0.25]` and `LEGACY P = #[0.5, 0.25]` — byte-identical. There is no
   checked/reference divergence to be silent about; literal Float `min`/`max` on non-binary data is
   the *specified* behavior (`Check.lean`'s `admittedAlgebraBool` doc comment, `Eval/AGENTS.md`
   Contract (c): "runtime values are NOT restricted to `0.0`/`1.0` … adding a truth check would
   create a checked/reference divergence").
2. **An input slot's dtype tag is behaviorally inert in the Dense path.** `S5` prepares the same
   program twice — once with the input declared `predicate` (slot signature `bool`), once
   undeclared (`f64`) — with identical Float data, and gets identical results
   (`Q = #[0.25, 9.0]` both times). So there is no invariant for `packChecked` or `runDensePlan` to
   re-establish here.
3. **The dtype invariant that *does* exist is re-checked, loudly, upstream.** The real obligation is
   "the external signature's dtype equals what the declaration commits the name to", and
   `prepareEvalPlan` Step B enforces it: `S6` shows the declaration-blind producer
   `InputSignature.ofDenseInputs` on a program declaring a `predicate` input failing with
   `InputSignatureError.dtypeMismatch "Z" bool f64`. `DenseTensor` has no dtype field to check
   against at run time, and by the time execution starts the signature has already been reconciled
   with the declaration.

Recorded as rows A7 and C6, verdict `assumed-unchecked` with failure mode `n/a (no invariant)` — the
stated departure from the closed vocabulary explained in §3's preamble and accounted for in §4.1.
Not a finding.

## 5. Open / unprobed

Named rather than omitted. (Two items from the first version of this fragment — `PreparedPlan.warnings`
and the JAX locator loss — have been promoted to BND-04 and BND-05 with construction evidence and are
no longer listed here.)

1. **`experiments/jax_bridge`'s own `PreparedPlan` consumers were not audited.** `EvalPlanCodegen.lean`
   (`generateForward`, `renderInputConstants`, `renderAffinePlanNamed`, `generateNamed`,
   `lowerCheckPlanToCandidate`), `EvalPlanAffineSmoke.lean`, and `EvalPlanAffineCorpus.lean` all take
   a `PreparedPlan` directly. Out of scope by the brief. BND-01/BND-02 reach them by construction
   (they consume the same name sidecar, and `experiments/jax_bridge/README.md` states the name gap as
   a known property), but which of them re-establish anything was not checked.
2. **Three `experiments/jax_bridge` entry points use the declaration-blind `InputSignature.ofDenseInputs`**
   (`EvalPlanAffineSmoke.lean`, `EvalPlanAffineCorpus.lean`, `EvalPlanSmoke.lean`). A corpus or
   fixture program that declares a `predicate` *input* would abort those runs at Step B with
   `dtypeMismatch` rather than mis-execute (S6), so this is loud — but it is a latent run-script
   breakage, not a silent one, and it was not exercised against the live corpus here.
3. **Two independent copies of the same shape/storage rule.** `packChecked` and `runDensePlan` each
   code `t.shape == sig.shape.toList` and `t.data.size == ∏ shape` separately;
   `Adapter.lean`'s own comment records why (the shared helper is private and typed to
   `PositionalInputError`). They agree today (S7 vs A4/A5). Not a finding — both check — but it is a
   two-copy rule at exactly the boundary Scatter will extend with destination-side geometry.
4. **`CheckedScanPlan`, `CheckedPlanBlock`, `CheckedPointwisePlan`, `CheckedAxiswisePlan`** appear in
   the type census as `private mk ::`-enforced and were not otherwise probed — `Scan.lean` is Task
   B's territory and the block/nonlinearity checkers were outside the five named families.
5. **Whether the `CompileTest.lean` rename `#guard` has siblings elsewhere in the suite** was not
   swept exhaustively; the one cited in §2 was found by grepping for `renamed`/`name authentication`
   and is the only hit, but a fix wave should re-grep rather than trust that.

## 6. Count reconciliation

**Row total: 41** (8 + 6 + 7 + 5 + 10 + 4 + 1 across §§3.1–3.7).

**`assumed-unchecked` rows: 8** — A6, A7, B4, C6, D4, D5, E8, E10.

**Findings under the brief's mechanical rule: 6 rows → 4 distinct defects.** A6 / D4 / E8 are one
defect seen from three consumers (BND-01); B4 / D4 are the materialized-name axis (BND-02, and D4
spans both name axes); D5 is BND-04; E10 is BND-05. A7 and C6 are `assumed-unchecked` but carry the
stated `n/a (no invariant)` failure mode and are not findings — §3's preamble and §4.1 explain why.
**BND-03 is a fifth listed entry that is explicitly outside the rule** (row A8 is
`re-checked`/`loud typed error`).

The brief predicted ~14–18 boundaries yielding ~10–12 `assumed-unchecked` cells needing 4–6
constructions. Actual: 41 rows, 8 `assumed-unchecked`, 11 construction fixtures. The
`assumed-unchecked` count is *lower* than predicted, which is itself a result: the 2026-09-05
consolidation (`0160f59`, `06604f2`) genuinely closed most of this surface. What it did not close is
a single axis — **names** — and that axis is unchecked at every one of the three places it appears,
by a decision recorded in four documents and pinned green by one test.
