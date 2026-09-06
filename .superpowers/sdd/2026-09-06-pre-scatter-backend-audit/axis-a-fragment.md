# Axis A — boundary / invariant re-establishment audit (findings only)

Base: `worktree-pre-scatter-audit` @ `2159d28`. Build green at **8660 jobs** before and after; no
production code was changed (`LeanNCD/` diff empty).

Construction evidence lives in `axis-a-spikes/AxisABoundaryProbe.lean` (a copy of the gitignored
`leanncd/spikes/AxisABoundaryProbe.lean`) with its verbatim run recorded in
`axis-a-spikes/AxisABoundaryProbe.output.txt`. Spike blocks are cited below as `S1`…`S9`.

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
| The hand-constructible set on the checked surface is **three** types, not two | `[read]` type census of `Eval/Plan` minus the ten `private mk ::` types: on the *checked* surface (types whose fields include an already-validated payload) the public-constructor complement is `PreparedPlan`, `PlanBindings`, and `JaxExecutableCandidate`. The brief named only the first and third; `PlanBindings` is the one it omitted, and it is the type both confirmed findings live in. |
| Every production `PreparedPlan` consumer in `LeanNCD/` routes through `checkPreparedBindings` | `[read]` the complete consumer list is `pack`, `unpack`, `runPreparedDense`, `packChecked`, `unpackChecked`, `materializedSignatures`, `preparedBindingsTied`, `stepTiedToPreparedStep`, and `checkPreparedBindings` itself; each either calls it or receives the `CheckedPreparedBindings` a caller obtained from it |
| `PlanBindings` has **no** consumer that takes it as a parameter | `[read]` grep for `PlanBindings` in `LeanNCD/`/`experiments/` returns only its own declaration; it is reached exclusively through `PreparedPlan.bindings` |
| `packChecked`'s and `runDensePlan`'s `raw.tensorSigs.getD` defaults are unreachable | `[snippet]` S9 — `checkPlan { raw with inputSlots := #[99] }` → `PlanStepError.assign (PlanError.slotOutOfRange 99 3)`. The bound is `checkStepGraph`'s first loop (`unless s < n`), which runs before any `CheckedEvalPlan` exists |
| `runDensePlan`'s `Array.replicate` placeholder can never be read | `[snippet]` S9 — adding an unproduced `tensorSigs` slot gives `PlanError.missingProduction 3` from `checkStepGraph`'s final loop |
| `runDensePlan`'s `inputs[i]!`, `store.set! slot` are in range | `[snippet]` S7 — `runDensePlan plan #[]` is rejected (`arityMismatch`), and slot bounds come from the same `checkStepGraph` bound above |
| `runDensePlan` re-checks shape and storage exactly as `packChecked` does | `[snippet]` S7 — wrong shape and wrong storage are both rejected; `[read]` the two loops apply the same two `unless` comparisons against `sig.shape`, in two independent copies |
| `packChecked`'s `| none => .missingEnvBinding` arm is **dead code** | `[snippet]` S2 — a `PreparedPlan` pairing a validly-checked one-input `RequiredBindings` against a two-slot `raw.inputSlots` is rejected earlier by `checkPreparedBindings` with `PreparedBindingsError.requiredInputs (BindingsError.notAPermutation #[0, 1] #[0])`. `checkPreparedBindings` re-runs `checkBindings` against `raw.inputSlots`, ignoring `RequiredBindings`' own stored field |
| A name↔slot *pairing* swap in `requiredInputs` is accepted and silently changes the answer | `[snippet]` S1 — `checkBindings`, `checkPreparedBindings`, and `preparedBindingsTied` all accept it; `runPreparedDense` returns `.ok` with `W = #[110.0, 220.0]` where the correct value is `#[30.0, 300.0]` |
| Renaming a materialized binding to an input's name is accepted and clobbers that input | `[snippet]` S3 — `runPreparedDense` returns `.ok`, `env["A"]` becomes the computed output `#[30.0, 300.0]`, and `W` is absent from the result environment |
| **The input-dtype candidate is REFUTED** — checked and reference backends agree on non-binary data through a Boolean destination | `[snippet]` S4 — a `predicate P(i)` destination over `X = [0.5, 0.25]`, `Y = [0.75, 0.1]` gives `CHECKED P = #[0.5, 0.25]` and `LEGACY P = #[0.5, 0.25]`, identical |
| An **input** slot's `bool` dtype tag changes no Dense behavior at all | `[snippet]` S5 — the same Float data through a `bool`-signature input slot and an `f64`-signature input slot both give `Q = #[0.25, 9.0]` |
| The declaration-blind signature producer is caught downstream, loudly | `[snippet]` S6 — `prepareEvalPlan sched (InputSignature.ofDenseInputs …)` on a program declaring a `predicate` input fails with `InputSignatureError.dtypeMismatch "Z" bool f64` at Step B |
| A validated JAX kernel cannot be re-used at a non-`.assign` step index | `[snippet]` S8 — `Y[i] := relu(X[i])` lowers to `#["assign", "pointwise"]`; a candidate whose step-0 einsum kernel is repeated at index 1 is rejected as `JaxExecutableValidationError.invalidCandidate` |
| Neither `prepareEvalPlan` nor `evalScheduled` reads a cached `sched` field after validation | `[read]` `prepareEvalPlan` binds `checked.declEnv`, `checked.explicitSizes`, `checked.extNames`; `evalScheduled` binds `checked.explicitSizes`. The only raw reads on either side are `sched.decls`/`sched.stmts`, which `ScheduledProgram`'s own contract makes authoritative (not cached products), and which are the exact values `validateScheduled` validated |
| `evalPlain sched.decls` and `checked.declEnv` provably cannot disagree | `[read]` `buildDeclEnv` rejects a second tensor-bearing declaration of a name (`CompileError.duplicateTensorDecl`), so `combineFor`'s first-match `decls.find?` and a `DeclEnv` lookup see the same declaration for every name that survives validation |
| No existing test covers the name↔slot pairing swap | `[read]` `AdapterTest.lean` Check 5 reverses the `requiredInputs` **array** while keeping each binding's own name↔slot pair intact, and asserts the *correct* result; nothing perturbs the pairing itself |

## 3. Boundary inventory

Columns: `Boundary` | `Consumed type` | `Constructor` | `Invariant` | `Producer establishes` | `Consumer re-checks` | `Verdict` | `Failure mode` | `Scatter` | `Severity`

### 3.1 `Adapter.packChecked` / `pack`

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| A1 | `PreparedPlan` | public | every `raw.inputSlots` slot has a bound name | `prepareEvalPlan` (`inputSlotsAcc`/`requiredInputsAcc` built together) | `checkPreparedBindings` → `checkBindings` (`Perm` against `raw.inputSlots`) | `re-checked` | loud typed error | direct | — |
| A2 | `PreparedPlan` | public | `raw.tensorSigs.getD slot` is in range | `checkStepGraph`'s input bound | `checkPlan` (before `CheckedEvalPlan` exists) | `enforced-by-type` | loud typed error | direct | — |
| A3 | `NamedDenseEnv` | public | each bound name is present in `env` | — | `packChecked`'s `env[name]?` → `InputBindingError.missingEnvBinding` | `re-checked` | loud typed error | direct | — |
| A4 | `DenseTensor` | public | tensor shape = signature shape | — | `packChecked` `unless t.shape == tsig.shape.toList` | `re-checked` | loud typed error | direct | — |
| A5 | `DenseTensor` | public | `data.size = ∏ shape` | — | `packChecked` `unless t.data.size == …foldl (· * ·) 1` | `re-checked` | loud typed error | direct | — |
| **A6** | `PlanBindings` | public | each `requiredInputs` binding's NAME is the name the schedule gave THAT slot | producer discipline only (`prepareEvalPlan` pushes `{name := nm, slot}` in one step) | none — `checkBindings` checks the slot multiset and name uniqueness, never the pairing | `assumed-unchecked` | silently-wrong-answer | direct | **S1** |
| A7 | `DenseTensor` | public | values are 0/1 when the slot's signature dtype is `bool` | not an invariant by design (`admittedAlgebraBool`'s doc comment; `Eval/AGENTS.md` Contract (c)) | none in Dense; the only consumer for which the tag is load-bearing (`jaxAssignSupported`) rejects a `bool` source outright | `assumed-unchecked` | loud typed error | adjacent | S4 |
| A8 | `PreparedPlan` | public | `requiredInputs.inputSlots` = the enclosing plan's `raw.inputSlots` | producer discipline (per both files' doc comments) | `checkPreparedBindings` — it ignores the stored field and re-runs `checkBindings` against `raw.inputSlots` | `re-checked` | loud typed error | direct | — |

### 3.2 `Adapter.unpackChecked` / `unpack` / `runPreparedDense`

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| B1 | `Array DenseTensor` | public | store arity = `raw.tensorSigs.size` | `runDensePlan` returns exactly that | `unpackChecked`'s exact-equality guard → `PositionalInputError.storeArityMismatch` | `re-checked` | loud typed error | direct | — |
| B2 | `PlanBindings` | public | every `materializedNames` slot is in the table | `prepareEvalPlan` allocates each in `tensorSigs` | `rawMaterializedWith` → `PlanError.slotOutOfRange` (via `checkPreparedBindings` and again via `materializedWith`) | `re-checked` | loud typed error | direct | — |
| B3 | `PlanBindings` | public | the materialized slot SEQUENCE is the raw plan's publication sequence | `prepareEvalPlan`'s per-statement push order | `checkPreparedBindings` vs `rawPublicationSlots` → `PreparedBindingsError.publicationSlots` | `re-checked` | loud typed error | direct | — |
| **B4** | `PlanBindings` | public | each `materializedNames` binding's NAME is the name the schedule assigns that slot | producer discipline only | none — only the slot sequence is compared; names are unconstrained | `assumed-unchecked` | silently-wrong-answer | direct | **S1** |
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
| C6 | `DenseTensor` | public | data respects the slot's `bool` dtype tag | not an invariant by design | none (S5: the tag is behaviorally inert here) | `assumed-unchecked` | loud typed error | adjacent | S4 |
| C7 | `CheckedEvalPlan` | `private mk ::` | the signature table executed under is the table checked against | `runDensePlan` reads `c.raw.tensorSigs`; there is no caller-supplied table to disagree with (unlike `runDenseScan`, which needs and has `signatureContextMismatch`) | n/a | `enforced-by-type` | loud typed error | direct | — |

### 3.4 `Prepared.lean` type set

| # | Consumed type | Constructor | Invariant | Producer establishes | Consumer re-checks | Verdict | Failure mode | Scatter | Sev |
|---|---|---|---|---|---|---|---|---|---|
| D1 | `RequiredBindings` | `private mk ::` + `checkBindings` | binding slots are a `Perm` of its own `inputSlots`, names `Nodup` | `checkBindings` | — | `enforced-by-type` | loud typed error | direct | — |
| D2 | `CheckedPreparedBindings` | `private mk ::` + `checkPreparedBindings` | the whole sidecar has been validated against the plan's own raw slots | `checkPreparedBindings` | — | `enforced-by-type` | loud typed error | direct | — |
| D3 | `PreparedPlan` | public | every consumer sees a validated sidecar | — | every production consumer calls `checkPreparedBindings` (complete list in §2) | `re-checked` | loud typed error | direct | — |
| D4 | `PlanBindings` | public | name↔slot pairings (both `requiredInputs` and `materializedNames`) | producer discipline only | none | `assumed-unchecked` | silently-wrong-answer | direct | **S1** |
| D5 | `PreparedPlan` | public | `warnings` are the preparation's own | producer discipline only | none — a hand-built plan can carry any warning list, or drop them | `assumed-unchecked` | silent no-op | none | S4 |

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
| **E8** | `JaxExecutableCandidate` | public | which NAME belongs to which slot in the source's `PlanBindings` | producer discipline only (documented as deliberately not re-derivable — `raw` carries no names) | none — `preparedBindingsTied` inherits `checkPreparedBindings`' blind spot (S1: it returns `true` on a name-swapped plan) | `assumed-unchecked` | silently-wrong-answer | adjacent | **S1** |
| E9 | `JaxKernelCandidate` | public | tables/operands are the ones the checked factor maps mean | — | `validateAffineTable`/`validateEinsum` recompute from the checked factors | `re-checked` | loud typed error | none | — |
| E10 | `JaxExecutableCandidate` | public | the located rejection reason survives to the caller | — | partially: `validateAndConstructExecutable` returns bare `invalidCandidate` for any per-step failure, and `jaxSupportOk` discards the located `JaxSupportError` and passes `nodeIndex 0` for every step | `assumed-unchecked` | silent no-op | adjacent | S4 |

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

Two findings. Both are the same underlying weakness at two ends of the same type, and both are
reachable, silent, and produce a wrong answer.

### BND-01 — a `requiredInputs` name↔slot pairing is never re-established, and swapping it silently feeds the wrong tensor to the wrong slot

- **Rows:** A6, D4, E8. **Severity S1** (silently-wrong-answer). **Scatter: direct.**
- **Boundary:** `Adapter.packChecked`; propagates to `Executable.preparedBindingsTied`.
- **What is unchecked:** `checkBindings` establishes exactly two properties of a `RequiredBindings` —
  the binding slots are a `List.Perm` of `inputSlots`, and the binding names are `Nodup`. Swapping
  the *pairing* (`A→0, B→1` becomes `B→0, A→1`) preserves both. `checkPreparedBindings` adds only the
  tie to `raw.inputSlots`, which the swapped multiset also satisfies. Nothing anywhere compares a
  name against the slot the schedule actually allocated for it — by design; `raw` carries no names.
- **Construction and observed output** (`S1`, spike `AxisABoundaryProbe.lean`), on `W[i] := A[i] · B[j]`
  with `A = [10, 100]`, `B = [1, 2]`:

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
- **Why no existing test catches it:** `AdapterTest.lean` Check 5 reverses the `requiredInputs`
  *array* while preserving each binding's own name↔slot pair, and asserts the correct result. That
  fixture is specifically about array-position-vs-`.slot` resolution; the pairing itself is never
  perturbed anywhere in the suite.
- **Why it matters before Scatter:** Scatter + affine LHS writes adds destination-side geometry that
  will need its own binding-sidecar entries. Any new sidecar field added beside `requiredInputs`
  inherits this same "checked-shape, unchecked-pairing" posture unless the pairing question is
  settled first.

### BND-02 — a `materializedNames` binding's NAME is never re-established, so an output can be published under an input's name

- **Rows:** B4, D4. **Severity S1** (silently-wrong-answer). **Scatter: direct.**
- **Boundary:** `Adapter.unpackChecked`; the same blind spot in `checkPreparedBindings`.
- **What is unchecked:** `checkPreparedBindings` compares `materializedNames.map (·.slot)` against
  `rawPublicationSlots raw` for exact equality — a genuinely strong slot-sequence check — and
  `rawMaterializedWith` bounds every slot. The `name` field is compared against nothing.
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

### BND-01-candidate (input dtype at the runtime input boundaries) — **REFUTED**

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
   re-establish here: the dtype they would be checking has no Dense consumer. (It does have a JAX
   consumer, `jaxAssignSupported`, which rejects a `bool` source outright and loudly.)
3. **The dtype invariant that *does* exist is re-checked, loudly, upstream.** The real obligation is
   "the external signature's dtype equals what the declaration commits the name to", and
   `prepareEvalPlan` Step B enforces it: `S6` shows the declaration-blind producer
   `InputSignature.ofDenseInputs` on a program declaring a `predicate` input failing with
   `InputSignatureError.dtypeMismatch "Z" bool f64`. `DenseTensor` has no dtype field to check
   against at run time, and by the time execution starts the signature has already been reconciled
   with the declaration.

Recorded as rows A7 and C6 (verdict `assumed-unchecked`, failure mode `loud typed error` — the only
consumer for which the tag is load-bearing rejects it loudly). Not a finding.

### BND-03 — two long doc comments assert a producer-discipline-only guarantee that is in fact re-checked (documentation defect)

- **Rows:** A8. **Severity S4** (diagnostic-quality). **Scatter: direct.**
- `Adapter.lean`'s `packChecked` doc comment and its inline comment, plus `Prepared.lean`'s
  `RequiredBindings` doc comment, all state that alignment of `requiredInputs.inputSlots` against
  the enclosing `PreparedPlan.plan.raw.inputSlots` is "producer discipline, not something the type
  enforces", and describe `packChecked`'s `| none => throw (.missingEnvBinding …)` arm as the
  fallback that handles the mismatch.
- That is no longer true. `checkPreparedBindings` re-runs `checkBindings` **against
  `raw.inputSlots`**, discarding `RequiredBindings`' own stored `inputSlots` field, and every path
  into `packChecked` goes through it. `S2` attempts exactly the construction those comments describe
  — a two-slot plan carrying a one-input plan's validly-checked `RequiredBindings` — and observes:

  ```
  S2 pack rejected with: LeanNCD.Eval.Plan.InputBindingError.invalidPreparedBindings
    (LeanNCD.Eval.Plan.PreparedBindingsError.requiredInputs
      (LeanNCD.Eval.Plan.BindingsError.notAPermutation #[0, 1] #[0]))
  ```

  The `missingEnvBinding` arm is dead code, and `checkBindings` is the identifier that blocks it.
- **Why this is worth a finding number rather than a note:** these comments are the first thing an
  implementer reads before touching this seam, and they point attention at the *wrong* unchecked
  axis. They say "the slot alignment is only producer discipline" (it is not) while saying nothing
  about the name pairing (which genuinely is — BND-01/BND-02). Under review pressure that
  misdirection is exactly how BND-01 survives another slice.

## 5. Open / unprobed

Named rather than omitted.

1. **`experiments/jax_bridge`'s own `PreparedPlan` consumers were not audited.** `EvalPlanCodegen.lean`
   (`generateForward`, `renderInputConstants`, `renderAffinePlanNamed`, `generateNamed`,
   `lowerCheckPlanToCandidate`), `EvalPlanAffineSmoke.lean`, and `EvalPlanAffineCorpus.lean` all take
   a `PreparedPlan` directly. Out of scope by the brief. BND-01/BND-02 reach them by construction
   (they consume the same name sidecar), but which of them re-establish anything was not checked.
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
4. **`PreparedPlan.warnings` (row D5)** is unvalidated and unvalidatable: a hand-built plan can carry
   any warning list, and every outcome path faithfully propagates whatever it finds. Recorded for
   completeness; there is no obvious check to add.
5. **Locator loss in the plan-level JAX path (row E10)** was read, not constructed: `jaxSupportOk`
   discards the located `JaxSupportError` and passes `nodeIndex 0` for every step, and
   `validateAndConstructExecutable` collapses every per-step failure into bare `invalidCandidate`.
   A construction showing which step index is lost was not built.
6. **`CheckedScanPlan`, `CheckedPlanBlock`, `CheckedPointwisePlan`, `CheckedAxiswisePlan`** appear in
   the type census as `private mk ::`-enforced and were not otherwise probed — `Scan.lean` is Task
   B's territory and the block/nonlinearity checkers were outside the five named families.

## 6. Count reconciliation

The brief predicted ~14–18 boundaries yielding ~10–12 `assumed-unchecked` cells needing 4–6
constructions. Actual: **41 rows across 7 boundary groups**, of which **7** came back
`assumed-unchecked` (A6, A7, C6, D4, D5, E8, E10 — three of those, A6/D4/E8, are the same name
defect seen from three consumers), and **9 construction fixtures** were built. The
`assumed-unchecked` count is
*lower* than predicted, which is itself a result: the 2026-09-05 consolidation (`0160f59`, `06604f2`)
genuinely closed most of this surface. What it did not close is a single axis — **names** — and that
axis is unchecked at every one of the three places it appears.
