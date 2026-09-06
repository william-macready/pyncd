# Task A report — Axis A boundary / invariant re-establishment audit

**Status: DONE_WITH_CONCERNS** (findings-only task completed in full; the concerns are two confirmed
S1 defects found, plus three factual corrections to the brief itself — see §4).

## What was done

A findings-only audit of the five in-scope boundary families in `LeanNCD/Eval/Plan`, verified by
construction against the real build. No production code was changed; `git diff` over
`leanncd/LeanNCD` and `experiments/` is empty. Nothing was added to `lakefile.toml`; no test module
was created.

**Build:** `cd leanncd && lake build` → `Build completed successfully (8660 jobs)` both before
starting and after finishing, unchanged.

**Deliverable:** `.superpowers/sdd/2026-09-06-pre-scatter-backend-audit/axis-a-fragment.md`
(fragment only — `papers/pre_scatter_backend_audit.md` was neither created nor edited, per the
controller's ruling).

**Construction evidence:** nine spike blocks in `leanncd/spikes/AxisABoundaryProbe.lean`
(gitignored scratch), copied for the record to
`.superpowers/sdd/2026-09-06-pre-scatter-backend-audit/axis-a-spikes/` together with the verbatim
run output. Every block prints observed behavior rather than asserting, so the audit records what
actually happened.

Spike inventory:

| Spike | Question | Outcome |
|---|---|---|
| S1 | Is a name↔slot *pairing* swap in `requiredInputs` caught? | No — accepted by `checkBindings`, `checkPreparedBindings`, and `preparedBindingsTied`; `runPreparedDense` returns `.ok` with `W = #[110.0, 220.0]` instead of `#[30.0, 300.0]` |
| S2 | Is `packChecked`'s `missingEnvBinding` arm reachable? | No — blocked earlier by `checkBindings` (`notAPermutation #[0,1] #[0]`); dead code |
| S3 | Is a `materializedNames` *name* checked? | No — output published under an input's name, input clobbered, declared output absent, `.ok` |
| S4 | The brief's input-dtype candidate: does checked diverge from reference on non-binary Boolean data? | No — `CHECKED P = #[0.5, 0.25]` and `LEGACY P = #[0.5, 0.25]`, identical. **Refuted.** |
| S5 | Does an input slot's `bool` tag change any Dense behavior? | No — `bool`- and `f64`-tagged input slots give identical results on identical data |
| S6 | Is the declaration-blind `ofDenseInputs` caught? | Yes — `InputSignatureError.dtypeMismatch "Z" bool f64` at Step B |
| S7 | Does `runDensePlan` re-check arity/shape/storage? | Yes, all three rejected; arbitrary floats at a `bool` slot accepted (same as `pack`) |
| S8 | Can a validated JAX kernel be reused at a `.pointwise` step index? | No — `JaxExecutableValidationError.invalidCandidate` |
| S9 | Are the `getD`/`replicate` defaults in `packChecked`/`runDensePlan` reachable? | No — `checkPlan` gives `slotOutOfRange 99 3` and `missingProduction 3` |

## Results

**41 inventory rows across 7 boundary groups.** 7 came back `assumed-unchecked`; the rest are
`enforced-by-type` or `re-checked`. Three findings:

- **BND-01 (S1 severity, Scatter: direct)** — a `requiredInputs` binding's NAME is never tied to the
  slot the schedule allocated for it. `checkBindings` checks the slot multiset (`Perm`) and name
  uniqueness (`Nodup`); a pairing swap satisfies both. `checkPreparedBindings` adds only the tie to
  `raw.inputSlots`, which the swapped multiset also satisfies. Constructed with public API only,
  runs `.ok`, returns a different answer with no diagnostic. `preparedBindingsTied` inherits the
  same blind spot, so the JAX executable path is affected too. **No existing test covers this** —
  `AdapterTest` Check 5 reverses the bindings *array* while preserving each pair, which is a
  different property.
- **BND-02 (S1 severity, Scatter: direct)** — a `materializedNames` binding's NAME is likewise
  unchecked. The slot *sequence* is compared for exact equality against `rawPublicationSlots`
  (a strong check, added by the round-4 fix), but the name beside it is compared against nothing.
  Renaming the output to an input's name publishes the result over the caller's input and drops the
  declared output name entirely, silently.
- **BND-03 (S4 severity, documentation)** — `Adapter.lean`'s `packChecked` doc comment and inline
  comment, and `Prepared.lean`'s `RequiredBindings` doc comment, all assert that alignment against
  `raw.inputSlots` is "producer discipline, not something the type enforces" and describe the
  `missingEnvBinding` arm as the fallback. `checkPreparedBindings` now re-checks exactly that, so
  the claim is stale and the arm is dead (S2). This matters beyond tidiness: those comments point an
  implementer at the wrong unchecked axis while saying nothing about the one that genuinely is
  unchecked (BND-01/02).

**The brief's own candidate defect is REFUTED**, on three independent counts documented in §4 of the
fragment: the checked and reference backends agree byte-for-byte on non-binary data through a
Boolean-algebra destination (S4); an input slot's dtype tag is behaviorally inert in the Dense path
(S5); and the dtype invariant that does exist — signature dtype vs declaration dtype — is
re-established loudly at `prepareEvalPlan` Step B (S6). "Runtime values are not restricted to 0/1"
is a stated contract (`admittedAlgebraBool`'s doc comment, `Eval/AGENTS.md` Contract (c)), not an
oversight.

**The brief's assessment of the 2026-09-05 consolidation is confirmed.** `0160f59`/`06604f2` closed
most of this surface genuinely. Slot ranges, publication sequences, store arity, signature-table
ties, shape/storage, kernel-to-step ties, and evidence aggregation are all either type-enforced or
re-checked with a located typed error. The `assumed-unchecked` count came in *below* the brief's
prediction. What remains open is one axis — **names** — unchecked at all three places it appears.

## Concerns / corrections to the brief

Three of the brief's stated facts did not survive verification. None changes the task's scope; all
three are recorded in the fragment's Verified-facts table.

1. **`private mk ::` count.** The brief says 16 repo-wide. There are **12** declaration sites
   (`grep -rn --include=*.lean -E "^\s*(structure .* where )?private mk ::" .`, excluding `.lake`);
   the extra grep hits are prose inside doc comments. No other constructor-privatization idiom is
   used anywhere in the repo.
2. **The hand-constructible set is three types, not two.** The brief names `PreparedPlan` and
   `JaxExecutableCandidate`. **`PlanBindings` is the third** — and it is the type both confirmed
   findings actually live in. It has a public constructor, no validator, and (per grep) no consumer
   that takes it as a parameter, so it is reached only through `PreparedPlan.bindings`, which is
   exactly why it was easy to overlook.
3. **The `Eval/Eval.lean` instance named in the brief is present but benign.** `evalScheduled` does
   pass `sched.decls` into `evalPlain`/`evalScan` rather than `checked.declEnv`, but `sched` there is
   `checked.program` and `decls` is an authoritative field, not a cached product; `buildDeclEnv`
   already rejected the one disagreement (`duplicateTensorDecl`) that could make `combineFor`'s
   first-match scan differ from a `DeclEnv` lookup. Verdict `re-checked`, not a finding.

## Constraints honored

- No production code changes (`git diff` over `leanncd/LeanNCD` and `experiments/` empty).
- `lakefile.toml` untouched; no test module added; nothing "fixed".
- No subagents dispatched.
- Only `axis-a-fragment.md` written under the SDD directory; `papers/pre_scatter_backend_audit.md`
  neither created nor edited.
- `LeanNCD/Eval/Plan/Scan.lean` was read only for context on `CheckedScanPlan`'s constructor
  privacy (type census) and its `signatureContextMismatch`/`storeArityMismatch` precedents cited in
  rows C7 and B1. **No write-geometry predicate was audited** — `writeRowKinds`, `baseWriteRowsOk`,
  `stepWriteRowsOk`, `writesCollide`, `freeExtentsAgree`, `pinnedLiteralsInRange`, and
  `stateReadCausal` are untouched and left entirely to Task B.
- Citations are by identifier, not `file:NNN`.

## Suggested handling (for the controller, not acted on)

BND-01 and BND-02 are one fix: a name-authenticity obligation. The cheapest shape is for
`prepareEvalPlan` to hand the name↔slot map forward as part of the checked artifact rather than as
an unvalidated sidecar, since `raw` deliberately carries no names and cannot re-derive it. That is a
design decision, not a mechanical fix, and it should be settled *before* Scatter adds
destination-side geometry beside `requiredInputs` — any new sidecar field inherits the same
checked-shape/unchecked-pairing posture by default. BND-03 is a three-comment edit and can ride
along with whatever lands first.
