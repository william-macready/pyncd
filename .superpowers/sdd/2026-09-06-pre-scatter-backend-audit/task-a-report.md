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

---

# Fix round 1 — report

**Status: DONE.** All four Important and all four Minor findings addressed. Two new construction
spikes were built to supply the evidence the promoted findings need. No production code changed.

**Build:** `cd leanncd && "$HOME/.elan/bin/lake" build` → `Build completed successfully (8660 jobs)`
— unchanged from baseline.
**Diff:** `git diff 2159d28 HEAD -- leanncd/LeanNCD/` → **empty**.

## Disposition

### Important 1 — the unchecked-name axis is a documented, test-pinned deliberate decision

Verified all four cited sites myself before citing them:

| Site | Text confirmed |
|---|---|
| `Prepared.lean`, `checkPreparedBindings` doc | "Names remain deliberately unauthenticated: positional raw IR can prove slots and required-name uniqueness, not origins." |
| `LeanNCD/Eval/AGENTS.md`, `Prepared.lean` row | "Raw plans prove slots but cannot authenticate names." |
| `test/Eval/Plan/CompileTest.lean` | comment "Exact publication is structural slot identity, not name authentication. … changing only names is valid", followed by a live `#guard` asserting `checkPreparedBindings` returns `.ok` on `materializedNames.map fun b => { b with name := "renamed" }` |
| `experiments/jax_bridge/README.md` | "…raw IR cannot authenticate the user-visible names themselves." |

Changes made:
- New Verified-facts row recording all four, cited by identifier/file.
- The single row "No existing test covers the name↔slot pairing swap" was **split in two**, because
  it was true only of BND-01's axis: one row states BND-01's axis is untested; a second states
  BND-02's axis is tested and pins acceptance as intended.
- Rows A6, B4, D4, E8 now name the documentation in their "Producer establishes" cell.
- BND-01 and BND-02 each gained a paragraph stating this explicitly, with BND-01's noting that the
  brief's Rule-12 instruction is why the verdict is unchanged.
- Retire-list added to §Suggested handling below: a fix must retire the `CompileTest.lean` `#guard`,
  the `checkPreparedBindings` doc sentence, `Eval/AGENTS.md`'s contract line, and
  `experiments/jax_bridge/README.md`'s line. Nothing was edited — the constraint to cite, not
  change, was respected.

### Important 2 — BND-03's rationale was factually wrong

Confirmed: `checkPreparedBindings`' doc comment does state the name gap, in the same file as the
`RequiredBindings` comment BND-03 criticises. The old paragraph claiming the comments "say nothing
about the name pairing" is deleted. The replacement argues the correct thing: the defect is
**misdirection about the slot axis** — an implementer is told the slot alignment is the fragile,
producer-discipline-only property and that `missingEnvBinding` is its safety net, and both halves
are false, so the hardening effort that claim invites is spent on an already-re-checked coupling.
BND-03 kept.

### Important 3 — §6 arithmetic

Corrected. **B4 was missing from the enumeration** — the row BND-02 rests on. §6 now reads: 41 rows,
**8** `assumed-unchecked` (A6, A7, B4, C6, D4, D5, E8, E10), and the follow-on prose is rewritten to
say that D4 spans both name axes and B4 is the materialized one, rather than the earlier muddled
"three of those are the same defect".

### Important 4 — finding numbering vs the mechanical rule

Reconciled in both directions, with a new §4.1 reconciliation table that a controller can check
mechanically:

- **D5 promoted to BND-04** (`assumed-unchecked` / `silent no-op`).
- **E10 promoted to BND-05** (`assumed-unchecked` / `silent no-op`).
- **BND-03 kept but explicitly labelled out-of-rule**, with its row (A8, `re-checked` /
  `loud typed error`) and the reason stated at the top of §4 and again in §6.
- **A7 and C6 depart from the closed Failure-mode vocabulary** (`n/a (no invariant)`), and that
  departure is now stated three times: a preamble to §3, the §4.1 table, and §6.

Counting `assumed-unchecked` rows with a non-`loud` failure mode gives 6 rows → **4** rule-derived
findings (BND-01, BND-02, BND-04, BND-05), with BND-03 listed as an explicitly out-of-rule fifth.
That reconciliation is stated in the fragment so a merging controller gets the same number.

Both promoted findings needed construction evidence the first pass did not have (§5 had said of
E10 that it "was read, not constructed"). Two spikes were added:

- **S10** (BND-04): on `Y[i, j] := X[2 * i + j]` with a 6-element `X`, the producer records one real
  `paddedAccess` warning. `{ prepared with warnings := [] }` runs `.ok` reporting **0** warnings
  while `Y`'s trailing zeros are genuinely zero-padded reads; and a plan with no padded read at all,
  given a borrowed warning list, runs `.ok` reporting **1** warning about a read it does not
  contain. Both directions silent.
- **S11** (BND-05): on a two-statement plan whose step **1** has a Boolean destination, the located
  gate called directly gives `JaxSupportError.destinationDType 1 3 bool`, while the only public
  entry a caller can reach reports `destinationDType 0 3 bool`. The locator is not absent but
  **wrong**, which is worse — `0` is a plausible answer. `S8` already supplied the plan-level half
  (bare `invalidCandidate`, no index, no cause).

### Minor 5 — BND-03's stale-site list was incomplete

Both additions verified before citing. The list is now six sites in two groups:

*Stale producer-discipline / `missingEnvBinding` claim (4):* `Adapter.lean` `packChecked` doc;
`Adapter.lean` `packChecked` inline loop comment; `Prepared.lean` `RequiredBindings` doc;
**`Error.lean` `InputBindingError` doc** — "If that coupling were ever broken by a hand-built
`PreparedPlan`, `pack` still fails loud — a `.missingEnvBinding` naming the unmatched slot".

*Misnamed shared resolver (2):* `Adapter.lean` `unpackChecked` doc and **`Error.lean`
`PlanRunCause.materialization` doc**, both saying "the shared `PlanBindings.materializedWith`" when
the function is `CheckedPreparedBindings.materializedWith` — a difference that is exactly the point
of the round-4 fix, since resolution is reachable only after validation.

### Minor 6 — A7/C6 failure mode imported another boundary's behavior

Agreed, it was a category slip. Both rows now read `n/a (no invariant)` in the Failure-mode column,
and their "Producer establishes" / "Consumer re-checks" cells say plainly that nothing establishes
the claim, nothing checks it, and the system does not hold it. The `jaxAssignSupported` reference is
removed from those cells; it survives in §1's scope list and row E2, where it belongs (not, as first
written here, "only in §4.7 as one of the three refutation counts" — §4.7 does not mention it at
all). The vocabulary departure is stated in §3's preamble rather than buried in a cell.

### Minor 7 — `PlanBindings` grep overstatement

Corrected and re-measured. `grep -rn --include=*.lean "PlanBindings" LeanNCD/ experiments/` returns
**16** hits: one `structure` declaration, one `PreparedPlan.bindings` field, fourteen doc-comment
mentions. (The review said 15; 16 is what the command returns here, over `LeanNCD/` plus
`experiments/`.) The row now states the substantive claim precisely — no function anywhere takes
`PlanBindings` as a parameter — and gives the breakdown instead of the false "returns only its own
declaration".

### Minor 8 — census exhaustiveness

`SomeJaxKernel` and `SomeJaxExecutable` are now named in the census row with the reason for
excluding them: each has a dependent second field (`kernel : JaxKernel evidence`,
`executable : JaxExecutable evidence`) that forces the exposed index to be the one a validated
payload was built with, so the wrapper admits no state its payload does not already permit. The row
no longer claims the three-type set is the whole public complement — it claims it is the set that
admits genuinely unconstrained field values.

## Suggested handling (updated; for the controller, not acted on)

BND-01 and BND-02 remain one fix: a name-authenticity obligation. The cheapest shape is still for
`prepareEvalPlan` to hand the name↔slot map forward as part of the checked artifact rather than as
an unvalidated sidecar, since `raw` deliberately carries no names and cannot re-derive it.

**A fix wave must be warned that this is a documented contract change, not a bug fix.** Landing it
turns a green test red and contradicts two prose contracts. The retire-list:

1. `test/Eval/Plan/CompileTest.lean` — the `#guard` asserting `checkPreparedBindings` accepts
   `materializedNames.map fun b => { b with name := "renamed" }`, and the comment above it
   ("changing only names is valid"). **The build goes red the moment the check is added if this is
   not retired in the same commit.**
2. `Prepared.lean` — `checkPreparedBindings`' doc sentence "Names remain deliberately
   unauthenticated…".
3. `LeanNCD/Eval/AGENTS.md` — the `Prepared.lean` row's contract line "Raw plans prove slots but
   cannot authenticate names."
4. `experiments/jax_bridge/README.md` — "raw IR cannot authenticate the user-visible names
   themselves."
5. Re-grep for further siblings of (1) before assuming the list is complete (§5 item 5).

BND-03 (six comment sites) and BND-05 (locator plumbing) are independent and can land in any order.
BND-04 is a design question — whether `warnings` should be a projection of the checked artifact
rather than a public field — and should not be bundled with the name fix.
