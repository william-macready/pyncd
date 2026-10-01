# F32-C execution record

Companion to `papers/f32c_evalplan.md`: execution-time measurements (manifest tables, the re-derived
§4 audit, job counts). Authoring-time measurements stay in `papers/f32c_prototype_notes.md`.

The plan says this file "starts at Task 1's first commit"; Tasks 1 and 2 did not create it (their
measurements live in the SDD ledger, `.superpowers/sdd/f32c_evalplan/task-{1,2}-report.md`). It is
first created here, by Task 3 phase 1.

## Task 3 phase 1 — source admission and the independent oracle

Tree: `worktree-f32c-scans-plan`, base `77f111a` + `papers/f32c_files/task3.patch` + the prose
edits below. Build: `bash leanncd/scripts/lake-build.sh leanncd` → `Build completed successfully
(8673 jobs)` (plan: 8672 + 1 new module; observed 8673).

### Observed values (all equal the plan's)

- `CompileTest` fixture 15(d) (`f32ScanProg`): `causeOf … == none` (admitted).
- Fixture 2.9, both orders (`f32ScatterThenScanProg`, `f32ScanThenScatterProg`, `f32IdentitySig`):
  `.inputSignature (.missingSignature "S0")`.
- Two-scan pair, both orders (`f32TwoScanProg`, `f32ScanSig`): `.inputSignature (.missingSignature
  "T0")`.
- FW2a (`f32ScatterReluThenScanProg`): `.capability (.unsupportedNonlin "Y: scatter nonlinearity")`.
- `ScanDense32Test` Part C: 9 guards green (C1 identity, C3 scan-local scatter, C4 predicate-only,
  C2 identity/relu pair, C5 base relu/identity pair, C6 step softmax, C7 base softmax).
- `ScanDense32Test` Part D: 3 `agrees` guards green. Both legs were also printed (`#eval`, scratch
  file, not shipped) to confirm neither is vacuous — both `.ok`, bit-equal:
  - `linProg .identity`: oracle `("S", [0x4B800000 ×3])`, scan worker `[0x4B800000 ×3]`.
  - `linProg (.pointwise .relu)` / `reluIn`: both `[0x4B800000, 0x4B800000, 0]`.
  - `scatProg`: both `[0x4B800000, 0x4B800000, 0, 0, 0x41B00000, 0x41B00000, 0, 0, 0x42040000,
    0x42040000, 0, 0]`.

### Fixture re-points: what they no longer pin (owned, not hidden)

Fixture 2.9's pair and the two-scan pair (`f32TwoScanProg`) **no longer pin source order**. Both
used to observe `f32CapabilityCheck`'s first-rejection-wins traversal; with Step 0c deleted and scan
admitted, every statement in either program passes Steps 0b and A, and Step B (first-seen-read
signature validation) answers with the same payload in both orders. No binary32 source-order
capability traversal remains to pin. FW2a no longer witnesses a 0c-before-A order; it now witnesses
Step A answering ahead of Step B (the program also lacks `S0` in `f32IdentitySig`). FW2b still pins
Step 0b ahead of Step A. The `CompileTest` prose around these fixtures (Fixture 15's heading, the
2.9 docstring and heading, the two-scan comment, the FW2 docstring and FW2a/FW2b comments) was
rewritten to say this; the patch's own comments still claimed `f32TwoScanProg` pins source order.

### Prose edits beyond the patch (all in files this task touches)

- `CapabilityError.unsupportedDtype` docstring (`Error.lean`): the Step 0c bullet replaced with the
  plan's text (Step 0c DELETED by F32-C, all four contexts producer-less); the lead-in "Both
  producers are in `prepareEvalPlan`" corrected to one producer (Step 0b).
- `Compile.lean`: the `## Binary32 source capability` module-doc section that described the deleted
  `f32CapabilityCheck` removed with it; `checkDecl`'s `.typedTensor` comment no longer cites Step 0c;
  `compileScan`'s base-branch comment "their OWN result-slot pushes stay literal `.f64`" (made false
  by the `destDtype` fix) rewritten.

### `Types.lean` — checked, no edit needed (Task 3 phase 1 step 4)

`ScalarDType`'s docstring says `f32` "remains rejected by every BINARY64 entry — `dtypeAdmitted`,
`checkAssign`, `checkScanPlan`, `checkPointwise`/`checkAxiswise`, `checkPlanBlock`, and each Float
worker/adapter door." Re-checked against the tree, true for each scan/block name:
`checkScanPlan := checkScanCore .float64`, whose state loop applies `scanDtypeAdmitted .float64 =
dtypeAdmitted` (`.f32 => false`) — pinned by `ScanTest` f32 fixture 10 (`stateDtypeNotAdmitted 0 2
.f32`, unedited); `checkPlanBlock := checkPlanBlockCore .float64`, whose gate `unless k == kind ||
all-bool` refuses a real-f32 table as `storageKindNotAdmitted .float32` (`BlockTest`, `ScanTest`
unedited pins). The sentence never claimed f32 has no admission path — only that these binary64
entries reject it, which remains literally true. **Accurate; not edited.**

### §4 re-derivation against the post-Task-3-phase-1 tree

Every door the tables name was located with `rg` and read. Doors opened: `compileScan`'s four
nonlinear result-slot pushes (`destDtype`, base/step × pointwise/axiswise) and its preactivation
push (`destDtype`, unchanged); `prepareEvalPlan` (no Step 0c; Step 0b → Step A → Step B …);
`checkScanScatterOpts` (`opts.fill != 0` integer check, carrier-free); `checkPlan`'s `.scan`
`localCheck` arm (selects `checkScanPlan`/`checkScanPlanF32` by `storageKind`; no capability loop);
`checkScanCore` (state loop `scanDtypeAdmitted kind`; `checkPlanBlock`/`checkPlanBlockF32` by kind;
BOTH blocks checked before EITHER `checkCaptures kind` call); `checkPlanBlockCore` (gate `k == kind ||
all-bool`, then `localCheck` selecting `checkAssign`/`checkAssignF32`, `checkPointwise`/
`checkPointwiseF32`, `checkAxiswise`/`checkAxiswiseF32` by kind; stamps `kind`); `runDenseScan`/
`runDenseScan32` and `runDenseBlock`/`runDenseBlock32` (each guards `storageKind` as its first
statement, then calls the private `…With` worker with `0.0`/`(0.0 : Float32)` and the matching block
worker / the three matching per-kind workers); `runDenseScanWith` (state allocation `Array.replicate
… zero`; `sig` default `getD … dtype := .f64` used for `.shape` only; two `commitWrite zero …` calls);
`commitWrite` (`getD … zero`); `runDensePlan`'s `.scan` arm (`runDenseScan`, unchanged) and
`runDensePlan32`'s `.scan` arm (`runDenseScan32`); `rawPublicationSlots`' `.scan` arm (state
`destSlot`s, carrier-free); `runPreparedDense32 := runPreparedDenseOf runDensePlan32` and
`packBodyOf`/`unpackBodyOf`/`runPreparedDenseOf` (`{α} [StorageCarrier α]`); the JAX plan-level gate
in `Executable.lean` (`candidate.source.plan.storageKind == .float64`, unchanged); the legacy
evaluator's `rejectUnsupportedStorage` entry guards (`Eval/Scan.lean`) and `test/Eval/ScanTest.lean`
fixtures 11–13 (unchanged).

**Result: no cell disagrees with the plan's §4.** Two precision notes, neither changing a class:

1. Table B's "`getD … { dtype := .f64 }` totality defaults (shape-only)" row: not every such default
   is shape-only. In `compileScan`, `baseSigs`' initial `outerSigs.getD (slotOf.getD rn 0) { …
   .f64 }` flows its DTYPE into the block table, and in `Scan.lean` `checkCaptures`/`checkWrites`
   compare the defaulted dtype. Each default is unreachable — `slotOf[rn]?` is proven `some` just
   above in `compileScan`; each `Scan.lean` index is range-checked before its `getD`, directly or via
   membership in the block's outputs, which `checkPlanBlockCore` already range-checked — so the
   class stays **(c)**, but the row's "(shape-only)" qualifier is only exact for `resolveSource` and
   `runDenseScanWith`'s `sig`.
2. Table A's "f32 capture dtype" **(c)** cell: confirmed producer-less under `.float32`.
   `captureDtypeNotAdmitted` fires under `.float32` only for an `.f64` capture slot; any block table
   containing one either derives `.float64` or is mixed, and `checkPlanBlockCore`'s gate (or
   `deriveStorageKind`'s mixed error) rejects that block first, because `checkScanCore` checks both
   blocks before either capture check.

**Table A — case × door (re-derived; unchanged from the plan)**

| Case | Source (`compileScan`) | `checkPlan`/`checkScanPlan*`/`checkPlanBlock*` | Float workers | binary32 workers | Adapter | JAX | Legacy |
|---|---|---|---|---|---|---|---|
| f32 scan, identity bodies | **required** (C1) | **required** `checkScanPlanF32` (B1, A1; Q13) | **forbidden**, guard first (A3, B1; Q2, Q4) | **required** (A1, B1; Q1, Q3, Q14) | **required**, carrier-generic (C1) | forbidden, plan-level `.float64` gate, unchanged | forbidden permanently (fixture 13) |
| f32 scan, nonlinear body | **required**, `destDtype` ×4 (C2, C5–C7; Q15–Q18) | **required** `checkPointwiseF32`/`checkAxiswiseF32` (Q10, Q11) | forbidden | **required** (via `runDenseBlockWith`) | required | forbidden | forbidden |
| f32 scan-local scatter | **required**, no source change (C3) | **required**, carrier-free geometry | forbidden | **required**, state `+0` init pinned (C3; Q12) | required | forbidden | forbidden |
| predicate-only scan (bool-only blocks) in f32 program | **required** (C4) | **required**, bool-only exemption (A6, C4; Q8) | forbidden | **required** | required | forbidden | forbidden |
| f64 state/block in an f32 scan (programmatic) | unreachable from source | **forbidden**: `stateDtypeNotAdmitted` (A4), `baseBlockError (storageKindNotAdmitted .float64)` (A4b; Q7) | — | — | — | — | — |
| f32 capture dtype | — | **(c)**, producer-less under both kinds: the block gate always runs first | — | — | — | — | — |
| binary64 scans (preservation) | unchanged | **required**, stamps `.float64` (A2) | **required**, all binary64 suites unedited/green | **forbidden** (A3; Q1, Q3) | unchanged | unchanged | unchanged |
| snapshot / cross-state read | carrier-free | carrier-free | pinned by binary64 `ScanTest` | **SI**: shared generic code, no binary32 multi-state pin (§1.4) | — | — | — |

**Table B — a binary64 literal at a site binary32 now reaches (re-derived; unchanged from the plan,
see precision note 1)**

| Site | Reached by f32? | Class | Pin |
|---|---|---|---|
| `0.0` state init @ `runDenseScan` | yes | **fixed** → `zero` param | C3, Q12 |
| `0.0` `getD` default @ `commitWrite` | yes (unreachable arm) | **fixed** → `zero`; (c) | — |
| `runDenseBlock` calls ×2 @ `runDenseScan` | yes | **fixed** → `runBlock` param | A1, Q3 |
| `checkAssign`/`checkPointwise`/`checkAxiswise` @ `checkPlanBlock` | yes | **fixed** → select by kind | Q9–Q11 |
| `.ok .float64 => pure ()` gate @ `checkPlanBlock` | yes | **fixed** → `k == kind` or all-`bool` | A5, A6, C4, Q8 |
| `dtypeAdmitted` @ `checkScanPlan` state loop / `checkCaptures` | yes | **fixed** → `scanDtypeAdmitted kind` | A1, A4, Q6 |
| `checkPlanBlock` calls @ `checkScanPlan` | yes | **fixed** → by kind | A4b, Q7 |
| 4 × `dtype := .f64` nonlinear result slots @ `compileScan` | yes | **fixed** → `destDtype` | C2, C5–C7; Q15–Q18 |
| `getD … { dtype := .f64 }` totality defaults (shape-only) | yes | **(c)** | — |
| `opts.fill != 0` @ `checkScanScatterOpts` | yes | **required**, carrier-free (`+0` both) | C3 |

No (c) cell turned out reachable (plan §8).

### Mutation cycles Q15–Q18 (`mutation-manifest.sh --task 3`)

Run directly on `papers/f32c_mutations_post.json` (no scratch-manifest workaround needed: `--check`
validated all 18 entries, every old-string unique, now that the patch's final text exists).

| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| Q15 (base pointwise result slot back to .f64) | yes | yes | yes | PASS |
| Q16 (base axiswise result slot back to .f64) | yes | yes | yes | PASS |
| Q17 (step pointwise result slot back to .f64) | yes | yes | yes | PASS |
| Q18 (step axiswise result slot back to .f64) | yes | yes | yes | PASS |

4/4 cycles passed. Mutated-build failures (`ScanDense32Test` guards): Q15 → C5's base-relu guard,
Q16 → C7 (base softmax), Q17 → C2's relu guard AND Part D's `agrees (linProg (.pointwise .relu))
reluIn` (the Part D `agrees` guard also fails, since the worker leg's — `run32`'s — mutated behavior
is itself rejected/differs, not because the oracle caught a live value mismatch between two agreeing
legs), Q18 → C6 (step softmax). The earlier deferred cycles (Q5, Q8,
Q10–Q14) and G1/G2 are Task 3 phase 2's full re-run, not run here.

## Task 3 phase 2 — documentation sweep (close-out)

Tree: `worktree-f32c-scans-plan` at `c2fcec4` plus this phase's doc-only commit. Purely mechanical
per the plan's own framing: every edit a value-grep and a line replacement, no production code
touched (verified: `git diff --stat` against `c2fcec4` shows only `.md` files, `AGENTS.md`, and
docstring/comment-only `.lean` edits — no `#guard`, no executable code line changed).

### Step 1 — full manifest run, both manifests, 20/20 PASS

**`papers/f32c_mutations.json` (G1/G2 — binary64 preservation gate, final confirmation after Tasks
2–3):**

| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| G1 (scan signature tie dropped: runDenseScan accepts a stale/wrong signature table) | yes | yes | yes | PASS |
| G2 (block arity check dropped: runDenseBlock accepts a wrong-arity input array) | yes | yes | yes | PASS |

2/2 cycles passed.

**`papers/f32c_mutations_post.json` (Q1–Q18 — full re-run, no `--task` filter):**

| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| Q1 (runDenseScan32 storage-kind guard deleted) | yes | yes | yes | PASS |
| Q2 (runDenseScan storage-kind guard deleted) | yes | yes | yes | PASS |
| Q3 (runDenseBlock32 storage-kind guard deleted) | yes | yes | yes | PASS |
| Q4 (runDenseBlock storage-kind guard deleted) | yes | yes | yes | PASS |
| Q5 (checkScanCore stamps .float64 whatever the kind) | yes | yes | yes | PASS |
| Q6 (state admission ignores kind) | yes | yes | yes | PASS |
| Q7 (f32 scan checks its blocks as binary64) | yes | yes | yes | PASS |
| Q8 (bool-only block exemption dropped) | yes | yes | yes | PASS |
| Q9 (f32 block assignment checked as binary64) | yes | yes | yes | PASS |
| Q10 (f32 block pointwise checked as binary64) | yes | yes | yes | PASS |
| Q11 (f32 block axiswise checked as binary64) | yes | yes | yes | PASS |
| Q12 (binary32 state zero-init is +1, not +0) | yes | yes | yes | PASS |
| Q13 (checkPlan checks an f32 scan with the binary64 checker) | yes | yes | yes | PASS |
| Q14 (runDensePlan32 scan arm refuses again) | yes | yes | yes | PASS |
| Q15 (base pointwise result slot back to .f64) | yes | yes | yes | PASS |
| Q16 (base axiswise result slot back to .f64) | yes | yes | yes | PASS |
| Q17 (step pointwise result slot back to .f64) | yes | yes | yes | PASS |
| Q18 (step axiswise result slot back to .f64) | yes | yes | yes | PASS |

18/18 cycles passed. **Total 20/20.** Q5, Q8, Q10–Q14 — the cycles deferred in Tasks 1–2 specifically
because their `expect` line numbers only exist once the full `ScanDense32Test.lean` (Parts A–D)
exists — are the real, first-time verification point for those entries; all passed with no
work-around needed.

### Step 2 — `Plan/AGENTS.md`

Code Map: `Block.lean` and `Scan.lean` rows extended with their checker/worker-core pairing
(`checkPlanBlock`/`checkPlanBlockF32` over `checkPlanBlockCore kind`; `runDenseBlock`/
`runDenseBlock32` over `runDenseBlockWith`; the `Scan.lean` mirrors). Contracts' "Current binary32
boundary" bullet rewritten: no step kind is refused by capability any more; points at
`f32c_evalplan.md` §1.2 for what remains refused by policy/backend, and names `ScanDense32Test` Part
D (`oracle32`) as the scan oracle. Pitfalls' "A (c) cell is a guard dependency" sentence named
`runDenseBlock`/`runDenseScan` as Float-only examples, which is now false for that pair specifically
(carrier-parametric since Task 1); replaced with a still-true example found in the file:
`captureDtypeNotAdmitted` under `.float32`, confirmed producer-less by this slice's own §4
re-derivation (precision note 2, above). Two more stale AGENTS.md lines were caught only by Step 3's
own sweep of this same file and fixed alongside: the `Dense32.lean` row ("`.scan` refused as
`storageKindMismatch`") and the `Compile.lean` row ("Step 0c `f32CapabilityCheck` capability pass",
with no mention it is deleted).

### Step 3 — value-grep sweep, every document

All six greps re-run after every fix, from the worktree root:

```bash
rg -n "F32-C" leanncd papers --glob '!papers/f32c_*' --glob '!papers/f32d_*' --glob '!papers/f32b_*'
rg -n "f32 scan" leanncd/LeanNCD leanncd/test papers --glob '!papers/f32c_*'
rg -n "f32UnsupportedStep [0-9a-z]+ \.scan|scan[^\n]*storageKindMismatch \.float32 \.float64" leanncd papers --glob '!papers/f32c_*'
rg -n "checkScanPlan[^\n]*Float-backed|Float-backed[^\n]*checkScanPlan|runDenseScan[^3W][^\n]*Float-only|runDenseBlock[^3W][^\n]*Float-only" leanncd papers --glob '!papers/f32c_*'
rg -n "f32CapabilityCheck" leanncd papers --glob '!papers/f32c_*'
rg -n "scan is F32-C|scan.*still unadmitted|scan evidence is refused" leanncd/LeanNCD leanncd/test
```

Hit counts (final, post-fix): 17 / 16 / 6 / 5 / 12 / 0 lines respectively. Every leanncd (live-code)
hit was read in context and is one of:

- **accurate, current-state prose** this slice itself wrote (e.g. `EvalPlan.lean`'s and `Error.lean`'s
  `f32UnsupportedStep` docstrings, `AGENTS.md`'s rewritten Contracts bullet, `Dense32.lean`'s own
  module doc, `GraphCheckTest.lean`'s F32-C acceptance comments, `CompileTest.lean`'s re-pointed
  fixture prose) — these say "admitted since F32-C" / "deleted" / "no longer", not "still rejected";
- the **explicitly allowed, unedited** cases: the legacy evaluator's own files (`Eval/Scan.lean`,
  `test/Eval/ScanTest.lean` fixture 13), and the new producer-less `"{name}: f32 scan"` mention in
  `Error.lean`;
- **two real stale hits found and fixed** beyond the six carried-forward findings (not pre-enumerated
  by Task 3 phase 1 or the brief, caught only by this sweep):
  1. `leanncd/test/Eval/Plan/ScanTest.lean`'s fixture-10 docstring claimed "every binary32 scan form
     is slice F32-C, so there is no f32 scan worker" — false now; reworded to state `checkScanPlan`
     stays deliberately Float-backed beside its new sibling `checkScanPlanF32`, matching
     `checkAssign`/`checkPointwise`/`checkAxiswise`'s own pattern. The fixture's actual `#guard`
     (checkScanPlan still rejects an all-f32 table) is unchanged and still true.
  2. `leanncd/test/Eval/Plan/ScatterCheckTest.lean`'s fixture-9 docstring said block/scan checkers
     "stay Float-backed because they have no binary32 worker — F32-C", which no longer generalizes
     now that `checkPlanBlockF32`/`checkScanPlanF32` exist; reworded to say every local/graph checker
     now has a binary32 sibling, `checkScatterF32` included.
  3. `papers/wave_f_capability_manifest.md`'s dtypes bullet asserted "`f32` is still rejected
     outright in a scan" immediately above a sentence (already edited into this same bullet) saying
     the opposite — a self-contradiction the plan's enumerated edit alone would have introduced;
     rewritten so the whole bullet reads consistently: `checkScanPlan`'s binary64-only kernel never
     changed, but an f32 schedule no longer routes through it at all, admitted instead via
     `checkScanPlanF32`/`runDenseScan32` since F32-C.
- All historical/plan-authoring prose in `f32_evalplan.md` (§1.3/§1.4 outside the two edited items,
  and the dated-"COMPLETED 2026-09-21" §3.5 sibling-audit table), `f32_evalplan_handoff.md`, and every
  `f32b_evalplan.md`/`f32d_evalplan.md`/`f32d_*` hit, is a historical close-out or already-merged
  slice's own planning record describing a past boundary — left unrewritten per the brief's own rule
  (append a dated note, never rewrite history); none of them was asked for by this phase's Step 4,
  and none asserts anything false about the CURRENT tree.

Final re-run (post-fix) of all six greps: **no hit beyond the allowed/accurate set above.**

### Step 4 — papers

- `f32_evalplan.md`: §1.3 item 2 and §1.4 item 3 both got "**Landed by `f32c_evalplan.md`.**"; the
  "largest risk surface… expect it to split into two slices" sentence got "It did not need to — one
  slice, three tasks (see `f32c_evalplan.md` §1.5)."
- `f32d_evalplan.md`: §1.3's "Where the two slices DO connect" paragraph got "**Settled by
  `f32c_evalplan.md` §1.3: moot**…"; the harness-lift sentence got "The lift did not happen — see
  `f32c_evalplan.md` §1.3."
- `backend_missing_functionality.md`: the "Binary32 beyond the assignment fragment" table row and
  rationale item 4 rewritten to "now fully closed" (F32-B + F32-D + F32-C); the "Deliberately still
  rejected" bullet under "Already closed" no longer lists scan; the "(mixed storage, f32 scan)"
  mention annotated "closed by F32-C"; a new "Update (F32-C shipped…)" paragraph added mirroring the
  existing F32-B one. The 10/16/6 split was **re-derived, not assumed**: `unsupportedDtype` was
  already counted as one live FAMILY (not per producer-site), and Step 0b's mixed-storage throw keeps
  that family live after F32-C removes its scan producer — **confirmed unchanged at 10/16/6.**
- `wave_f_capability_manifest.md`: the "still refused outright … (F32-C, still deferred)" sentence →
  "admitted natively since F32-C"; the Binary32 row's "Nothing on THIS page… is binary32" sentence
  rewritten to state scan is now admitted (`checkScanPlanF32`/`runDenseScan32`, independent oracle);
  the "Only binary32 scan …, F32-C" clause now lists scan among the admitted, not the still-open.
  (Also fixed per Step 3: the dtypes bullet's internal contradiction, see above.)
- `eval_ir.md`: the Step 0c description now states it is DELETED since F32-C, with assign/pointwise/
  axiswise/scatter (F32-D) and now scan (F32-C) all admitted, leaving nothing for it to reject.

### Step 5 — counts (before/after)

Before-slice baselines (measured on the pre-Task-1 tree, commit `19ea6ba`, where the plan was
authored — re-measured now, not assumed from the plan text):

```bash
rg -c 'unsupportedDtype s!"{nm}: f32 scan"' leanncd/LeanNCD/Eval/Plan/Compile.lean    # 2
rg -c 'f32UnsupportedStep' leanncd/LeanNCD/Eval/Plan/EvalPlan.lean                     # 3
rg -c '\.scan _ => throw (\.storageKindMismatch \.float32 \.float64)' \
  leanncd/LeanNCD/Eval/Plan/Dense32.lean                                               # 1
```

After-slice (measured now, on the full post-Task-3/phase-2 tree):

```bash
rg -c 'unsupportedDtype s!"\{nm\}: f32 scan"' leanncd/LeanNCD/Eval/Plan/Compile.lean   # 0
rg -c 'f32UnsupportedStep' leanncd/LeanNCD/Eval/Plan/EvalPlan.lean                      # 3
rg -c '\.scan _ => throw \(\.storageKindMismatch \.float32 \.float64\)' \
  leanncd/LeanNCD/Eval/Plan/Dense32.lean                                                # 0
```

| Site | Before | After | Matches plan? |
|---|---|---|---|
| `Compile.lean` f32-scan `unsupportedDtype` throw sites | 2 | 0 | yes — "both deleted" |
| `Dense32.lean` `.scan` `storageKindMismatch` arm | 1 | 0 | yes — "→0" |
| `EvalPlan.lean` `f32UnsupportedStep` text occurrences | 3 | 3 | **no — plan said "→2"** |

**Discrepancy, reported not forced to match:** the plan predicted the `EvalPlan.lean` grep would drop
from 3 to 2 once "the throw site" was removed. That throw site (`| .scan _ => throw
(.f32UnsupportedStep ni .scan)` in `checkPlan`) WAS removed — but in Task 2 (`85b0114`), not Task 3;
`git diff 85b0114 c2fcec4 -- leanncd/LeanNCD/Eval/Plan/EvalPlan.lean` is empty, so Task 3/phase 2 made
no change to this file at all. The baseline count of 3 (decl + one docstring line + the throw site)
dropped to 2 when the throw site was deleted, but Task 2 *also* added a second docstring line
("Since F32-C, `.scan` joins them: `f32UnsupportedStep` has no live producer at all.") containing the
same substring, bringing the raw text-occurrence count back up to 3 net. The three live occurrences
today are: the constructor declaration (line 142) and two docstring sentences (lines 145, 148) — zero
throw sites. This is a textual-count artifact of an accurate, intentional doc addition, not a missed
deletion or a build-correctness issue; `rg -n 'throw.*f32UnsupportedStep' leanncd/LeanNCD/Eval/Plan/EvalPlan.lean`
returns no hits, confirming zero live throw sites either way.

### Step 6 — final numbers

- **Manifest total: 20/20 PASS** (2 G-cycles + 18 Q-cycles; tables above).
- **Grep sweep: clean** — six greps re-run post-fix, every hit triaged, no stale claim remains (Step
  3 above).
- **Final whole-project build:** `bash leanncd/scripts/lake-build.sh leanncd` →
  `Build completed successfully (8673 jobs)` — identical job count to Task 3 phase 1's own build
  (doc-only changes add no modules).
- **Carried-forward findings from earlier task reviews:** all three addressed —
  1. `Block.lean`'s `BlockError.storageKindNotAdmitted` docstring and `checkPlanBlockCore`'s
     docstring both rewritten to state the actual kind-mismatch gate (with the bool-only exemption),
     not "only `.float64` admitted"/"a `.float32` table is unconditionally rejected".
  2. `Error.lean`'s `PlanStepKind` docstring: `.scan` added to the list of kinds that are
     "deliberately NOT producers of `f32UnsupportedStep`", with "scan since F32-C" appended.
  3. `ScanDense32Test.lean`'s module header and `oracle32`'s docstring reworded to drop "PROTOTYPE"/
     "Oracle prototype" framing, **without changing the file's line count** (confirmed: still 270
     lines; spot-checked that every mutation-manifest `expect` line number — 66, 68, 81, 82, 89, 97,
     98, 218, 219, 221, 224, 253, 256, 258, 267, 268 — still contains the text the manifest expects).
     `papers/f32c_record.md`'s own Q17 note reworded to attribute the Part D failure to the WORKER
     leg (`run32`) breaking under the mutation, not to the oracle detecting a live mismatch.

## Final whole-branch review fix wave (commits `1b701c9`, `0cfb90a`)

The final two-lens review (lens a: storage-kind guard/evidence boundary soundness) constructed and
built a probe program disproving §6 decision 1's own rationale: a bool-only outer table (predicates
only) with a scan whose step block writes real-dtype scan-local scratch was wrongly routed to the
`invalidPlan` compiler-bug channel, because `checkPlan`'s graph-level storage-kind derivation (from
`raw.tensorSigs`) cannot see scan-local scratch and defaulted to `.float64`, while `prepareEvalPlan`'s
own Step 0b (which counts scan scratch) had already derived `.float32` for the same schedule.

**Fix** (`EvalPlan.lean`): when the outer table is bool-only, `checkPlan` now falls back to the first
real dtype found in any scan step's `baseBlock`/`stepBlock` tensorSigs (reusing the pre-existing
`storageConstraintOfDtype` helper), generalizing the same bool-only exemption Task 1 already applies
at the block level, one level up. A real outer slot stays authoritative — the fallback only fires when
`raw.tensorSigs.all (·.dtype == .bool)` — so genuine f32/f64 mixing is still refused exactly as before
(`mixedStorageKinds`, F32-E's scope, unaffected).

**New coverage:** `ScanDense32Test.lean` Part E (E1: the scratch-only f32 program now admitted,
`storageKind == .float32`, bits `0x3F800000`×3; E2: the f64 scratch sibling stays `.float64`, proving
the kind tracks the scratch's real dtype, not "bool-only ⇒ auto-f32"; E3a–d: four negative controls —
visible f32+f64 mixing still `mixedStorageKinds`; a real outer slot stays authoritative over a
disagreeing block; block search order (base before step); source-level Step 0b still catches a
genuinely mixed schedule). Three new mutation cycles Q19–Q21 in `papers/f32c_mutations_post.json`
(fallback deleted; fallback overriding a real outer table; fallback ignoring block content) — all
independently verified by the scoped re-review to mutate the actual fix code in the claimed way.

**Plan correction:** `papers/f32c_evalplan.md` §5 Task 3 phase 1 Step 5 and §6 item 1 both carry dated
(2026-09-30) append-only corrections — the original wrong rationale is kept, not rewritten.

**Docs fixed in the same fix wave (final-review Minors 2–4):** `Scan.lean`'s `checkCaptures`/
`CheckedScanPlan`/`checkWrites` docstrings and the `checkScanCore` state-loop comment now describe
both the `.float64` and `.float32` doors (previously binary64-only text, a plan-level miss from Task
1 Step 4); `backend_missing_functionality.md`'s stale F32-B-row claim and re-derivation date fixed;
`GraphCheckTest.lean` fixture 16's docstring now explains its two `isF32Unsupported` guards are
vacuous/historical (kept, not deleted, per closed-family-discipline precedent) now that
`f32UnsupportedStep` has no producer. One additional stale docstring found and fixed during this wave:
`Dense32.lean`'s `runDensePlan32` doc, made stale by the Finding-1 fix itself.

**Final manifest total: 23/23 PASS** — `f32c_mutations.json` 2/2 (G1/G2, re-run clean, binary64
preservation unaffected by the graph-level fix) + `f32c_mutations_post.json` 21/21 (the original 18 +
new Q19–Q21), both with no `--task` filter. Final build: `Build completed successfully (8673 jobs)`,
unchanged (doc/logic additions here add no new module).

**Scoped re-review verdict:** all four fix-wave findings ADDRESSED, no new Critical/Important
breakage — independently confirmed the foundational `checkPlan` change cannot reclassify any
pre-existing admitted binary64 program (every such program's first real block slot was already f64 or
absent, by construction of what the old block gate used to admit) and cannot affect any outer table
that already carries a real slot (the fallback is syntactically gated to the bool-only case only).
Three out-of-scope Minor observations parked, not blocking: `f32c_record.md`'s own stale 20/20 count
(this section fixes it); `Scan.lean:476`'s causality docstring names only the binary64 door (accurate
in substance, incomplete in naming); `Compile.lean`'s Step E comment says a compiled scan "meets
`checkScanPlan`" without naming the f32 sibling for f32 graphs (same class of minor doc incompleteness
as Finding 2, not re-opened here).

## Rule 6 token accounting (measured, `token-report.py 3e15be7b-6194-4fb4-acbf-4f8d8e11d1c9`)

**Slice execution total: 98.4M ctx** — well under the ~175M slice-execution budget (CLAUDE.md Rule 6),
despite two per-dispatch overruns surfaced honestly rather than silently absorbed:

- Task 3 phase 2's implementer dispatch ran 154 turns / 27.2M ctx (peak 280k), well past the ~60-turn
  / ~250k-peak per-dispatch guideline — it combined a full 20-cycle manifest re-run, a six-pattern doc
  grep across the whole repo, four paper edits, and three carried-forward findings in one dispatch.
  In hindsight this should have been split per `slice-plan` §5/§6 rather than batched; flagged in the
  SDD ledger at the time, not discovered only at close-out.
- The final-review fix wave's recovery dispatch ("Complete stalled F32-C fix verification") ran 75
  turns / 8.1M ctx after a prior dispatch ("Fix F32-C final review findings", 42 turns, within budget)
  stalled on an infrastructure failure (600s watchdog) mid-build, not a token/turn issue — the recovery
  dispatch's extra turns were spent re-verifying a prior agent's uncommitted work before building on it,
  not re-doing design work.
- Every other dispatch (implementers, task reviewers, the final whole-branch reviewer, the fix-wave
  re-review) stayed within or close to the ~60-turn / ~250k-peak guideline.

Per-dispatch ledger (turns / ctx / peak), from the measured report: Task 1 implement 45t/3.7M/106k +
4t/0.2M/51k (resumed after the mutation-manifest ruling); Task 1 review 6t/0.4M/90k; Task 2 implement
42t/3.7M/126k; Task 2 review 17t/1.4M/107k; Task 2 fix re-review 4t/0.1M/41k; Task 3 phase 1 implement
70t/8.0M/172k; Task 3 phase 1 review 10t/0.8M/103k; Task 3 phase 2 implement 154t/27.2M/280k; Task 3
phase 2 review 19t/1.8M/116k; final whole-branch review 36t/5.1M/207k; fix-wave attempt 42t/4.6M/159k
(stalled); fix-wave recovery 75t/8.1M/161k; fix-wave re-review 21t/1.9M/109k; controller (this session)
152t/31.3M/341k.
