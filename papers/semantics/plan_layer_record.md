# Part V Plan layer, slice 1: record

Record, not the live plan (`plan_layer_plan.md`). Authoring facts below; the close-out section is
filled by the controller at the end of execution.

## Authoring dispatches

Tool-use counts are harness counts (CHECKPOINT §7: self-reports ran about 20 percent low).

| phase | output | harness tool uses |
|---|---|---:|
| A1 prototype | `Syntax`, `Batch`, `Memory`; `a1_notes.md` | 102 |
| A2 prototype | `Step`, `Simulation`; `a2_notes.md` | 147 |
| A3a prototype (finish) | `Validity`, `Run`; `a3a_notes.md` | 64 |
| A3b prototype | `Correctness`, comparison fixtures; `a3b_notes.md` | 78 |
| patch emission | `plan_layer_patches/0{1..5}-*.patch`, `manifest.json`, `evidence.json`, `emit-patches.py` | 44 |
| Phase B write-up | `plan_layer_plan.md`, `plan_layer_mutations_post.json`, this file | about 59 (own count at commit) |

## Authoring facts (measured)

- Patch base `0bf02e47`; scratch replay head `f14415ed`, tree `f3eee99e` (evidence.json). Replay:
  applying the five patches to the base gives the prototype tree on all 19 shipped paths.
- Per-task emission builds (evidence.json): T1 2960 jobs, T2 2961, T3 2963, T4 2966, T5 (default
  targets) 8784; all "Build completed successfully". Forbidden-token grep: 18 files, 0 hits.
- Patch sizes (lines): 429, 293, 786, 551, 830.
- Fixture count (scratch tree, counted): 50 `#eval check` rows + 46 top-level `example`/`theorem` = 96.
- Mutation manifest: 20 cycles (T1 2, T2 4, T3 5, T4 8, T5 1); 3 equivalent (A2-b, A2-e, A3a-a).
  `mutation-manifest.sh --check` against the scratch tree: "manifest OK: 20 entries, 20 selected,
  every old-string unique". The full manifest was NOT run at authoring. (Later run on the shipped
  tree, commit `5f1101d0`: 20/20; only the A1-d and A2-d `expect` strings changed; see plan §7 and
  `plan_layer_artifacts/manifest_run.md`.)
- Cycles whose `new` text or `expect` is not verbatim from the notes (to be confirmed by the
  controller's full run):
  - A1-a: mutant is last-writer-wins (`fun _ x`), not the recorded `if dest = p` form; location
    `Batch.lean` line 80 col 19 inferred from A1-b (the recorded line 84 came from a 5-line mutant).
  - A1-c: location moved from the recorded line 30 / 242 to 28 / 240 (recorded mutant was 3 lines;
    this one is 1 line); text reconstructed.
  - A1-d: `expect` keeps only "split_ifs failed" (recorded locations depend on the mutant's shape).
  - A2-d: `expect` "plan.Mat 2 (addr 0)" is the notes' description of the `decide` failure; the
    exact Lean wording is unconfirmed.
  - A2-e: `execAccSeq` body reconstructed (fold with per-member scan and commit).
  - A3b-2: field rename instead of field drop (manifest takes one site per entry).
  - All other cycles: `new` follows the notes' literal mutant text; `expect` locations were checked
    against the shipped files (each cited line holds the declaration the notes name).

## Close-out (controller fills in)

- Execution worktree / branch:
- Base `main` SHA at execution:
- Per-task commits (T1..T5) and build results:
- Docs-sweep commit:
- Full default build: jobs, `error` lines, forbidden-token grep:
- Mutation manifest full run (`--out` table path, PASS count, any `expect` corrected from the log):
- Whole-branch review, soundness lens (findings file, adjudication):
- Whole-branch review, spec-Lean fidelity lens (findings file, adjudication):
- Fix dispatches (one per finding group):
- Open items resolved / parked (plan §10):
- Token total (`token-report.py`), against CLAUDE.md Rule 6 (≤ ~175M execution):
- Merge SHA on local `main`; branches and worktrees removed; push status (not pushed):

## Review round 1

Two lenses, files `plan_layer_artifacts/review_fidelity.md` (F1..F13) and
`plan_layer_artifacts/review_soundness.md` (F-1..F-6). Section 8 and spec-restatement findings go to
the section 8 fix dispatch; the others were applied to plan sections 1-7, 9, 10 after checking the
claim against the shipped Lean and plan. No finding was rejected.

| ID | lens | severity | disposition |
|---|---|---|---|
| F1 | fidelity | Important | section 8 fix dispatch |
| F2 | fidelity | Important | section 8 fix dispatch |
| F3 | fidelity | Important | section 8 fix dispatch |
| F4 | fidelity | Important | section 8 fix dispatch |
| F5 | fidelity | Minor | section 8 fix dispatch |
| F6 | fidelity | Minor | applied to plan §1 (theorems are sort-generic over `K : S → Type`; only fixtures and profile use one sort); path doc 4.9 wording: section 8 fix dispatch |
| F7 | fidelity | Important | section 8 fix dispatch |
| F8 | fidelity | Minor | section 8 fix dispatch |
| F9 | fidelity | Minor | section 8 fix dispatch |
| F10 | fidelity | Minor | section 8 fix dispatch |
| F11 | fidelity | Important | section 8 fix dispatch |
| F12 | fidelity | Minor | section 8 fix dispatch |
| F13 | fidelity | Minor | section 8 fix dispatch |
| F-1 | soundness | Minor | applied: A2-e equivalence qualified to valid plans (N5, §5.2); reviewer-computed distinguishing plans in §10 item 10, marked not built or verified; A2-b and A3a-a confirmed for all plans |
| F-2 | soundness | Important | section 8 fix dispatch |
| F-3 | soundness | Minor | applied to D9, N6, §5.1 (`accFlat_complete` substantive, `cov1_of_cov2_pubOrder` Valid-level corollary); spec §8.1 citation: section 8 fix dispatch |
| F-4 | soundness | Minor | applied: `execAcc` within-group duplicate and `stepCommand` empty command now OPEN rows; §5 tallies and §10 item 3 parked cost updated; Nodup-pair equivalence and `checkInit` half noted |
| F-5 | soundness | Minor | applied to §3.1 (branch and clean-status gates, Co-Authored-By trailer) |
| F-6 | soundness | Minor | applied to §3.1 and §9.5 (tag `plan-layer-slice1-proto` kept before `branch -D`; review files and `manifest_run.md` in the landing set; Rule 13 scope; scratch worktree removal) |

Tool uses (harness counts): fidelity review 50 (self-reported ~34), soundness review 49
(self-reported ~37), manifest validation 43, Phase B authoring 61, patch emission 44.
Fix dispatches (harness counts): group P (plan body) 47 (self-reported 29, cap 45: breached), group S
(section 8 and spec restatement draft) 66 (self-reported ~41, cap 45: breached). Reconciled by the
controller afterwards: D5 row corrected, decision N9 added to plan section 2 (one-step simulation
proved for `Conf = refState pc` only), `D-sweep-1` renamed to N9. Briefs gave 35 as the aim; both
dispatches ran about 1.4-1.9x over the harness count, so budget fix dispatches at ~25 self-reported.
