# Task B2 report — Axis B, part 2: the `strided` row kind across the write-geometry surface

**Status: DONE_WITH_CONCERNS.** All five deliverables complete. The concerns are substantive
findings, not incomplete work — see §6.

- **Base:** `9680b92` (worktree `worktree-pre-scatter-audit`).
- **Build:** green, **8660 jobs**, `cd leanncd && "$HOME/.elan/bin/lake" build` → `Build completed
  successfully (8660 jobs).` Run after all spike work; no production code was changed, so this is the
  unchanged baseline confirmed rather than a new number.
- **Production diff:** empty. `git diff HEAD --stat -- leanncd/LeanNCD leanncd/lakefile.toml
  leanncd/test` → no output. **No `strided` constructor exists in any committed file.**
- **Deliverable:** appended to `.superpowers/sdd/2026-09-06-pre-scatter-backend-audit/axis-b-fragment.md`
  as §B2.1–§B2.8, plus the three in-place census/summary updates §B1.2 named. Exactly one append
  marker, still the last line.
- **Not touched:** `axis-a-fragment.md`, `papers/pre_scatter_backend_audit.md`, `lakefile.toml`, any
  test, any documentation site.

---

## 1. What was produced

### The table (deliverable 1)

Four rows appended as R13–R16 across all 14 existing columns — `strided @ {adv, non-adv} @ {base,
step}` — with no change to any column header, to any of B1's twelve rows, or to B1's legend. One
B2-local mark (`★`) is declared in §B2.2 as a **row-label** mark, not a cell mark, so it contributes
nothing to the census; it flags that R13/R14's marks are the marks under §B2.1's decision A.

**Census, mechanically recounted from the committed table** (a script parsed every `| R<n> |` row,
stripped `**`/`‡`/`§`, and tallied):

| Scope | cells | a | b | c | — | ▷ |
|---|---|---|---|---|---|---|
| B1's R1–R12 | 168 | 24 | 16 | 86 | 18 | 24 |
| **B2's R13–R16** | **56** | **0** | **6** | **36** | **6** | **8** |
| **Whole table** | **224** | **24** | **22** | **122** | **24** | **32** |

Per row: R13 and R14 are 11 c / 1 — / 2 ▷; R15 and R16 are 7 c / 3 b / 2 — / 2 ▷. The three
locations §B1.2 named were updated to these figures: §B1.2's census line, §B1.3's group list, and
§B1.5's gate summary (which sits *before* the marker; editing it in place is what §B1.2 said to do).

**Reported divergence.** The brief predicted ~27 adjudicable cells; 36 came out — a 33% overshoot,
far milder than B1's 86-against-40. The mechanism is B1's own and says nothing new about the code:
the five non-validating / dimension-class-blind columns contribute 20 of the 36 by construction.
Excluding them leaves **16**, i.e. *below* the estimate.

### Adjudication (deliverable 2)

All 36 new `c` cells adjudicated across **14 groups, G17–G30** — 7 closed / 20 cells, 7 open / 16
cells, the open ones collapsing to a single finding **B2-F1**. Combined with B1: **31 groups / 122
`c` cells, 16 closed / 91 cells, 15 open / 31 cells**, three findings (B1-F2 10, B1-F4 5, B2-F1 16).

Every closure quotes a clause and names a catcher that **fires in the cell's own phase** — the G16
failure that cost B1 a fix round. Concretely: the four step-phase groups whose catcher is
`stepWriteRowsOk` (G18, G21, G23, G28) are closed, because that predicate runs at step and
`checkWrites` throws `writeGeometryNotAdmitted` before ever reaching the value predicates; the two
base-phase value-predicate groups (**G22** on `freeExtentsAgree`, **G24** on `pinnedLiteralsInRange`)
are **open**, for exactly the reason G16 was reopened — at base there is no catcher and no context
shape to appeal to. No write-path cell is closed as backstopped by `gatherFactor`'s `inBoundsPerDim`;
no cell is softened to "unlikely" or "defensive".

### Extent-rule tie (deliverable 3)

§B2.4 maps each of `outExtent`'s five arms to a checked-plan row kind and states which arm each
strided cell is the image of. `LHSSlot.outIdx` is total over five `LHSSlot` constructors and
`IdxExpr` has exactly five constructors, so the five arms are exhaustive over `outExtent`'s own
input (both inductives counted, not assumed). Measured at `size(i) = 4`, all six forms in one probe:
`(some 4, some 6, some 5, some 7, some 8, some 11)`.

Result: `.axis` is `.free`'s image, `.const` is `.pinned`'s, `.shift a 1` is `.advancing`'s, and the
three remaining forms — `.shift a c` (c≠1), `.scale c a`, `.affine c0 [(c,a)]` — are exactly the
strided kind's, selected by its `(scale, offset)` payload. A two-axis `.affine` has an extent
(`some 7`) but **no** row image (B2-F6).

On call-versus-copy: the site **could call** the shared formula — every S21 probe compiled under
`import LeanNCD.Eval.Plan.Scan` alone, and `Scan.lean` reaches `DSL.Ast` transitively via
`Block → Dense → Check → Error → Kernel`. The obstruction is the argument vocabulary (an `LHSSlot`
plus a UID lookup, in a positional UID-free IR), and a synthetic-`AxisSpec` adapter closes it
exactly, measured at `(some 6, some 6, some 9)`.

### B1-F9 and B1-F10 (deliverable 4) — both answered

See §3 and §4 below.

### Barrier accounting (deliverable 5)

§B2.7. Barrier 2 re-read and confirmed verbatim (the base loop's two emittable row shapes and its
`| .iterNext _ | .affine _ =>` throw; the step loop's differently-shaped `| .iterAt .. | .affine _ =>`).
A **third** barrier exists for the strided case that B1's case does not have — `checkScanLHSSlot`'s
preflight `.affine => scatterOrAffineLhs`, called barrier 0. This does **not** correct B1: `.iterNext`
and `.iterAt` are both *admitted* at preflight, so barrier 0 is genuinely irrelevant to B1-F2.

**What barrier 1 alone covers, and does not:** barrier 1's whole force is making a `p < contextWidth`
test unsatisfiable. It therefore covers exactly the `.advancing` kind — the only current branch with
that guard. Under decision A the strided branch's guard is `p ≥ contextWidth`, the **opposite
polarity**, satisfied by every `p` at `contextWidth = 0`. So barrier 1 is not a weakened defence for
B2-F1; it is **no defence at all**. After the Scatter slice lands: `.advancing` stays latent behind
barrier 1 alone (B1-F2, 10 cells), `.free`-at-an-advancing-dim stays live-and-safe (B1-F4, 5 cells),
and strided becomes live and unsafe behind nothing (B2-F1, 16 cells).

---

## 2. Fact 2: the decision, recorded

The brief made this my call rather than a fact to inherit. **Decision A adopted:** the strided branch
carries the domain-partition guard `p ≥ contextWidth` — the guard `.free` already carries — and **no
phase gate**, ordered after the advancing branch. **Consequence: the base cell is LIVE, not latent**,
and this is the write-geometry defect family's sixth instance.

Reasons, in §B2.1: the feature wants base strided writes (there are two `.affine` arms to lower, not
one); a phase gate would buy latency by resting a third row kind on barrier 1's unenforced value; the
`p ≥ contextWidth` guard is required regardless, because the minimal payload names an *output-slice*
position; and the branch's placement after the advancing branch is load-bearing, since coefficient 1
with bias 1 is `.advancing` in the context half.

**The assumption is named and labelled as an assumption, not a measurement.** Decision A assumes
affine LHS writes are wanted in **base** blocks and not only step blocks. That is a scope assumption
about the feature, not derivable from `9680b92` — the base `.affine` arm being *present and throwing*
shows the slot is reachable enough to need an arm, not that the feature intends to lower it. **If the
Scatter slice decides affine LHS is step-only, decision B is correct** and every `★` row becomes
latent; §B2.3 gives decision B's reading for each group that differs, so the answer is tested either
way rather than assumed either way.

**The construction was built both ways**, as required:

```
rows for dp[0, 2·oc₀, oc₀] at base width 0
  decision A:  #[some (pinned 0), some (strided 0 2 0), some (free 0)]
  decision B:  #[some (pinned 0), none,                 some (free 0)]
  baseWriteRowsOk #[0] 1 (A) = true      -- LIVE
  baseWriteRowsOk #[0] 1 (B) = false     -- LATENT (clause 1)
```

### On the throwaway constructor

The brief permitted a throwaway spike with a real constructor. I used one:
`leanncd/spikes/AxisBStridedModelThrowaway.lean` declared a four-constructor `WRK` inductive and then
copied `baseWriteRowsOk`, `stepWriteRowsOk`, `freeExtentsAgree`, `pinnedLiteralsInRange` and
`writesCollide` **verbatim** from `Scan.lean` with no strided arm added, so a genuinely new
constructor could be run through the current predicate text. **It was deleted before committing and
was not copied into `axis-b-spikes/`.** Its output is reproduced inline in the fragment under a new
tag, `[snippet, model]`, declared at the top of §B2 and explicitly described as weaker than
`[snippet]`: it measures a faithful copy, not the shipped function. **Every `[snippet, model]` claim
in the fragment is paired with a `[snippet]` measurement of the real clause it models** — usually the
same predicate at the same parameters with `.pinned`/`.advancing` standing in, which is sound because
the arms in question (`| _ => none`, `| _ => true`, `| _, _ => false`) are constructor-blind by their
own text, quoted at each site.

---

## 3. B1-F9 answered: **not** rejected on the scatter path

Both `outExtent` callers measured; the answer splits, and the reachable case is not the one B1
measured.

**Caller 1 — `Eval.scatterOutShape` → `evalScatter`: no rejection anywhere.** All four negative forms
give `.ok` with a shape-`[0]` tensor and an **empty** data array; every write is silently dropped by
`evalScatter`'s bounds guard (`0 ≤ z && z < d` is false at every coordinate when `d = 0`), the same
rule that exists for genuine overspill. The collision policy cannot fire either, because
`.rejectCollisions` is reached only *inside* that guard. The two gates that do still fire
(non-identity nonlin, unsized source axis) are both ordered before the shape is consulted.

**Caller 2 — `SizeInfer.scatterOutputShapes` → the sizing fixpoint: rejected, but only if read.**
`scatterOutputShapes` publishes `some [0]`; when a downstream statement reads it, `inferAxisSizes`
fails loud as `SolveFailureKind.nonPositive` with correct remediation text. **But the diagnostic
blames the reader** — `uid 2` is the downstream axis `k`, and the source list names
`Out[axis k] (scatter-out)`. The zero-coefficient slot that produced the extent is one statement away
and unmentioned.

**The genuinely live case is a ZERO coefficient, reachable from plain surface syntax.**
`DSL/Elab.lean`'s `elabTLLHSSlot` builds every affine LHS coefficient and offset as
`Int.ofNat n.getNat` from a `num` literal, so **none of B1's four negative forms is surface-reachable**
— they need a programmatic `Stmt`. A zero coefficient is different. Measured end-to-end through
`tlprog!{ … }` / `TLProgram.eval`:

```
Out[0*i] := X[i]     with axis i : ℕ = 4   ->  eval .ok; Out shape = [0], data = #[]
Out[0*i + 0] := X[i]                        ->  eval .ok; Out shape = [0], data = #[]
Out[2*i] := X[i]           (CONTROL)        ->  eval .ok; Out shape = [8], data = #[1,0,2,0,3,0,4,0]
Out[0*i] then Y[k] := Out[k]                ->  eval FAILED: affine size system non-positive (uid 2)
```

So four words of ordinary surface syntax compile, evaluate `.ok`, and return an empty `Out` with all
four writes dropped and no diagnostic — **live at `9680b92`**.

**Cell status:** `c`, **not closed**. The catcher fires in only one of two consumer paths and never in
`evalScatter` itself — the same disqualification G22/G24 face. It stays outside the 14-column grid and
is not part of B2-F1's 16.

**Scope note, so this is not read wider than measured:** the checked backend does not see a scatter at
all today (`Compile.lean` throws `scatterOrAffineLhs` at three sites; `checkScanLHSSlot` rejects
`.affine`). Every measurement above is of the **legacy** evaluator. It is B2's business because the
Scatter slice is what carries `.affine` into the checked backend.

---

## 4. B1-F10 answered: the negative coverage, named in four tiers

B1-F10's baseline reproduced with commands recorded verbatim in the fragment: 5 geometry `#guard`s
(all acceptances), 0 negated `#guard`s, 0 `== false`, 3 `writeGeometryNotAdmitted` assertions all
carrying `isBase = false`. One sharpening so B1-F10 is not read too widely: the **value**-predicate
siblings *do* have base-phase fixtures (`writeFreeExtentMismatch true 0 …`,
`writePinnedLiteralOutOfRange true 1 …`, `baseWritesOverlap 0 0 1`, plus two `.scan
(.baseWritesOverlap "sc2" "dp" 0 1)`). The gap is specific to **geometry admission at base**.

**No tests were added.** §B2.6 names 12 numbered items plus one differential obligation, in four
tiers: (1) the first negative `#guard`s either geometry predicate has ever had, three strided
placements plus three positive controls, plus a retrofit for B1-F10's own 10 unlocated cells; (2) five
base-phase `writeGeometryNotAdmitted true …` fixtures — the family with zero members — including a
data-asserting acceptance control, because without one a fixture cannot distinguish "wrote the right
cells" from "skipped every write", which is exactly the failure §B2.5 found; (3) two boundary cases
(`scale = 0` reclassifying as `.pinned`; the `scale=1, offset=1` context-vs-output ordering
obligation); (4) hand-extending `ScanUnroll.lean`'s oracle rewrite, since it deliberately calls no
scan-write helper — the item most likely to be skipped, and skipping it silently turns the three-way
gate into a two-way one.

**Finding B2-F5:** the 6 new `b` cells are **not locatable by any test that could exist at
`9680b92`** — the constructor they classify does not exist. That is a different status from B1-F10's
10 unlocated cells, which *could* be pinned today, so they are counted separately in the gate line.

---

## 5. Findings introduced

| ID | Substance | Status |
|---|---|---|
| **B2-F1** | The write-geometry defect family recurs a **sixth** time, **live** at base under decision A: clause 2's `filterMap` drops a strided row from the cover, both value predicates pass it at any extents, `writesCollide` can only over-reject, and `commitWrite` computes `scale·out[p] + offset` with no bounds recovery — reaching flat address **14 on a 9-element store** | OPEN, 16 cells |
| **B2-F2** | **Not one `a` cell among 56.** No audited site requires or demands a strided row's presence, in either phase — though clause 2 and clause 4 are positional-*cover* clauses, and a strided row is a cover row no clause counts | Finding |
| **B2-F3** | Four docstrings (`WriteRowKind`'s, `pinnedLiteralsInRange`'s, `writesCollide`'s, `commitWrite`'s three bullets) plus `Eval/AGENTS.md`'s `Scan.lean` row enumerate the constructor set as a closed list and go stale. Located starting set given as 6 files, from a recorded command — offered as a starting set, **not** as a claim to exhaustiveness | Finding |
| **B2-F4** | `freeExtentsAgree`'s equality **is** the shared formula's `scale=1, offset=0` case; there is no arm supplying the general one. The tempting tighter bound (`scale·(n−1)+offset < stateShape[d]`, 5 vs 6) is the **`scatterOutDim` drift shape in miniature** — a second extent formula disagreeing by `scale − 1` with no import enforcing agreement | Finding + recommendation |
| **B2-F5** | The 6 new `b` cells are not locatable by any test that could exist today | Finding |
| **B2-F6** | The minimal strided kind admits a **strict subset** of the affine LHS forms `outExtent` prices: `Out[2*i]`, `Out[i+3]`, `Out[2*i+3]` yes; `Out[i+j]` no — and once barrier 0 is lifted, that rejection surfaces as a positional `writeGeometryNotAdmitted` rather than a source-locating capability error | Finding |

---

## 6. Concerns

1. **B2-F1 is the deliverable that matters, and it is live rather than latent.** Under decision A the
   Scatter slice cannot land `baseWriteRowsOk` unchanged without shipping an out-of-range
   `Array.set!` at flat address 14 on a 9-element store. `baseWriteRowsOk` needs the counterpart of
   `stepWriteRowsOk`'s third clause — a statement of which rows MAY occupy an output position — and
   `freeExtentsAgree` needs a strided arm. Stated as obligations; no code written.

2. **§B2.1's decision rests on a scope assumption I do not have authority over.** If affine LHS
   writes are step-only, decision B is right and 16 cells go from live to latent. The fragment labels
   this conditional and gives decision B's reading per group, so the slice inherits a tested answer
   either way — but *someone with the feature's scope in hand should confirm which decision holds*.
   This is the one non-measurement in the section and it is marked as such.

3. **B1-F9 turned out to be live at HEAD, from surface syntax, independent of the Scatter slice.**
   `Out[0*i] := X[i]` returns an empty tensor with every write dropped and no diagnostic. This is not
   a pre-scatter forecast; it is a current-behaviour finding on the legacy evaluator, and it is
   arguably fixable now rather than as part of the Scatter slice.

4. **B2-F4's recommendation (call `outExtent` via a synthetic-`AxisSpec` adapter) is a
   recommendation, not a measurement of feasibility beyond arithmetic.** I measured that the adapter
   reproduces the right numbers and that the import is available; I did **not** build the refactor,
   so whether a `Scan.lean` call site can be made to read cleanly is unverified.

5. **`[snippet, model]` is a weaker evidence class than anything B1 used**, and it is unavoidable
   without adding a constructor to production. Each such claim is paired with a `[snippet]`
   measurement of the real clause, and the pairing is sound only because the three arms involved
   (`| _ => none`, `| _ => true`, `| _, _ => false`) are constructor-blind by their own quoted text.
   A reviewer who disagrees with that transfer should treat the model observations as unverified.

6. **Two `—` marks follow B1's column convention rather than call order, and I flag it rather than
   silently rely on it.** B1 marks `freeExtentsAgree`/`pinnedLiteralsInRange` as `c` (not `—`) for
   step rows that `stepWriteRowsOk` already rejects, even though `checkWrites` throws before calling
   them. I kept that convention for R15/R16 for consistency, and then closed G21/G23 *on* the earlier
   throw — so the convention is not doing any load-bearing work, but the mark is weaker than a `—`
   would be.

---

## 7. Verification trail

| Claim | How verified |
|---|---|
| Build green, 8660 jobs | `cd leanncd && "$HOME/.elan/bin/lake" build` → `Build completed successfully (8660 jobs).` |
| Production diff empty | `git diff HEAD --stat -- leanncd/LeanNCD leanncd/lakefile.toml leanncd/test` → no output |
| Census reproduces | Script parsed every `\| R<n> \|` row of the committed fragment, stripped `**`/`‡`/`§`, tallied: 224 / 24 a / 22 b / 122 c / 24 — / 32 ▷; B1's 12 rows unchanged at 168 / 24 / 16 / 86 / 18 / 24 |
| Exactly one append marker, last line | Script asserted one occurrence and printed the final line |
| 5 geometry `#guard`s, all acceptances | `grep -rn "#guard.*baseWriteRowsOk\|#guard.*stepWriteRowsOk" test/` → 5; `grep -rn "#guard *!.*WriteRowsOk\|#guard *¬.*WriteRowsOk" test/` → 0; `grep -rn "baseWriteRowsOk\|stepWriteRowsOk" test/ \| grep -i false` → 0 |
| 3 `writeGeometryNotAdmitted` assertions, all `false 0` | `grep -rn "writeGeometryNotAdmitted" test/` |
| Value-predicate base-phase fixtures exist | `grep -rn "writeFreeExtentMismatch\|writePinnedLiteralOutOfRange\|baseWritesOverlap" test/` |
| `commitWrite` has 3 per-constructor bullets | `grep -n "^    - a \`\.\|^    - an \`\." leanncd/LeanNCD/Eval/Plan/Scan.lean` → lines 544, 548, 558 |
| 4 constructor-enumerating prose sites in `Scan.lean` | `grep -n "pinned\`/\`\.free\|free\`/\`\.advancing\|pinned to a literal" leanncd/LeanNCD/Eval/Plan/Scan.lean` → lines 6, 95, 108, 109 |
| 6-file starting set for the doc pass | `grep -rln "advancing" --include='*.lean' --include='*.md' leanncd/LeanNCD/ \| xargs grep -l "pinned"` |
| `outExtent` five arms exhaustive | `inductive IdxExpr` (5 ctors) and `def LHSSlot.outIdx` (total over 5 `LHSSlot` ctors) both read at `DSL/Ast.lean` |
| `outExtent` visible from the Plan subtree | S22; plus `grep -n "^import"` over 11 `Eval/Plan/*.lean` files, giving the chain `Scan → Block → Dense → Check → Error → Kernel → DSL.Ast` |
| Surface syntax cannot express a negative affine LHS | `elabTLLHSSlot` read at `DSL/Elab.lean`: all four affine arms and `.iterAt` use `Int.ofNat n.getNat` |
| All S17–S26 outputs | `lake env lean spikes/<file>.lean`, captured to the three `.output.txt` files committed alongside |
| Throwaway model deleted | `leanncd/spikes/AxisBStridedModelThrowaway.lean` removed; `axis-b-spikes/` listing contains only the 3 keeper pairs plus B1's 2 |

### Exhaustiveness claims made, and how each is discharged

Given how often these have been falsified in this audit, every one is listed:

1. *"`outExtent`'s five arms are exhaustive over its own input"* — both inductives counted by reading
   them, not inferred.
2. *"`classifyWriteRow` has exactly one branch guarded on `p < contextWidth`"* — the function is 9
   lines and was read in full.
3. *"All 24 `a` cells belong to R1–R12"* (B2-F2) — from the mechanical recount, which reports 0 `a`
   in R13–R16.
4. *"All five geometry `#guard`s are acceptances; there is no negated one"* — three greps, all
   recorded, including the negated-form search that returned 0.
5. *"Every plan-level `writeGeometryNotAdmitted` assertion carries `isBase = false`"* — one grep, 3
   hits, each inspected.

**One place I deliberately did not claim exhaustiveness:** B2-F3's list of constructor-enumerating
documentation sites is described as *"the located starting set… not a claim that these are the only
affected sites"*, because the greps that produced it match on a prose pattern rather than on
structure.
