# B5c final whole-branch review A — acceptance/shape

- Base: `806d35abb86e743c0c9c9f9dfe08d9f0c32db5f1`
- Reviewed committed snapshot: `d634d84c` on `b5c-exec`.
- Lens: independent acceptance/shape audit of the entire committed diff, plan/design
  conformance, fixture strength, and Bridge/Agreement theorem statements.
- Constraints: no builds, source/fixture/manifest edits, delegation, or other-review
  access. Evidence below refers to immutable committed objects, not subsequent
  working-tree changes.
- Status: complete — **APPROVE WITH NONBLOCKING FINDINGS**.

## Evidence and coverage log

- Review initialized before investigation. Authority sections 2, 5, 6, 7, design,
  authoring record, and complete snapshot diff will be inspected next.
- Read authority plan sections 2, 5, 6, 7 (including the three explicitly known S
  cells), section 9, and the complete design. The committed diff comprises 17
  files, 298 additions and 40 deletions.
- Snapshot production diff inspected: `Collect.lean` adds boxed-single
  classification, makes singleton groups take B5, and appends them alongside
  (not instead of) the unchanged multiwriter groups. `ScheduledValidation.lean`
  passes pinned sizes only at native scheduled validation; the desugar default
  remains empty. `Differential.lean` adds a separately stated declared-shape
  condition. Source windows and fixture/unchanged-sibling audit remain in progress.
- Controller mutation run started during review. All further source/test evidence
  is taken from `git show`/`git diff` pinned to `d634d84c`; any local windowed
  copies are immutable snapshot extracts, never current production files.
- Read the authoring record (`additive_b5c_plan_record.md`), including prior
  scalar regression, transposed-assign fixture gap, 11 prototype mutation kills,
  and the explicitly unmeasured authoring cost. These are provenance claims, not
  gates rerun by this review.
- Read all 146 lines of snapshot `B5cSingleBoxTest.lean`: larger/equal/smaller,
  unpinned, bare assign, D5 idiom/transpose/identity, scalar, max-plus holes,
  reader, predicate, D2 classifier exclusions, multiwriter disjointness and
  route acceptance are present. Main larger-box values and shape are checked on
  all three native legs; smaller-box diagnostics are exact on all three.
- Snapshot `DefaultF32Test.lean` migrates only its scatter declaration to the D5
  idiom; dedicated new fixtures retain the genuinely distinct-axis box case.
  `lakefile.toml` registers the new module. The staged predictor adds four single
  rows and exact 17/11 row/accept counts. Differential pins require `fH9` parity
  with zero conditions and retain `fR` as a native failure naming `Y#1`; the
  retired condition does not turn that refusal into a successful comparison.
- Verified unchanged files by immutable base/snapshot diff:
  `DSL/Pipeline/Lowering.lean`, `Bridge/Agreement.lean`,
  `Eval/CollectorShape.lean`. Snapshot `Lowering.lean:594–600` calls
  `desugarMultiWriters logical` with its empty pinned default, then gates only
  `writerGroups logical.stmts`. Because singleton boxing requires a nonempty
  declared axis list and every axis in the empty map, it cannot activate there.
  The existing gate still refuses B5 multiwriter groups; legacy all-bare groups
  retain their previous route path (not all groups are categorically refused).
- Read theorem **statements**, not just proofs: snapshot
  `Bridge/Agreement.lean:31–40` factors successful compilation through the
  default desugar and physical route; `:417–419` states successful compilation
  implies `tc.WellFormed`; `:447–450` states DSL/CSV realization equality with
  `WellFormed` and `WellShaped` hypotheses. None states native boxed-shape or
  evaluator-value agreement. No theorem hypothesis or conclusion was weakened.
- Read all remaining committed documentation diffs. One low-severity factual
  documentation discrepancy is recorded below; no production defect established.
- Traced fixture observations through snapshot `B5NativeTest.lean:7–34,157–165`:
  the f64 variant only changes declared dtype (it does not synthesize missing
  tensor declarations), reference and checked paths are distinct, and `agree`
  compares actual f64/f32 bit patterns against expected arrays. Snapshot
  `B5bBoxTest.lean:109–114` makes `shapesOf` inspect public `S.shape` on all three.
- Traced the shared shape mechanism (`Eval/CollectorShape.lean:10–40`): retained
  original writer slots produce actual extents, pinned declared basis produces
  expected extents, boxed obligations use per-dimension `<=`, and boxed private
  scatter names enter `sizingView`. The unchanged collector reads scratches in
  the agreed sort (`Collect.lean:221–229,258–269`), rather than inserting a second
  padding implementation.

## Acceptance/shape coverage (all source citations at `d634d84c`)

Paths in the table are relative to `leanncd/`; `Single` abbreviates
`test/Eval/Plan/B5cSingleBoxTest.lean`, `Collect` abbreviates
`LeanNCD/DSL/Pipeline/Collect.lean`, and the `OracleSortRules*` files are under
`test/Semantics/`.

| Case | Code / fixture evidence | Assessment |
| --- | --- | --- |
| Larger, equal, smaller single scatter | `Collect:142–163,174–184`; `Single:93–103` | Larger shape and holes on three legs, equal values, exact smaller-box diagnostics on all three. Smaller box deliberately refuses although actual nonzero write coordinates fit. |
| Unpinned / undeclared single | Classifier requires declared axes and every UID pinned (`Collect:149–152`); `Single:103,138–141` | Unpinned derived shape exercised on three legs. Undeclared exclusion follows directly from `none` in declaration lookup; no dedicated new undeclared-single runtime twin. |
| Bare assign | `Collect:158–161` and singleton `needsB5` at `:100–103`; `Single:106–110` | Padding values, tight shape, and exact overrun refusals on three legs. |
| D5 upsample / transpose / identity | `Collect:153–161`; `Single:113–117,138–141` | Derived shapes on three legs plus explicit no-singleton classification. Rectangular transpose makes accidental boxing observable, unlike a square transpose. |
| Rank-0 scalar | Nonempty-axis check `Collect:152`; `Single:115,138–141` | Empty shape on three legs and explicit exclusion; catches otherwise-vacuous D5. |
| Tropical additive identity | Agreed-sort collector `Collect:221–229,258–269`; `Single:120–121`; helper `B5NativeTest:157–165` | Max-plus negative data and `-inf` holes compared bitwise, including f32. Existing `B5bBoxTest:64–67` retains max/min group identity checks. |
| Reader shape | `Single:125–129` | Reference and checked f64 require reader shape plus full values; checked f32 requires reader shape. |
| D1 predicate | Algebra exclusion `Collect:152`; `Single:133,138–141` | Reference derived shape and classifier exclusion; checked-leg limitation remains explicitly known S. |
| D2 constant / multiaxis | Bounded-slot guard `Collect:156–157`; `Single:84–90,138–141`; shared `DSL/Ast.lean:78–84,472–475` | Classifier exclusions, not new end-to-end checked acceptance/value claims. Explicit constant differs intentionally from zero-scale bounded syntax. |
| Multiwriter / legacy all-bare | `writerGroups` remains length >=2 (`Collect:88–97`), singleton classifier matches only `[i]` (`:149–150`); existing geometry/sort/UID checks `:188–219` unchanged | Group sets disjoint; no double collection. `Single:140` tests concat is absent from singleton groups; inherited B5/B5b guards still cover group values and refusals. |
| Route | `DSL/Pipeline/Lowering.lean:594–600`; default empty map `Collect:241`; `Single:144` | Actual call does not box singles; B5 multiwriter refusal remains. Fixture is only an acceptance guard, not an isolating desugar guard (known S). |
| Oracle and staged SHAPED | Differential diff at `Semantics/Source/Differential.lean:206–224`; `OracleSortRules.lean:301–316,323–343,347–377`; `OracleSortRulesTest.lean:474–504` | Independent declaration/slot predicate, real checked preparation with concrete signatures, explicit accept/refusal counts. SHAPED observations are not value/shape-content comparisons. |
| Bridge/Agreement | `LeanNCD/Bridge/Agreement.lean:31–40,417–419,447–450` | Unchanged statements concern routing well-formedness / DSL–CSV realization, not native boxed shapes. |

## Findings

### A1 — Low / nonblocking: stale count of iter-pinned staged rows

- **Location (snapshot):** `leanncd/LeanNCD/Semantics/AGENTS.md:163–164`.
- **Evidence:** the changed paragraph says two hand rows pin their box through
  an `iter` declaration. Snapshot
  `leanncd/test/Semantics/OracleSortRulesTest.lean:474–480` has four: the existing
  two-affine iter box12/box4 and the new single-affine iter box12/box4. The overall
  17 rows / 11 accepts / 6 refusals counts are correct.
- **Impact:** evidence-navigation prose undercounts iter coverage; no acceptance,
  shape, evaluation, predictor, or theorem behavior changes.
- **Proposed adjudication:** accept as nonblocking documentation debt; replace
  “two rows” with “four rows” in a separately authorized follow-up. This reviewer
  makes no fix.

## Scope limits

- Known S: route guard does not isolate absence of singleton desugaring; required
  to widen for this goal? no (explicitly excluded); rough cost 1 dispatch.
- Known S: differential D5 branch is not independently exercised because source
  admission rejects the idiom first; required to widen for this goal? no; rough
  cost 1 dispatch.
- Known S: predicate single-writer checked legs unobserved (unrelated checked-input
  refusal); required to widen for this goal? no; rough cost 1 dispatch.
- Scope-excluded: M4 fit-by-write-image and zero-scale scratch range failures,
  inferred-size boxes, route/JAX shape parity, scan-local writers, F3 and D1/D2
  geometry extensions; required for this goal? no (plan section 2 expressly
  excludes them); rough cost multiple dispatches per independent slice, not
  estimated more precisely by this bounded review.
- Fixture limitation: D2 uses classifier assertions, and `groupsOf` returns `[]`
  on scheduling failure (`Single:79–82`); unlike positive runtime cases, these
  negative classifier rows do not separately assert successful scheduling or
  end-to-end execution. No current scheduling failure is established here;
  required to widen for this goal? no; rough cost 1 dispatch.
- Fixture limitation: no dedicated new undeclared-single runtime twin or
  single-writer min-plus hole fixture; checked f32 reader values are not pinned
  beyond shape. Code inspection, shared machinery and inherited group tests are
  the evidence, not proof of those extra cases; required for this goal? no;
  rough cost 1 dispatch.
- Predictor limitation: SHAPED compares preparation outcomes/refusal tags, not
  published tensor shapes or values, and permits pre-existing `sizeConflict` only
  for a predicted exact-shape mismatch (`OracleSortRules.lean:347–377`); required
  to strengthen for this goal? no; rough cost 1 dispatch.

## Review completion and budget

- Entire committed 17-file diff inspected. No acceptance, shape, padding,
  multiwriter, route, or theorem-statement defect found within the approved
  scope. A1 is the sole finding and is documentation-only.
- No build, test, mutation, or gate was run by this reviewer; the controller owns
  all execution gates. Prototype results quoted above are explicitly attributed
  to the authoring record, not independently revalidated.
- No delegation, external-system access, source/fixture/manifest edit, or commit.
  The review report is the only intended tracked-file change. Local snapshot
  extracts used for file-viewer windows are removed at completion.
- Budget: fewer than 45 assistant turns by manual count; peak-context and token
  usage are not instrumented in this review. No known budget breach.

## Final verdict

**APPROVE WITH NONBLOCKING FINDINGS** for snapshot `d634d84c` against
`806d35abb86e743c0c9c9f9dfe08d9f0c32db5f1`, subject to the controller's gates.
Adjudicate A1 as accepted low-severity documentation debt (optional separately
authorized count correction); do not expand the three known S cells or any other
excluded scope as part of this review.
