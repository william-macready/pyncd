# S2a final whole-branch review, lens (a): semantics / proof soundness

Reviewer: Opus 5.5. Range 6fad5161..42013f71, read via `git show 42013f71:` / `git diff` only (no builds).

## Findings

- **Minor: "bare" is recognised by form shape, not by admission path, so an affine-path write with unit
  forms into a wider destination is normalised as bare and reported as a `referenceDiscrepancy`.**
  Location: `Debug.normalizeOracleContribution`, `NumericalProfile.checkFiber` (`let bare := ...`) and
  `Differential.nonBareWrite`, all testing
  `statement.output.forms == statement.output.indices.map WriteForm.single`.
  Evidence: `idxAffineForm (.shift a 0) = (0, [(1, a.uid)])` and `idxAffineForm (.scale 1 a)` give exactly
  `WriteForm.single a` (`Elab` produces `.scale 1 a` from `1*a`). `admitAffineWrite` admits
  `Y[a+0] := X[a]` with `Y : [k]`, `|k| = 9`, `|a| = 2`. `SourceAdmissionAffineTest` (g) pins that admission
  (`view (admitSourceAffine (snap 9 [k] (.assign "Y" [.affine (.shift a 0)] readX))) == some [([(0, [(1, 7)])], [7], [[0], [1]], true)]`).
  The bare path would refuse it, because `resolveSourceSlots` demands equal extents. In the differential,
  `normalizeOracleContribution` passes the `nonBareWrite` gate, and `assign` checks only `coordinate < 9`.
  So the rows for cells 2..8 each produce an occurrence keyed `(a, c)`, which the executor never emits, and the
  body comparison disagrees. `classification` then returns `referenceDiscrepancy` before the
  profile or condition checks run. The same misclassification hides `scatterExtentOverridesDeclared`
  (`nonBareWrite` is false there too).
  Why it matters: this is not unsound, because the failure is loud. But a valid admitted program is reported
  as a reference (executor) bug, which is the most misleading of the possible labels, and nothing tests the
  case. Fix: also require the destination entry's extents to equal the support extents, or carry an explicit
  path flag. Add a differential fixture `Y[a+0]` into a wider `Y`.

- **Minor: the builder lemmas are not lifted to `admitSourceAffine`.** Location: `admitAffineOutput_formsSpec`,
  `admitOutput_formsSpec`. `admitAffineWrite`/`admitAffineStatement` have no `_fields`-style theorem, so the
  claim "every output of the differential's reference entry satisfies `FormsSpec`" holds by inspection (the
  only two `AdmittedOutput` constructions in `LeanNCD/` are the two builders), not by a theorem. No
  downstream theorem consumes `FormsSpec` (it is referenced only at its definition and in the two builder
  lemmas), and the oracle/executor comparison would expose a `forms`/`dest` mismatch as a destination
  disagreement. So this is a documentation-precision point: "proved for the two builders" is accurate, but
  "proved for admission's outputs" (the `AdmittedOutput.forms` docstring) is one composition step beyond what
  is proved. Question: worth a two-line `admitSourceAffine` lemma, or reword the docstring?

- **Minor (doc accuracy, plan section 0 and record F2/F3 rows): three stale or overstated claims about scope
  limits.**
  (1) Plan: "today only T1's proof test builds one [a hand-built output whose `forms` and `dest` disagree]".
  But `SourceOracleAffineTest.tampered` also builds one (`{ st.output with forms := forms }`) and DOES pass
  it to `Oracle.run`, on purpose, to pin the oracle's `writeOutOfRange`. That use is legitimate and
  test-only, but the plan's "must never reach the oracle" plus "only T1" is false as written. It should say
  "never in production code; tests do so deliberately".
  (2) Plan: "no `.shift` value fixture". `SourceOracleAffineTest` fixture 4 (`Y[a+2]`, hand
  `[0,0,1,2,3,4]`) and fixture 7 (`Y[b+1]`) are hand-valued `.shift` fixtures. Record row F2 ("hand-valued
  `.shift`/negative-coefficient fixture parked") is half stale: only the negative-coefficient VALUE fixture
  is missing (admission-side negative coefficients are covered in `SourceAdmissionAffineTest` (g)).
  (3) Plan: "a defect in `idxAffineForm` is invisible to every differential row". The legacy leg's scatter
  coordinates come from `Eval.evalIdx` (`Eval/Scatter.lean` `outCoordZ := slots.map (fun sl => evalIdx coord sl.outIdx)`),
  which interprets `IdxExpr` directly, not through `idxAffineForm`. So on rows where the legacy value
  comparison runs (four-leg parity rows and the T4-A2 legacy collision-sum agreement), an `idxAffineForm`
  defect WOULD show. The claim overstates the gap in the safe direction. Only the checked leg (`Compile`,
  `Scan`, `Lowering`) and the reference/oracle pair share `idxAffineForm`.

- **Minor (nit): stale module docstring.** `SourceAffineDestinationTest` header: "Admission still produces
  only bare outputs, so the affine output is built here by retargeting". That was true at T1, but since T2
  `admitSourceAffine` produces affine outputs. Reword to "built by hand to exercise arbitrary `dest`".

## Checked and found sound (no finding)

1. `IsBare`/`FormsSpec`: `FormsSpec` is consumed by no theorem or definition. In production, `Oracle.run`,
   `normalizeOracle` and `checkRunProfile` are reached only from `compareSource`, through
   `sourceDebugAffine`, `admitIdentifiedSourceAffine` and `admitSourceAffine`. `Permutation` only reorders
   statements. The only hand-built outputs are in tests (`SourceAffineDestinationTest.retarget`,
   `SourceOracleAffineTest.tampered`).
2. Raw chain: the bodies of `admitStatement`, `admitSource`, `outputIndices` and `admitIdentifiedSource` are
   textually unchanged. `admitOutput` gains only constructor fields (`shape := sig`, `dest := id`,
   `forms := ids.map single`), with no new failure branch. `StatementFields`/`RawStatementFields` are
   STRENGTHENED (conjoin `IsBare`), discharged by `admitOutput_bare`.
   `CertifiedRawStatement.output_projection` keeps its hypotheses. Its first conclusion conjunct is now the
   `dest`-wrapped `destination_pullback`, but the per-coordinate conjunct still gives the bare raw reading
   for every `q`, now derived through the certified `IsBare` witness. So, coordinate by coordinate, the
   statement is as strong as before. No theorem mentions `forms` except `FormsSpec`, `admitOutput_forms`
   and the builder lemmas, so nothing gives a raw reading of forms. `admitAffineWrite` is private, and
   `admitAffineStatement` routes all-free `.assign` and all-free policy-checked `.scatter` to
   `admitStatement`.
3. Oracle independence: `termFiber`/`destination` read `statement.output.forms`, and the destination
   extents come from `(admitted.source.table.entry statement.output.tensor).axes`. A grep of `Oracle.lean`
   finds no `dest`, `sourceSlots`, `output.shape` or `output.indices`. Out-of-range values are an error, never
   wrapped. For bare statements the behaviour is unchanged: support = `indices`, and the range check is
   implied by `resolveSourceSlots`'s extent equality. The docstrings ("Independent of `dest`") are
   accurate. The `idxAffineForm` scope limit is stated in the plan (see the third Minor for its precision).
4. Admission: `coordAll_spec` makes the range check exhaustive over the support box `supportShape` (extents
   taken from the source context and re-validated by `resolveSourceSlots`). `dest` cannot be built without
   the `hfit` proof (`coordOfForms`), so a total typed destination exists only when every image fits.
   `formsSpec_of_forms` handles constants (empty uids), coefficient 0 (the uid stays in the support, value
   unaffected) and repeated axes (`firstUIDs` dedup plus `Slots.lookup_project`). There is a rank check, and
   fixtures cover lower and upper bounds, mixed signs and an interior-maximum case.
5. Theorem strength: `Term.globalDestination_partition`, `Term.fiber_partition`,
   `Term.collectedBody_correspondence`, `Term.empty_fiber`, `AdmittedStatement.fiber_partition`,
   `pure_correspondence` and `destination_pullback` are each the old statement with
   `slots.project x` replaced by `dest (slots.project x)`, universally quantified over all outputs. At
   `admitOutput` outputs (`admitOutput_identity`: `shape = sig`, `dest = id` up to the cast) they reduce to
   the old statements. `AdmittedStatement.destination_bare` recovers the old `destination_pullback`
   conclusion under `IsBare`.
6. Escape hatches: `git diff -G` for `sorry|axiom|native_decide|ofReduceBool|implemented_by|unsafe|partial`
   over `leanncd/` gives no hunks. `AxiomAudit` runs `#audit_axioms LeanNCD.Semantics` over
   `import LeanNCD.Semantics`, which imports `Semantics.Source` and so every changed module. New public
   theorems are therefore audited automatically. Pre-existing caveat, not S2a's: `audited` filters by
   `ns.isPrefixOf n`, so `private` declarations (mangled `_private...`) are not listed themselves. They are
   still covered transitively whenever a public declaration uses them, and S2a adds no private theorems.

Verdict: **APPROVE WITH MINORS.** There is no Critical or Major finding. The proof chain, the raw-chain
gating and oracle independence are sound. The first Minor (bare classification by form shape) is the only
one with behavioural impact (a false `referenceDiscrepancy`). It is loud, not silent, and can be fixed or
parked at the controller's discretion.
