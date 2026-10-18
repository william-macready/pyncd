# S2a P2a findings: admission of non-bare writes

Branch `proto-s2a-p2a` (from `proto-s2a-p1` @ 33ea3df5). Patches in `p2a_patches/`.

## 1. Diagonal-write fact check (answer: ALREADY admitted)

`Y[a, a] := X[a]` with `Y` declared over `[a, a]` is admitted by today's `admitSource`, before any
P2a change (probe run on the P1 tip): `indices = [7, 7]`, `context.axes = [7]`, `shape = [7, 7]`
(the signature), `dest = id`. It is the bare path. `firstUIDs` dedups the output context, and the
two slots resolve to the same context axis. S2a only needs a regression fixture, now in
`SourceAdmissionAffineTest` (both entries agree; forms `[(0,[(1,7)]), (0,[(1,7)])]`; distinct
images `[[0,0],[1,1]]`). It stays on the bare path under `admitSourceAffine` as well, because
an all-`.free` `.assign` is delegated to `admitStatement`.

## 2. Final types and signatures (Admission.lean)

```lean
abbrev WriteForm := Int × List (Int × UID)          -- idxAffineForm's codomain
def WriteForm.single (u : UID) : WriteForm := (0, [(1, u)])
def WriteForm.uids (f : WriteForm) : List UID
def writeValue (f : WriteForm) (v : UID → Int) : Int  -- f.1 + Σ coef * v uid
def coordLookup : Coord sh → UID → Int                -- first axis with that uid, else 0
def coordValues : Coord sh → List Int
def coordAll (sh) (p : Coord sh → Bool) : Bool        -- box enumeration; coordAll_spec
def formFits (a : Axis) (f) (v) : Bool                -- 0 ≤ value < a.extent
def formsFit : Shape → List WriteForm → (UID → Int) → Bool
def coordOfForms (sh fs v) (h : formsFit sh fs v = true) : Coord sh

structure AdmittedOutput (source : Context) (σ : Declarations Unit) where
  ...P1 fields unchanged...
  forms : List WriteForm          -- NEW, last field: one form per destination axis

def AdmittedOutput.FormsSpec (output) : Prop :=
  ∀ w : Coord source.axes, coordValues (output.dest (output.sourceSlots.project w)) =
    output.forms.map (writeValue · (coordLookup w))

theorem admitOutput_forms        : admitOutput … = .ok o → o.val.forms = ids.map WriteForm.single
theorem admitOutput_formsSpec    : admitOutput … = .ok o → o.val.FormsSpec
theorem admitAffineOutput_formsSpec :
  admitAffineOutput source dst forms origin = .ok o → o.val.forms = forms ∧ o.val.FormsSpec
theorem AdmittedOutput.formsSpec_of_forms   -- the general lemma behind the affine case

def admitAffineOutput (source : Context) (dst : σ.Tensor) (forms : List WriteForm)
    (origin : SourceOrigin) : Except SourceDiagnostic {o : AdmittedOutput source σ // o.tensor = dst}
def admitAffineStatement (source : AdaptedSource) (original : Nat) : Stmt → Except … (AdmittedStatement source)
def admitSourceAffine (snapshot : SourceSnapshot) : Except SourceDiagnostic AdmittedSource
```

Adapter.lean: `UnsupportedSource.scatterPolicy` and `SourceCause.writeOutOfRange` (no payload;
the origin's `slot` carries the destination axis index, like other output refusals).

### How forms are represented, and why the spec is not a field

- The oracle reads `statement.output.forms` (rg: `forms : List WriteForm`). It evaluates them
  with `writeValue f (coordLookup w)` over a SOURCE valuation `w : Coord source.axes`, so the
  forms are over source UIDs. It never needs `dest` or `shape`.
- For a bare write the forms are `indices.map WriteForm.single`, so a diagonal write has the
  same uid twice.
- `FormsSpec` is a separate `Prop` rather than a structure field. A stored proof would break
  P1's `{ o with tensor := t, dest := d }` retargeting in `SourceAffineDestinationTest`, which
  takes an arbitrary `dest`. It is proved for each of admission's two output builders by
  construction (unfold + split, the `admitOutput_identity` pattern).
- **Gap: not yet lifted to statements or sources.** There is no theorem
  `admitSourceAffine s = .ok a → ∀ st ∈ a.statements, st.output.FormsSpec`. It needs one
  unfolding of `admitAffineStatement`/`admitAffineWrite` (the `admitStatement_fields` pattern;
  the bare arms can reuse `admitStatement` plus `admitOutput_formsSpec`). This is P3's natural
  entry point, since the oracle proof is its consumer. It was left out for budget.

### Affine output construction

- `outputForms` gives one form per LHS slot: `.free a` ↦ `single a.uid`, `.affine e` ↦
  `idxAffineForm e`. Every `AxisSpec` is checked with `sourceAxis`, so an unknown axis is
  `.unbound` at that slot. `.freeNorm` stays `.unsupported .marked`; `.iterAt`/`.iterNext`
  stay `.scanSlot`.
- A rank mismatch is `.rank` at slot `min forms.length sig.length`.
- `indices := formsSupport forms` (`firstUIDs` of the mentioned uids) and
  `shape := supportShape source indices` (source extents). `slots`/`sourceSlots`/`context`/
  `embedding` are resolved exactly as in `admitOutput`, at `shape`.
- Range check: `coordAll shape (fun w => formsFit sig forms (coordLookup w))`. It enumerates
  the whole support box (decidable, no corner reasoning). On failure, the origin slot is the
  first destination axis whose form leaves `[0, extent)` somewhere on the box.
- `dest w := coordOfForms sig forms (coordLookup w) (coordAll_spec … w)`, with value
  `(writeValue f v).toNat` and the bound from the check.
- A write with an empty support (all `.const` slots) gets `shape = []`; this is not
  fixture-tested (see §6).

## 3. Raw chain: handled by a SEPARATE entry, not a flag

`admitSource`, `admitStatement`, `StatementFields`, `admitStatement_fields`, `admitSource_fields`,
`admitRawSource` and every RawCorrespondence/RawSemanticConnection/Provenance theorem are
**unchanged, byte for byte**. They still refuse affine LHS slots (`.unsupported .affine`) and
every scatter (`.unsupported .scatter`). Affine statements therefore get no raw-parse theorem,
by construction.

Deviation from the recommended `admitSourceWith (allowAffine : Bool)`: I added a second entry,
`admitSourceAffine` (built on `admitAffineStatement`), instead of re-expressing `admitSource` as
`admitSourceWith false`. Reason: the existing proofs (`admitStatement_fields`,
`admitSource_originals`, `admitSource_adapted`) unfold `admitStatement`/`admitSource` with
`simp only` and `split`. A flag would make them reduce through an extra `if`, for no gain. A
separate entry gives a zero diff there. The cost:

- `admitAffineWrite` duplicates the ~15-line write body of `admitStatement`'s `.assign` arm,
  differing only in `outputForms` + `admitAffineOutput`. Cleanup candidate: share it once both
  entries have proofs.
- `admitSourceAffine` duplicates the 4-line `admitSource`.

Routing in `admitAffineStatement`:

- An all-`.free` `.assign` goes to `admitStatement` (identical to the default).
- Any other `.assign` goes to `admitAffineWrite`.
- `.scatter`: first the policy check (`fill = 0`, `reduce ∈ {sum, rejectCollisions}`, else
  `.unsupported .scatterPolicy` at `{statement := some i}`). Then an all-`.free` scatter goes
  to `admitStatement` as an `.assign` (bare path, `dest = id`). Otherwise it goes to
  `admitAffineWrite`.
- `.recurMorphism` goes to `admitStatement`.

`NativeSource.admission` is now `admitSourceAffine snapshot = .ok admitted`, and `runNative`
matches on `admitSourceAffine`. No library proof consumed `NativeSource.admission`.

The theorems stated over arbitrary `AdmittedStatement`/`AdmittedSource`
(Fiber/Correspondence/ProgramCorrespondence/Permutation/Observation) hold for both entries'
statements, because P1 already stated them over `dest`. The theorems that take an
`admitSource … = .ok` hypothesis (`admitSource_fields`, `admitSource_originals`, the raw chain)
cover only the default entry. In particular, there is no `admitSourceAffine_originals` yet, so
`IdentifiedSource` is built only from `admitSource`. (Gap; same pattern as
`admitSource_originals`.)

## 4. Per-file table (vs P1 tip 33ea3df5)

Code commits: ba33df5e (admission), fb8311a0 (fixtures), b6e39e58 (NativeLegs). Patches are
`p2a_patches/0001..0003`.

| File | +/− | Change |
|---|---|---|
| Source/Admission.lean | +294/−2 | helpers (§2), `forms` field, `FormsSpec` + 4 theorems, `outputForms`, `formsSupport`, `supportShape`, `admitAffineOutput`, `admitAffineWrite`, `admitAffineStatement`, `admitSourceAffine`. The −2 are the `admitOutput` constructor and the `isBare_of_identity` `cases` pattern (new `forms` binder) |
| Source/Adapter.lean | +5/−0 | `UnsupportedSource.scatterPolicy`, `SourceCause.writeOutOfRange` |
| Source/NativeLegs.lean | +2/−2 | `NativeSource.admission` and `runNative` use `admitSourceAffine` |
| lakefile.toml | +1/−0 | `Semantics.SourceAdmissionAffineTest` after `Semantics.SourceAdmissionAcceptanceTest` |
| test/Semantics/SourceAdmissionAffineTest.lean | +139 (new) | fixtures (§5) |

Untouched: Oracle, NumericalProfile, Differential, and every RawCorrespondence/
RawSemanticConnection/Provenance/Observation/Fiber/Correspondence proof.

## 5. Tests

**No existing test was edited, and none flipped.** The old `realSlots (.affine (.shift (a .real) 1))`
guard in `SourceAdmissionAcceptanceTest` still passes unchanged: `admitSource` still refuses it
with `.unsupported .affine`. The flip lives in the new file. The full Tests run, which includes
the differential tests that now go through `admitSourceAffine`, needed no test change. So no
existing differential fixture contains an affine or scatter write that the new entry would
admit.

`SourceAdmissionAffineTest` (all `#guard`, ℚ-free; each accepted view also checks `FormsSpec`
numerically on every source coordinate):

- (a) FLIP. `Y[a+1] := X[a]`, Y over `a` (|a|=2): `admitSourceAffine` gives `writeOutOfRange`
  at `{output, decl 4, stmt 0, slot 0}`. `admitSource` gives `.unsupported .affine` at the same
  origin.
- (b) Neighbour (`|k|` only): Y over `k`, |k|=3, admits with forms `[(1,[(1,7)])]`, indices
  `[7]`, images `[[1],[2]]`. |k|=2 refuses `writeOutOfRange`, and `admitSource` still refuses
  `.affine`.
- (c)
  - `Y[2*a]`, |k|=3: forms `[(0,[(2,7)])]`, images `[[0],[2]]`. |k|=2 refuses.
  - `Y[2, a]`, Y over `[k,a]`: forms `[(2,[]),(0,[(1,7)])]`, images `[[2,0],[2,1]]`. `Y[3, a]`
    refuses at slot 0.
  - `Y[a+b]`, |k|=4: forms `[(0,[(1,7),(1,8)])]`, indices `[7,8]`, images `[[0],[1],[2],[3]]`.
    |k|=3 refuses.
  - Diagonal: see §1.
- (d) scatter `Y[2*a]`:
  - `reduce := .sum` and `.rejectCollisions` (fill 0) are admitted with the `.scale` forms.
  - `.max`, `.min`, `.overwrite` and `fill := 1` are refused `.unsupported .scatterPolicy` at
    `{statement := some 0}`.
  - `admitSource` refuses `.unsupported .scatter`.
  - A bare scatter `Y[a]` (sum) is admitted with single forms.
- (e) the read `X[a+1]` is refused `.unsupported .affine` at the read origin (decl 3, slot 0)
  under both entries, with a bare LHS and with an affine LHS. The neighbour is the (c) `.scale`
  fixture, which reads `X[a]`.

## 6. Builds, gaps, budget

- `LeanNCD.Semantics.Source.Admission`: green, 8507 jobs.
- `LeanNCD`: green, 8612 jobs.
- `test/Semantics/SourceAdmissionAffineTest.lean` via `lean-file.sh`: clean.
- `LeanNCD Tests` (one run, at code tip b6e39e58): `Build completed successfully (8817 jobs)`.
  The baseline was 8816; +1 is the new test module. It includes `Semantics.AxiomAudit`: "6511
  constants under LeanNCD.Semantics use only standard axioms".
- No `sorry`, `native_decide` or new axiom.
- Gaps (not done, fail-loud):
  1. No source- or statement-level `FormsSpec` theorem for `admitSourceAffine` (§2).
  2. No `admitSourceAffine_originals` / `IdentifiedSource` from the affine entry (§3).
  3. No fixture for an all-`.const` write (empty support, `shape = []`).
  4. No fixture for a write whose RHS reads an axis that the LHS does not mention.
  5. The `writeOutOfRange` slot index is checked only for single-slot failures and for the
     slot-0 failure of the `[k, a]` fixture. A failure on a later slot is untested.
  6. The `.rank` mismatch path of `admitAffineOutput` is untested.
- No AGENTS.md node was updated (prototype). The `Semantics/Source` node must later record:
  the two entries, `forms`/`FormsSpec`, and that affine statements have no raw-parse theorem.
- Budget: about 60 harness tool calls (at the limit). Context peak was well under 250k
  (about 110k).
