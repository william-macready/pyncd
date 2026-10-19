# S2a T1 review (commit 1a8b49a7): proof soundness

Lens: proof soundness. All code read via `git show 1a8b49a7` (never the working tree). Nothing built.

## Answers to the brief

- (1) `IsBare` gate. The raw chain needs the WITNESS, and it uses both conjuncts. In
  `CertifiedRawStatement.output_projection`, `hbu : bare.uids = indices` turns the certified
  `RawOutputSlots raw memo slots indices` into `RawOutputSlots ... bare.uids`, and that is what
  `RawOutputSlots.coordinate` needs: it reads coordinate `j : Fin sh.length` of `slots.project`
  for a `Slots` at the shape `sh`. Only `bare` sits at the destination signature, so only `bare`
  gives a reading at `q : Fin (signature).length`. Then `hbd` rewrites
  `dest (sourceSlots.project _)` to `bare.project _`. The equation alone (no witness) gives no
  `Slots` at the signature to apply `coordinate` to. The structural form (`shape = sig`,
  `dest = hs ▸ ·`) would also work, but only by transporting `sourceSlots` across `hs`. The
  witness is the weaker of the two (`isBare_of_identity` goes structural to witness), so it is
  the minimal sufficient gate. Not vacuous: `admitStatement_fields` discharges it through
  `admitOutput_bare`, and `rawStatement_fields` passes it on (`hs.2`).
- (2) Strength. Each listed theorem is the old statement with `output.slots.project x`
  replaced by `output.dest (output.slots.project x)`: `Term.fiber_partition`,
  `Term.globalDestination_partition`, `Term.collectedBody_correspondence`, `Term.empty_fiber`
  (hypothesis `∀ x, dest (slots.project x) ≠ p`), `AdmittedStatement.fiber_partition` (through
  `AdmittedStatement.destination`, now `dest ∘ slots.project`) and `destination_pullback`. Each
  is universally quantified over every `AdmittedOutput`, so every `dest` is covered. For
  admission's outputs, `admitOutput` sets `shape := (σ.signature dst).axes` and `dest := id`,
  so each new statement reduces to the old one definitionally. No hypothesis was added to any
  of them. `StatementFields` and `RawStatementFields` each gained an `IsBare` conjunct. Both
  are still proved by their producers (`admitStatement_fields`, `rawStatement_fields`), so the
  consumers get a stronger premise, not one that can never hold. `Program.destination`
  (Program.lean, `tag.statement.destination`) and Observation both go through
  `AdmittedStatement.destination`, so the executed program follows `dest` too. Nothing was
  weakened.
- (3) Raw entry and forms. At this commit no affine admission path exists:
  `git grep WriteForm|FormsSpec|.forms|admitAffine` over `leanncd/LeanNCD` finds nothing.
  `admitStatement` still builds outputs only through `admitOutput` (identity). `BareOutputSlots`
  is unchanged and still rejects affine LHS slots. The new
  `RawStatementFields.output_bare` makes the gate explicit. Nothing claims a raw reading of
  forms, because forms do not exist yet.
- (4) No `sorry`, `axiom`, `native_decide`, `@[implemented_by]` or `admit` in any touched
  file. The only `decide` is the Bool `decide (shape = ...)` inside the computed `bareRow`,
  which a `#guard` evaluates; no proof uses it. The new proofs (`isBare_of_identity`: `cases`,
  `subst`, defeq of `rfl ▸ x`; `admitOutput_identity`: the same `split`/`subst` skeleton as
  `admitOutput_fields`) rely on no new simp sets.
- (5) Guards: see the findings. Mutation-by-mutation, assuming the proof had not killed it
  first: T1-M1 (`if True`) makes every fiber 1+2+3+4 = 10, so `termGlobal`/`statementGlobal`
  `[1,0,2,0,...]` would FAIL. T1-M2 (`else some 1`) makes the spread fiber at p=0
  `1 + 1 + 1 + 1 = 4`, so `termCollected` `[some 1, ...]` would FAIL. T1-M3 (`.headD 0`) would
  SURVIVE (finding F1). The two rows also tell `dest` apart from "dest ignored": ignoring it
  would give `[1,2,3,4,0,0,0,0]` for both the spread and the collapsing write. The
  `retarget` + `term.fiber_partition` example pins the theorem's statement shape for an
  arbitrary `dest`.

## Findings

- **Minor: T1-M3 cannot be caught by any T1 guard; only the proof kill covers it.**
  Location: `SourceAffineDestinationTest.affineSnapshot` / `affineRow.statementGlobal`.
  Evidence: the only statement has one product term,
  `.assign "T" [.free x] (rhs [[.read "X" [.axis x]]])`, and
  `AdmittedStatement.globalFiber` is `(statement.terms.map ...).sum`. With one term, `.headD 0`
  equals `.sum`, so `statementGlobal` just repeats `termGlobal`. Why it matters: the record
  must not say the statement-level guard measures term summation. If the proof of
  `AdmittedStatement.fiber_partition` were later restructured so that it no longer dies on
  this mutation, nothing would catch it. Cheap fix if wanted: give the retargeted statement a
  second term (e.g. `rhs [[X[x]], [X[x]]]`). This is parked as a suggestion and is not needed
  for T1's soundness.
- **Minor: `AdmittedStatement.destination` itself is never evaluated by a guard.**
  Location: `SourceAffineDestinationTest.affineRow`. Evidence: `statementGlobal` is
  `affine.globalFiber`, which sums `term.globalFiber` and so goes through
  `Term.globalDestination`. `AdmittedStatement.destination` (the consumer of
  `Program.destination`, the executed program and `Observation`) is only covered by the
  `AdmittedStatement.fiber_partition` / `collect_statement` proofs. Why it matters: it is the
  path that T2/T3 production lowering will exercise. A row of
  `affine.destination (srcLayout.enumerate n)` listing the images would pin it directly. The
  same caveat as F1 applies: today the proofs kill any type-correct mutation of it.
- **Minor (Question): `IsBare` only constrains `dest` along source valuations.**
  Location: `AdmittedOutput.IsBare`. Evidence:
  `∀ w, output.dest (output.sourceSlots.project w) = bare.project w` with
  `w : Coord source.axes`. If `Coord source.axes` is empty (some declared axis, not
  necessarily an output index, has extent 0), `IsBare` holds for every `dest`. Why it
  matters: this is harmless for the raw chain, whose conclusions (`output_projection`,
  `destination_bare`) are `∀ v : UIDVal source.context` and so already empty in exactly that
  case. That vacuity existed before this commit. But `IsBare` must not be read or cited as
  "`dest` is the identity" or as a statement about context coordinates. For that,
  `admitOutput_identity` is the lemma to use. The docstring ("bare projection of the source
  valuation") is accurate.
- **Minor: the statement of `CertifiedRawStatement.output_projection` changed, though the
  plan's checklist (e) says "keeps its signature".**
  Location: `CertifiedRawStatement.output_projection`; the same edit is in
  `SourceRawCorrespondenceTest.DonorOutputConnection`. Evidence: the conclusion changed from
  `statement.output.sourceSlots.project (...)` to
  `statement.output.dest (statement.output.sourceSlots.project (...))` in two places. The
  hypotheses (`h`, `v`) are unchanged and no premise was added. Why it matters: this is not a
  weakening. The old text no longer typechecks (`sourceSlots.project` now lands in
  `Coord shape`, while `q` indexes the signature), and the new conclusion is the true
  destination coordinate, which matches the old one definitionally for admitted outputs. The
  record should say "hypotheses unchanged, conclusion generalised through `dest`" rather than
  "signature unchanged".

Verdict: APPROVE. The proofs are sound and no theorem was weakened. `IsBare` is the right, minimal gate and its hypotheses can be satisfied. The raw entry refuses affine outputs by construction. There are no escape hatches. The T1 guards are UNMEASURED (all 3 cycles are proof kills). T1-M1 and T1-M2 would also fail the guards, but T1-M3 would survive them (single-term fixture). Four Minor findings, none blocking.
