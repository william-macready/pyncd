# Input and whole-store prototype

Source: `leanncd/experiments/indexed_execution/IndexedComponentModelInputs.lean`
in namespace `IndexedComponentComposition`. Assumptions are finite, decidable
`σA.Tensor`/`σB.Tensor`, matched components `A`/`B`, boundary `wire`, and the
existing rational `K`. `C` below abbreviates `program A B wire`; `ρ` is a
complete store over `declarations A B`. These are **signature transcriptions**,
not Lean code to paste into a module.

```text
liftInput (η : A.program.Input) : C.Input
restrictInput (η : C.Input) : A.program.Input
restrictInput_liftInput (η : A.program.Input) :
  restrictInput A B wire (liftInput A B wire η) = η
liftInput_restrictInput (η : C.Input) :
  liftInput A B wire (restrictInput A B wire η) = η

boundaryInput (ρA : Store K σA) : B.program.Input
boundaryFromOutput (out : A.program.Output) : B.program.Input
boundaryInput_outputProjection (ρA : Store K σA) :
  boundaryInput A B wire ρA =
    boundaryFromOutput A B wire (A.program.outputProjection ρA)

restrictUpstream (ρ : Store K (declarations A B)) : Store K σA
restrictDownstream (ρ : Store K (declarations A B)) : Store K σB
glueStore (ρA : Store K σA) (ρB : Store K σB) :
  Store K (declarations A B)
restrictUpstream_glueStore (ρA : Store K σA) (ρB : Store K σB) :
  restrictUpstream A B (glueStore A B ρA ρB) = ρA
restrictDownstream_glueStore (ρA : Store K σA) (ρB : Store K σB)
  (h : B.program.InputAgreement (boundaryInput A B wire ρA) ρB) :
  restrictDownstream A B wire (glueStore A B ρA ρB) = ρB
glueStore_restrictions (ρ : Store K (declarations A B)) :
  glueStore A B (restrictUpstream A B ρ)
    (restrictDownstream A B wire ρ) = ρ

inputAgreement_lift_iff (η : A.program.Input) (ρ : Store K (declarations A B)) :
  C.InputAgreement (liftInput A B wire η) ρ ↔
    A.program.InputAgreement η (restrictUpstream A B ρ)
inputAgreement_restrictions_iff (η : C.Input) (ρ : Store K (declarations A B)) :
  C.InputAgreement η ρ ↔
    A.program.InputAgreement (restrictInput A B wire η) (restrictUpstream A B ρ)
inputAgreement_glue_iff (η : A.program.Input) (ρA : Store K σA)
  (ρB : Store K σB) :
  C.InputAgreement (liftInput A B wire η) (glueStore A B ρA ρB) ↔
    A.program.InputAgreement η ρA
inputAgreement_boundary_iff (ρA : Store K σA) (ρB : Store K σB) :
  B.program.InputAgreement (boundaryInput A B wire ρA) ρB ↔
    ∀ i : {t : σB.Tensor // B.program.input t = true}, ∀ p,
      ρB ⟨i.val, p⟩ =
        ρA ⟨(wire.matched i).val, (wire.domain i).coord p⟩
boundaryInput_restrictions (ρ : Store K (declarations A B)) :
  B.program.InputAgreement
    (boundaryInput A B wire (restrictUpstream A B ρ))
    (restrictDownstream A B wire ρ)
```

`downstream_input_address` identifies the boundary-matched upstream address
with the downstream input address. `restrictDownstream_glueStore` **requires**
the displayed downstream `InputAgreement`; it does not hold for arbitrary,
inconsistent `ρA`/`ρB`. Conversely, `boundaryInput_restrictions` supplies this
agreement for restrictions of *any* composite store. `glueStore` retains the
upstream summand and downstream **defined** coordinates; it does not duplicate
downstream input tensors. `boundaryInput` supplies `some` for every downstream
input, including an empty coordinate domain, and `none` for noninputs. No tensor
presence is inferred from coordinates.

Validation in this worktree:

- `bash <worktree>/leanncd/scripts/lean-file.sh <worktree>/leanncd experiments/indexed_execution/IndexedComponentModelInputs.lean` — passed without diagnostics.
- `bash <worktree>/.claude/skills/slice-plan/check-snippet.sh <worktree>/leanncd/experiments/indexed_execution/IndexedComponentModelInputs.lean` — `COMPILES`.
- Temporary `#print axioms` checks for `liftInput_restrictInput`,
  `restrictDownstream_glueStore`, `glueStore_restrictions`, and
  `boundaryInput_restrictions` reported only `propext`, `Classical.choice`,
  and `Quot.sound`; print commands were removed. Source search found no
  `sorry`, new `axiom`, `native_decide`, or `unsafe`.
- Controller reports the registered Inputs build/audit passed (255 constants);
  that build was not run by this prototype dispatch.

Scope ends at input/whole-store construction: no model-preservation theorem,
witness bijection, partial-denotation corollary, or fixture suite is claimed.
The single source module is an independently rejectable authoring patch.
Approximately 30–40 assistant/tool turns and 60–100k peak context tokens are
**estimates**, not measured accounting; no supported transcript/token counter
was available. Neither hard cap (50 turns/200k context) is known to have been
breached, but compliance cannot be certified from elapsed time. The reported
2,413 seconds of wall time included the controller's baseline refresh/wait and
does not measure turns or context. No source was staged or committed here.
