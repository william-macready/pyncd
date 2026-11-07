# Complete-model partial denotation prototype

Source: `leanncd/experiments/indexed_execution/IndexedComponentModelDenotation.lean`.
This non-default experiment imports `IndexedComponentModelWitnesses` and uses
the whole-store restriction/gluing theorem, not an execution order or rank.

## Assumptions and exported statements

`AtMostOneModels A` means that for **every validated** `A.program.Input`,
any two complete stores satisfying `A.program.Models RationalReference.ops`
are equal. It does **not** assert that a model exists. Both component
assumptions are explicit in each public corollary below.

Exact public signatures, in the `IndexedComponentComposition` namespace with
implicit finite/decidable tensor declarations and explicit `A`, `B`, `wire`:

```text
def AtMostOneModels (A : MatchedComponent σA) : Prop :=
  ∀ (η : A.program.Input) (ρ ρ' : Store K σA),
    A.program.Models RationalReference.ops η ρ →
    A.program.Models RationalReference.ops η ρ' → ρ = ρ'

theorem admInput_lift_iff (hA : AtMostOneModels A)
    (hB : AtMostOneModels B) (η : A.program.Input) :
    (program A B wire).AdmInput RationalReference.ops
      (liftInput A B wire η) ↔
      ∃ hAdmA : A.program.AdmInput RationalReference.ops η,
        B.program.AdmInput RationalReference.ops
          (boundaryFromOutput A B wire
            (A.program.denotation RationalReference.ops η hAdmA))

theorem admInput_restrictions_iff (hA : AtMostOneModels A)
    (hB : AtMostOneModels B) (η : (program A B wire).Input) :
    (program A B wire).AdmInput RationalReference.ops η ↔
      ∃ hAdmA : A.program.AdmInput RationalReference.ops
          (restrictInput A B wire η),
        B.program.AdmInput RationalReference.ops
          (boundaryFromOutput A B wire
            (A.program.denotation RationalReference.ops
              (restrictInput A B wire η) hAdmA))

theorem denotation_successive (hA : AtMostOneModels A)
    (hB : AtMostOneModels B) (η : (program A B wire).Input)
    (hAdmC : (program A B wire).AdmInput RationalReference.ops η) :
    ∃ hAdmA : A.program.AdmInput RationalReference.ops
        (restrictInput A B wire η),
      ∃ hAdmB : B.program.AdmInput RationalReference.ops
        (boundaryFromOutput A B wire
          (A.program.denotation RationalReference.ops
            (restrictInput A B wire η) hAdmA)),
        (program A B wire).denotation RationalReference.ops η hAdmC =
          liftOutput A B wire
            (B.program.denotation RationalReference.ops
              (boundaryFromOutput A B wire
                (A.program.denotation RationalReference.ops
                  (restrictInput A B wire η) hAdmA)) hAdmB)
```

In particular, `admInput_restrictions_iff` ranges over **every validated
composite input**, not just lifted inputs.

All three declarations use `RationalReference.ops`. The intermediate input
is a `B.program.Input`, built by the wire's matched output tensor and
`wire.domain` coordinate transport. Every downstream input is present,
including tensors with no coordinates; noninput bindings are `none`.
`liftOutput` respects composite
output-role metadata, including empty outputs. No value is asserted outside
the common admissibility domain, and neither component at-most-one premise
claims existence. The converse domain proof builds a complete composite
store from both component models. The forward proof retains the whole
upstream store through uniqueness, then projects its boundary; it never
selects one upstream solution from several. Proof parameters for denotation
are propositions, so changing a proof does not change the result.

## Verification

After the controller reported the Inputs and Witnesses dependencies built and
ready, both source-file typechecking and the exact source-copy check passed
without warnings:

`bash /Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-model/leanncd/scripts/lean-file.sh /Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-model/leanncd experiments/indexed_execution/IndexedComponentModelDenotation.lean`

`bash /Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-model/.claude/skills/slice-plan/check-snippet.sh /Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-model/leanncd/experiments/indexed_execution/IndexedComponentModelDenotation.lean`

The three `#print axioms` audits (lifted domain, unrestricted domain,
unrestricted values) each returned exactly `[propext, Classical.choice,
Quot.sound]`. No full Lake build or mutation test was run by this work item;
the controller coordinates builds and integration. No generic model
composition theorem, rank certificate, operational phase, or fixture change
was introduced. Remaining integration: controller-owned target registration,
whole-target build, staging and committing; this agent did not stage or
commit. Work stayed within the 40-turn target and 50-turn/200k hard checkpoint;
there was no budget breach.
