import Lean
import LeanNCD.Semantics

/-!
# Axiom audit for `LeanNCD.Semantics`

The proof-status tables in `papers/semantics/` call theorems "proved". A `sorry`,
a `native_decide`, or a new `axiom` would still build (with a warning) and leave
those tables silently wrong. This module fails the build instead.

`#audit_axioms ns` collects every theorem and definition whose name lies under
`ns`, and checks that the axioms each one reaches are within `allowedAxioms`.
Because it covers the whole namespace there is no list to keep in sync with the
docs: a new Semantics declaration is audited automatically.

Imported declarations use Lean's precomputed axiom sets, so the audit is cheap.
-/

open Lean Elab Command

namespace AxiomAudit

/-- The only axioms a `LeanNCD.Semantics` declaration may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Theorems and definitions under `ns`, in a deterministic order. -/
def audited (env : Environment) (ns : Name) : Array Name :=
  let names := env.constants.fold (init := #[]) fun acc n ci =>
    if ns.isPrefixOf n && (ci.isTheorem || ci.isDefinition) then acc.push n else acc
  names.qsort Name.lt

/-- Axioms outside the allowed set. -/
def forbidden (axs : Array Name) : Array Name :=
  axs.filter fun a => !allowedAxioms.contains a

elab "#audit_axioms " ns:ident : command => do
  let names := audited (← getEnv) ns.getId
  let mut offenders : Array String := #[]
  for n in names do
    let bad := forbidden (← collectAxioms n)
    unless bad.isEmpty do
      offenders := offenders.push s!"{n} uses {bad}"
  if offenders.isEmpty then
    logInfo m!"axiom audit: {names.size} constants under {ns.getId} use only standard axioms"
  else
    logErrorAt ns m!"axiom audit failed under {ns.getId}: {"; ".intercalate (offenders.toList.take 20)}"

end AxiomAudit

/-! ## Self-test: the audit rejects a non-standard axiom. -/

namespace AxiomAudit.Demo

axiom demoBad : False

theorem demoUsesBad : (1 : Nat) = 2 := demoBad.elim

theorem demoClean : (1 : Nat) + 1 = 2 := rfl

end AxiomAudit.Demo

/-- error: axiom audit failed under AxiomAudit.Demo: AxiomAudit.Demo.demoUsesBad uses #[AxiomAudit.Demo.demoBad] -/
#guard_msgs (error) in
#audit_axioms AxiomAudit.Demo

/-! ## The audit proper. -/

#audit_axioms LeanNCD.Semantics
