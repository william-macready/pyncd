import LeanNCD.Eval.Plan.Check

/-!
# Wave C C2 — `CheckedAssignPlan` construction boundary (compile-time privacy check)

Pins that `checkAssign` is the only way to obtain a `CheckedAssignPlan`: the structure's
constructor is `private mk ::`, so anonymous-constructor notation (`⟨...⟩`) cannot be used to
smuggle an unchecked `AssignPlan` past the checker from outside `LeanNCD.Eval.Plan`.

Lean has no in-tree "expect this declaration to fail to elaborate" harness, so unlike the rest of
this test suite, the negative half of this check is NOT an automated `#guard` — it is a documented
manual verification. The line below is deliberately commented out; it must never be uncommented in
committed code, because it must NOT compile:

```
-- def smuggled : CheckedAssignPlan := ⟨goodPlan⟩
```

Manually verified (2026-08-06) by uncommenting that exact line (with a `goodPlan : AssignPlan` in
scope) and running, from `leanncd/`:

```
lake env lean test/Eval/Plan/CheckedPrivacyTest.lean
```

Observed failure, exit code 1, literal captured stdout/stderr:

```
test/Eval/Plan/CheckedPrivacyTest.lean:56:36: error: Invalid `⟨...⟩` notation: Constructor for `LeanNCD.Eval.Plan.CheckedAssignPlan` is marked as private
```

The line was re-commented immediately after confirming the failure; this file compiles clean with
it commented out, exercising only the positive half (normal construction via `checkAssign` works).
-/

namespace LeanNCD.Eval.Plan.CheckedPrivacyTest
open LeanNCD.Eval.Plan

def sigs : Array TensorSignature :=
  #[ { shape := #[4], dtype := .f64 }
   , { shape := #[3], dtype := .f64 }
   , { shape := #[4], dtype := .f64 } ]

def readA : ReadPlan :=
  { sourceSlot := 0, map := { coeffs := #[#[1, 0]], bias := #[0] }
  , sourceShape := #[4], oobPolicy := .zeroPad }

def readB : ReadPlan :=
  { sourceSlot := 1, map := { coeffs := #[#[0, 1]], bias := #[0] }
  , sourceShape := #[3], oobPolicy := .zeroPad }

def goodPlan : AssignPlan :=
  { destinationSlot := 2, outputShape := #[4]
  , terms := #[{ iterationShape := #[4, 3], outputPos := #[0], reductionPos := #[1]
               , factors := #[readA, readB] }]
  , algebra := admittedAlgebra }

-- normal construction via the checker succeeds
#guard (checkAssign sigs goodPlan).toOption.isSome

-- must NOT compile: def smuggled : CheckedAssignPlan := ⟨goodPlan⟩

end LeanNCD.Eval.Plan.CheckedPrivacyTest
