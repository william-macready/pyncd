import LeanNCD.Eval.Plan.Check

/-!
# Wave C C2 — `CheckedAssignPlan` construction boundary (compile-time privacy check)

Pins that `checkAssign` and `checkAssignF32` are the only ways to obtain a `CheckedAssignPlan`: the
structure's constructor is `private mk ::`, so anonymous-constructor notation (`⟨...⟩`) cannot be
used to smuggle an unchecked `AssignPlan` past either checker from outside `LeanNCD.Eval.Plan`.

Both constructors are named here deliberately. Since the f32 slice's Task 2 the structure carries a
SECOND field, `storageKind`, set only by those two functions (`.float64` and `.float32`
respectively) — so the boundary now protects not just "this assignment was checked" but "checked
FOR THIS CARRIER", which is what every worker and adapter door gates on. A public constructor would
let a caller relabel binary32 evidence as binary64 and hand it to the Float worker.

Lean has no in-tree "expect this declaration to fail to elaborate" harness, so unlike the rest of
this test suite, the negative half of this check is NOT an automated `#guard` — it is a documented
manual verification. The line below is deliberately commented out; it must never be uncommented in
committed code, because it must NOT compile:

```
-- def smuggled : CheckedAssignPlan := ⟨goodPlan, .float64⟩
```

Manually verified (2026-08-06, for the original one-field shape; RE-verified 2026-09-16 against the
current two-field shape) by uncommenting that exact line (with a `goodPlan : AssignPlan` in scope)
and running, from `leanncd/`:

```
lake env lean test/Eval/Plan/CheckedPrivacyTest.lean
```

Observed failure, exit code 1, literal captured stdout/stderr (2026-09-16 run):

```
test/Eval/Plan/CheckedPrivacyTest.lean:83:36: error: Invalid `⟨...⟩` notation: Constructor for `LeanNCD.Eval.Plan.CheckedAssignPlan` is marked as private
```

Note what this re-verification rules out specifically: adding a field did NOT turn the anonymous
constructor public, and supplying the storage kind explicitly is not a way around `private mk ::`.
The line was re-commented immediately after confirming the failure; this file compiles clean with
it commented out, exercising only the positive half (normal construction via each checker works).
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
  { contextShape := #[], destinationSlot := 2, outputShape := #[4]
  , terms := #[{ iterationShape := #[4, 3], contextPos := #[], outputPos := #[0], reductionPos := #[1]
               , factors := #[.read readA, .read readB] }]
  , algebra := admittedAlgebra }

-- normal construction via the binary64 checker succeeds, and records `.float64`
#guard (checkAssign sigs goodPlan).toOption.isSome
#guard (checkAssign sigs goodPlan).toOption.map (·.storageKind) == some LeanNCD.StorageKind.float64

-- ... and via the binary32 checker, over the same shapes retagged f32, recording `.float32`
def f32Sigs : Array TensorSignature :=
  #[ { shape := #[4], dtype := .f32 }
   , { shape := #[3], dtype := .f32 }
   , { shape := #[4], dtype := .f32 } ]

def f32Plan : AssignPlan := { goodPlan with algebra := admittedAlgebraF32 }

#guard (checkAssignF32 f32Sigs f32Plan).toOption.isSome
#guard (checkAssignF32 f32Sigs f32Plan).toOption.map (·.storageKind)
  == some LeanNCD.StorageKind.float32

-- must NOT compile: def smuggled : CheckedAssignPlan := ⟨goodPlan, .float64⟩

end LeanNCD.Eval.Plan.CheckedPrivacyTest
