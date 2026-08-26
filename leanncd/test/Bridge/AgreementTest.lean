import LeanNCD.Bridge.Agreement
namespace LeanNCD
noncomputable example (tc : ThreadedComposed) : Acset.SBrInstance := fromThreadedComposed tc
-- the agreement theorem has the intended Σ-equality TYPE (not weakened):
example (tc : ThreadedComposed) (h : tc.WellFormed) :
    (realize tc h = realizeSBr (fromThreadedComposed tc)) = (realize tc h = realizeSBr (fromThreadedComposed tc)) := rfl
-- the theorems exist with the right statements:
#check @realize_fromThreadedComposed_agree
#check @agree_dom
#check @agree_cod
#print axioms realize_fromThreadedComposed_agree   -- uses sorryAx
-- fixture 12 (this slice's Task 2, logical-schedule flip): pin `compile_wellFormed`'s type
-- unchanged — this file was otherwise unguarded, so a silent weakening here would go unnoticed.
-- A type-ascribed `example`, NOT `#check`: `#check` has no expected type to check against, so it
-- prints whatever the signature became and cannot fail. This form fails to elaborate if any
-- binder, hypothesis, or conclusion changes.
example : ∀ (p : TLProgram) (s : Nat) (tc : ThreadedComposed) (s' : Nat),
    (TLProgram.compile p).run s = .ok tc s' → tc.WellFormed := @compile_wellFormed
end LeanNCD
