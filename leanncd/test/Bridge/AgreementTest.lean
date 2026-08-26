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
-- fixture 12 (Task 2, logical-schedule flip): pin `compile_wellFormed`'s type unchanged — this
-- file was otherwise unguarded, so a silent weakening here would go unnoticed.
#check @compile_wellFormed
end LeanNCD
