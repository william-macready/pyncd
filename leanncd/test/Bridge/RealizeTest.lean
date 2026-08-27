-- test/Bridge/RealizeTest.lean
import LeanNCD.Bridge.Realize
import LeanNCD.DSL.Compile
namespace LeanNCD
-- typecheck (noncomputable ⇒ no #eval):
noncomputable example (a : AxisP) : Axis := realizeAxis a
noncomputable example (s : StObjP) : StObj := realizeStObj s
noncomputable example (m : StMatP) (d c : StObj) : StMat d c := realizeStMat m d c
-- realizeAxis / realizeStObj must be sorry-FREE (no `sorryAx` in their axiom list):
#print axioms realizeAxis
#print axioms realizeStObj
-- intToCoeff is now SORRY-FREE (Coeff = MvPolynomial String ℤ is signed):
#print axioms intToCoeff
-- WEAVE realizations + dependent realizeBrBaseP (Task 2):
noncomputable example (w : WeaveShapeP) : WeaveShape := realizeWeaveShape w
noncomputable example (b : BrBaseP) : Σ (dom cod : BrObj), BrBase dom cod := realizeBrBaseP b
#print axioms realizeWeaveShape   -- must be sorry-FREE
#print axioms realizeBrBaseP      -- now SORRY-FREE (realizeStMat + intToCoeff are sorry-free)
-- COMPOSITE realize: the threaded DAG → ONE Br morphism. Now SORRY-FREE under `WellFormed`
-- (the body is the `interpUpto`/`finalPiece` fold). `#print axioms` must NOT list `sorryAx`.
noncomputable example (tc : ThreadedComposed) (h : tc.WellFormed) :
    Σ (dom cod : BrObj), BrMorph dom cod := realize tc h
#print axioms realize    -- [propext, Classical.choice, Quot.sound] — sorryAx GONE

-- BEHAVIOR: `realize`'s `dom`/`cod` are `realizeDom`/`codObj` (independent of the proof `h`), so they
-- are tested directly. Both are noncomputable (realized `ArrayType`); only their LENGTH is checked.
private def mkStep (ins outs : Nat) : BrBaseP :=
  { op := .contract, degree := [],
    inputWeaves := List.replicate ins [], outputWeaves := List.replicate outs [],
    reindexings := [] }

-- matmul-shaped: 1 step, 2 external inputs (slots 0,1), 1 output. nExternal = 2.
private def tcMatmul : ThreadedComposed :=
  { steps := [mkStep 2 1], routing := [[.external 0, .external 1]], nExternal := 2 }
#guard tcMatmul.externalPort 0 == some (0, 0)
#guard tcMatmul.externalPort 1 == some (0, 1)
#guard tcMatmul.wellFormedDom
example : (realizeDom tcMatmul).length = 2 := by rfl     -- dom: one entry per external slot
example : tcMatmul.codObj.length = 1 := by rfl           -- cod: last step's outputs

-- two-layer net: steps [H ⟵ W1,X ; Y ⟵ W2,H]. Externals W1,X,W2 = slots 0,1,2; H internal.
private def tc2Layer : ThreadedComposed :=
  { steps := [mkStep 2 1, mkStep 2 1],
    routing := [[.external 0, .external 1], [.external 2, .internal 0 0]], nExternal := 3 }
#guard tc2Layer.externalPort 0 == some (0, 0)
#guard tc2Layer.externalPort 1 == some (0, 1)
#guard tc2Layer.externalPort 2 == some (1, 0)   -- W2 consumed at step 1, input 0
#guard tc2Layer.wellFormedDom
example : (realizeDom tc2Layer).length = 3 := by rfl

-- empty program ⇒ empty dom and cod:
example : realizeDom { steps := [], routing := [], nExternal := 0 } = [] := by rfl
example : ThreadedComposed.codObj { steps := [], routing := [], nExternal := 0 } = [] := by rfl

-- NEGATIVE: one external slot read at two different ranks ⇒ not well-formed. One step, two inputs
-- both reading external slot 0: input 0 at rank 1 (`[.fixed _]`), input 1 at rank 0 (`[]`).
private def tcBadRank : ThreadedComposed :=
  { steps := [{ op := .contract, degree := [],
                inputWeaves := [[.fixed default], []], outputWeaves := [[]], reindexings := [] }],
    routing := [[.external 0, .external 0]], nExternal := 1 }
#guard ! tcBadRank.wellFormedDom

-- COMBINATORIAL PLAN (`wirePlan`): per-step selections + final selection, by the §4 liveness fold.
-- matmul: one step reading both externals, no carry ⇒ sel [0,1]; final picks the sole output.
#guard (tcMatmul.wirePlan.1.map (·.sel)) == [[0, 1]]
#guard tcMatmul.wirePlan.2.2 == [0]
-- two-layer: step0 reads W1,X and carries W2 ⇒ [0,1,2]; step1 reads W2,H (swapped in pool) ⇒ [1,0].
#guard (tc2Layer.wirePlan.1.map (·.sel)) == [[0, 1, 2], [1, 0]]
#guard tc2Layer.wirePlan.2.2 == [0]
-- fan-out: ext0 read by BOTH steps. step0 ⇒ copy (reads pos 0, carries pos 0) = [0,0]; step1 ⇒ [1]
-- (reads ext0 at pool pos 1, DROPPING step0's now-dead output) — exercising copy and discard.
private def tcFan : ThreadedComposed :=
  { steps := [mkStep 1 1, mkStep 1 1], routing := [[.external 0], [.external 0]], nExternal := 1 }
#guard (tcFan.wirePlan.1.map (·.sel)) == [[0, 0], [1]]
#guard tcFan.wirePlan.2.2 == [0]

/-! ## Routed nonlinear programs (T2 Task 3, B5-B8)

Same shaped surrogates as above, over `tl!{...}`-routed `ThreadedComposed` values instead of
hand-built ones -- `realize` stays noncomputable and unevaluated; every value below was OBSERVED
from a real run and transcribed, not predicted. -/

-- B5: routed ReLU (`H[i] := relu(W[i, j] · x[j])`) -- one logical statement, physicalized into a
-- private producer/consumer pair (2 physical steps). Clone of `tcMatmul`'s assertion block.
private def tcB5 : ThreadedComposed := tl!{ H[i] := relu(W[i, j] · x[j]) }
#guard tcB5.externalPort 0 == some (0, 0)
#guard tcB5.externalPort 1 == some (0, 1)
#guard tcB5.wellFormedDom
example : (realizeDom tcB5).length = 2 := by rfl   -- dom: nExternal = 2 (W, x)
example : tcB5.codObj.length = 1 := by rfl         -- cod: the consumer's one output (H)

-- B6: the same routed ReLU's `wirePlan`. Clone of `tc2Layer`'s `wirePlan` block: step 0 (the
-- private producer) reads both externals; step 1 (the consumer) reads step 0's sole output.
example : (tcB5.wirePlan.1.map (·.sel)) = [[0, 1], [0]] := by rfl
example : tcB5.wirePlan.2.2 = [0] := by rfl

-- B7: routed nonlinear CHAIN (`RouteWeaveTest`'s fixture-3 shape) -- the downstream read must wire
-- to the fragment's EXIT (the consumer, physical step 1), never its private producer (step 0).
-- `externalPort 2` (V) resolves to step 2, and the chain's 3rd physical step's wirePlan selection
-- length is 3 (V plus the two live carries from steps 0-1), confirming the exit, not the entry, is
-- what the downstream statement actually wires to.
private def tcB7 : ThreadedComposed := tl!{
  H[i] := relu(W[i, j] · x[j])
  Z[k] := H[i] · V[i, k]
}
#guard tcB7.externalPort 0 == some (0, 0)
#guard tcB7.externalPort 1 == some (0, 1)
#guard tcB7.externalPort 2 == some (2, 1)
#guard tcB7.wellFormedDom
example : (realizeDom tcB7).length = 3 := by rfl   -- dom: nExternal = 3 (W, x, V)
example : tcB7.codObj.length = 1 := by rfl         -- cod: Z, the last step's sole output
example : (tcB7.wirePlan.1.map (·.sel)) = [[0, 1, 2], [0, 1], [0, 1]] := by rfl
example : tcB7.wirePlan.2.2 = [0] := by rfl

-- B8: routed opaque SCAN (B4's single-ReLU-recurrence source) -- the whole scan node routes as
-- ONE opaque physical step (class 8/9: copied verbatim, the split lives entirely inside it,
-- invisible to this categorical presentation).
private def tcB8 : ThreadedComposed := tl!{
  iter l = 3
  G[j, 0]    := X[j]
  G[j, l +1] := relu(G[j, l] · W_G[j, k]) }
#guard tcB8.steps.length == 1
#guard tcB8.externalPort 0 == some (0, 0)
#guard tcB8.externalPort 1 == some (0, 1)
#guard tcB8.wellFormedDom
example : (realizeDom tcB8).length = 2 := by rfl   -- dom: nExternal = 2 (X, W_G)
example : tcB8.codObj.length = 1 := by rfl         -- cod: the scan's one published state (G)
example : (tcB8.wirePlan.1.map (·.sel)) = [[0, 1]] := by rfl
example : tcB8.wirePlan.2.2 = [0] := by rfl

end LeanNCD
