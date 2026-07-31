import LeanNCD.DSL.Compile
namespace LeanNCD

-- `iter l = 3` parses as a `Decl.iter`, distinct from `axis`.
private def singleIter : TLProgram := tlprog!{ iter l = 3 }
#guard singleIter.decls == [.iter { name := "l", uid := 0, kind := .nat } 3]

-- `iter r = 2, c = 2` parses as two `Decl.iter` entries (comma-list, like `axis`).
private def multiIter : TLProgram := tlprog!{ iter r = 2, c = 2 }
#guard multiIter.decls == [.iter { name := "r", uid := 0, kind := .nat } 2,
                           .iter { name := "c", uid := 0, kind := .nat } 2]

-- `iter` doesn't pollute the tensor-keyed DeclEnv (Step 6) — a program that only reads a
-- tensor with the SAME NAME as an iter-declared axis must still see it as an external input,
-- not find a spurious tensor decl. (`decide (_ ∈ extNames)` matches the codebase's own idiom
-- for `Finset` membership as a `Bool` — see `Structural.lean:667`, not a `.contains` method.)
#guard match (assignUIDs (tlprog!{ iter l = 3
                                    Y[i] := l[i] }) >>= resolveDecls) |>.run 0 with
  | .ok rp _ => decide ("l" ∈ rp.extNames)
  | .error _ _ => false

end LeanNCD
