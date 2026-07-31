import LeanNCD.DSL.Compile
namespace LeanNCD

-- `iter l = 3` parses as a `Decl.iter`, distinct from `axis`.
private def singleIter : TLProgram := tlprog!{ iter l = 3 }
#guard singleIter.decls == [.iter { name := "l", uid := 0, kind := .nat } 3]

-- `iter r = 2, c = 2` parses as two `Decl.iter` entries (comma-list, like `axis`).
private def multiIter : TLProgram := tlprog!{ iter r = 2, c = 2 }
#guard multiIter.decls == [.iter { name := "r", uid := 0, kind := .nat } 2,
                           .iter { name := "c", uid := 0, kind := .nat } 2]

-- `iter` doesn't pollute the tensor-keyed DeclEnv (Step 6) — the `.iter _ _ => m` arm at
-- Structural.lean:154 ensures iter-declared axes don't leak into the env. This guard directly
-- verifies that "l" is NOT in env (not just in extNames, which is computed independently
-- from env and wouldn't catch an env-pollution bug).
#guard match (assignUIDs (tlprog!{ iter l = 3
                                    Y[i] := l[i] }) >>= resolveDecls) |>.run 0 with
  | .ok rp _ => !rp.env.contains "l"
  | .error _ _ => false

end LeanNCD
