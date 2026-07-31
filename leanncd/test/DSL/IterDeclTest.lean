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

-- Both spacings converge: `l +1` and `l + 1` compile identically once `l` is declared `iter`,
-- and BOTH now produce a genuine `.scan` step (not a degenerate one). `=` (not `==`) matches
-- AcsetCodecTest.lean's own convention for comparing two `ThreadedComposed` values.
#guard
  let tcA := tl!{ iter l = 3
                  S[j, 0]   := X[j]
                  S[j, l +1] := S[j, l] }
  let tcB := tl!{ iter l = 3
                  S[j, 0]    := X[j]
                  S[j, l + 1] := S[j, l] }
  tcA = tcB

-- An axis used at an offset-1 LHS shift but NOT declared `iter` is a compile error, not a
-- silently-different AST — regardless of which spacing was used.
run_cmd
  match TLProgram.compile (tlprog!{ tensor X(j)
                                     S[j, 0]    := X[j]
                                     S[j, l +1] := S[j, l] }) |>.run 0 with
  | .error (.scanAxisNotIter "l") _ => pure ()
  | .error e _ => throwError s!"IterDeclTest: wrong CompileError: {repr e}"
  | .ok _ _    => throwError "IterDeclTest: expected scanAxisNotIter, compile succeeded"
run_cmd
  match TLProgram.compile (tlprog!{ tensor X(j)
                                     S[j, 0]     := X[j]
                                     S[j, l + 1] := S[j, l] }) |>.run 0 with
  | .error (.scanAxisNotIter "l") _ => pure ()
  | .error e _ => throwError s!"IterDeclTest: wrong CompileError: {repr e}"
  | .ok _ _    => throwError "IterDeclTest: expected scanAxisNotIter, compile succeeded"

end LeanNCD
