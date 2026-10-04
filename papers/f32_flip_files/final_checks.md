# Slice-2 plan: two controller checks (2026-10-04, before pushing the branch)

Both run by the controller, not an agent.

1. **Fixture mutation.** With the flip applied, `dtypeOfDecl`'s undeclared-name arm (`none`) was temporarily
   reverted from `.f32` to `.f64` and `Eval.Plan.DefaultF32Test` was rebuilt on its own. It FAILED with the
   fixture's own message `unannotated ≠ explicit f32 on 10 variant(s)` (and no other error). The line was
   restored and the tree was verified identical to the committed tip. So `DefaultF32Test` can fail, and it
   catches the silent mode (undeclared programs accepted as binary64 plans from binary32 buffers).
   Before the mutation, the fixture's targeted build with the flip was green (8520 jobs, 0 failures).
2. **Patch dry-run on clean main 574a633** (detached throwaway worktree, since removed):
   `git am` of `patches/0001`..`0007` applied cleanly in order, and `git apply --check` of
   `patches/0008-...DefaultF32Test-fixture.patch` passed. So Task 1's patch sequence is sound onto main.
   Caveat: the plan's Task 1 first action restores a subset of files from this branch before applying
   (patches 0001 and 0007 create the log, RESULTS.md and plan_modules.md, so those are NOT restored first);
   this dry-run started from bare main, which models that.

Still unverified: the two extra probes (a),(c) planned for the fixture (corpus re-pin to 12) were never built.
