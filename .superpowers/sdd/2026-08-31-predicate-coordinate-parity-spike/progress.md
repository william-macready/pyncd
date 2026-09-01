# SDD ledger — plan: docs/superpowers/plans/2026-08-31-predicate-coordinate-parity-spike.md

Worktree: /Users/williammacready/code/python/pyncd.worktrees/predicate-coordinate-parity-spike
Branch: agents/predicate-coordinate-parity-spike (fast-forwarded to local main @ 8f8981e)
.lake synced from /Users/williammacready/code/python/pyncd (8101/8094 mathlib oleans, no cold build needed)
Prepared by: .claude/skills/new-slice/prepare-worktree.sh

## Task 1 — positional predicate core

- Implemented UID-free `PosAffine`/`PosPredArith`/`PosBoolExpr`, independent positional evaluation,
  and explicit factor/mask lowering wrappers. `substitutePins` remains private; `TermPlan.factors`
  and source admission are unchanged. Width mismatch is
  `PosPredicateError.affineWidthMismatch coeffCount coordinateCount`.
- Temporarily exposed only `DifferentialTest.sameNameIter`, `sameNameFree`, and
  `sameAxisNameSched`, so T1-F4 uses the exact donor.
- Fixtures observed:
  - T1-F1: factor basis/residual `[1101,1102]`; positional/source tensor
    `[1,0,0,0,1,0,0,0,1]`, shape `[3,3]`.
  - T1-F2: basis `[1201,1202]` (`[i,j]`); predicate values at `[0,1]`/`[1,0]` were
    `false`/`true`; RC3 source tensor `[1,3,6]`.
  - T1-F3: last factor remained Iverson; basis `[1,2,3]` (`[i,j,k]`); values at
    `[0,0,1]`/`[0,1,0]` were `true`/`false`.
  - T1-F4: exact same-name UIDs yielded basis `[3101,3102]` and rows
    `#[1,0]`/`#[0,1]`; value at `[context l, output l]=[0,1]` was `true`.
  - T1-F5: initial/residual basis `[axR.uid]`/`[]`; nested affine leaves became
    `([],1)` and `([],-1)`, constant `([],1)`; value at `#[]` was `true`.
  - Mask policy: local basis `[i]`, absent non-seeded `j` lowered to zero; at local
    coordinate `2`, `[i=j]` was `false`. Width `2` against coordinate width `1`
    returned `.affineWidthMismatch 2 1`.

### Single-fault mutation cycles

Each cycle used
`cd leanncd && "$HOME/.elan/bin/lake" build Eval.Plan.PredicateCoordinateSpikeTest`;
the failing command exited 1, then the mutation was restored and the identical command exited 0.

- M1 diff: factor basis `context ++ output ++ contracted` →
  `context ++ contracted ++ output`. T1-F2 failed with `basis: [1202, 1201]`
  (T1-F3 also reported `[2,3,1]`); restore passed.
- M2 diff: append `contracted.reverse`. T1-F3 failed with `basis: [1, 3, 2]`;
  restore passed.
- M3 diff: replace UID basis lookup with first matching axis name from the exact term donor.
  T1-F4 failed with `UID basis: [3102, 3102]`; restore passed.
- M4 diff: replace
  `substitutePins pins basis (idxToRow basis idx)` with `idxToRow basis idx`.
  T1-F5 failed structurally with rows `#[1],0`, `#[1],-2`, and `#[0],1`;
  restore passed.

Planned targeted command:
`cd leanncd && "$HOME/.elan/bin/lake" build LeanNCD.Eval.Plan.Kernel
LeanNCD.Eval.Plan.Compile LeanNCD.Eval.Plan.Dense
Eval.Plan.PredicateCoordinateSpikeTest Eval.Plan.DifferentialTest`
exited 0; build completed successfully (8536 jobs). Differential sweeps remained
3832/3832 accepted and scan corpus 17/17 accepted.
