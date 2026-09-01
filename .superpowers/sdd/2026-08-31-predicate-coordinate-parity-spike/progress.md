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

## Task 2 — shared nonlinear callback and independent scan rewrites

- `AxiswiseFn.applyIncluded` is the sole callback-based axiswise math choke point.
  Existing source signatures delegate through a UID-map adapter; `none` includes all
  entries. `applyPositionalAxiswise` accepts the Task 1 positional mask separately
  from `RawAxiswisePlan`, evaluates it at each full local coordinate, and delegates
  to the same choke point. `RawAxiswisePlan` and admission are unchanged.
- `ScanUnroll` now recursively substitutes `PredArith`/`BoolExpr` with its own
  `substIdx`. Iversons use actual `sigma`; masks use zero for every source seed,
  actual coordinates for eliminated non-seeded free/freeNorm scan slots, and retain
  other output-axis expressions.
- Observed fixtures:
  - T2-F1 source/adapter: `[0,.4,.6,0,.5,.5]`.
  - T2-F2 source/adapter: `[0,1/(1+e),e/(1+e),0,.5,.5]`; excluded `1000`
    did not enter the maximum.
  - T2-F3 source/adapter/unroll: `[1,3,.25,.75,.25,.75]`; both rewritten
    masks were `(0 = 0)`, with seeded `l` absent.
  - T2-F4 source/unroll: `[1,1,0]`; rewritten Iversons were `(0 = 0)` and
    `(1 = 0)`, with eliminated `l` absent.
  - T2-F5 source/unroll shape `[2,2,2]`, data
    `[0,0,0,0,.25,1,.75,1]`; base masks were `(0 != 0)` and `(1 != 0)`,
    with eliminated `r,c` absent. The template6-derived retained-axis geometry was feasible.

### Single-fault mutation cycles

Each mutation showed its one-line diff, failed the named fixture, was restored,
and its target rerun passed.

- M5 `masked := !included c` → `masked := included c`: T2-F1 failed with
  source/adapter `[1,0,0,1,0,0]`; restore passed.
- M6 softmax maximum included masked values: T2-F2 failed with
  `[0,0,0,0,.5,.5]`; restore passed.
- M7 local mask basis `[i]` → `[l,i]`: T2-F3 adapter failed
  `.affineWidthMismatch 2 1`; restore passed.
- M8 seeded-mask substitution `0` → live `sigma`: T2-F3 independent history
  ended `[...,0,0]` versus source `[..., .25,.75]`; restore passed.
- M9 left Iverson unchanged: T2-F4 independent `[1,1,1]` versus source
  `[1,1,0]`; restore passed.
- M10 left masks unchanged: T2-F3 value parity reached its structural check,
  which failed because live seeded `l` remained. This demonstrates value parity
  alone cannot prove rewriting; restore passed.
- M11 eliminated free scan substitution `sigma` → `0`: T2-F5 lost the
  `r=1,c=0` normalized values (`.25,.75` became zero); restore passed.

Exact Task 2 targeted build (all eight plan targets) exited 0 and completed
successfully (8539 jobs); differential replay remained 3832/3832 and scan
corpus replay remained 17/17. Specification review found factor substitution
uses actual `sigma`, mask seeds take zero precedence, and eliminated free scan
slots use `sigma`; quality review found callback polarity is `included?`,
formulas have one implementation, and the oracle names only scan-free
`evalScheduled` (no checked lowerer, positional evaluator, or checked worker).
Full diff scope was limited to the two temporary production files, two
registered test/oracle files, and this ledger; `git diff --check` passed.
