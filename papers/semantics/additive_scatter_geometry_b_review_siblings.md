# Scatter geometry slice B: review lens 1 (siblings a diff cannot show)

Reviewer: lens 1. Code audited: PROTO worktree `worktree-proto-scatter-geometry-b` tip `2ad72b7c` (the code as
the plan would leave it). Plan package: `main` `5944c140`. Probes: untracked
`leanncd/spikes/ReviewL1_probe.lean` and `ReviewL1_name.lean` (deleted at the end), importing the built
`Eval.Plan.ScatterGeometryTest` donors (`convOf`, `sumSlot`, `convTwo`, `convBoxed`, `cells`, `prepCause`,
`sourceError`, `ref64`/`run64`/`run32`). Inputs `A = [1,2,3,4]` (`|a| = 4`), `B = [1,10,100]` (`|b| = 3`).
Probe helper `rep` prints: `compileToScheduled` | `validateScheduled` | `prepareEvalPlan` | `TLProgram.compile`
(route) | reference `evalScheduled` | `cells` (ref f64, checked f64, checked f32 bits). Note: `validate-ok` and
`prep-ok` are printed when `compileToScheduled` already failed (the helpers return `none`), so read the first
column first.

## Findings

### L1-1 (P2) A boxed single writer that mixes a constant/multi-axis slot with an identity slot keeps the derived shape; with two writers the same destination publishes the declared shape

- Identifier: D5 test in `boxedSingleGroups` @ `LeanNCD/DSL/Pipeline/Collect.lean:154-158`
  (`!(sourceUIDs ls).any declUIDs.contains`), mirrored by `declaredShapeWins` @
  `Semantics/Source/Differential.lean:207-211` and test `singleBoxed` @ `test/Semantics/OracleSortRules.lean:303`.
- Scenario: the canonical constant use, a ROW write. `tensor S(k, b)`, `axis k = 8`, `axis b = 3` (every
  declared axis pinned), `S[=3, b] := B[b]`. The `b` slot is the identity over its own declared axis, so D5
  fires and the writer is not boxed. Observed:
  - one writer `row [c 3]`: `sched-ok | validate-ok | prep-ok | route-ok | ref-ok | ([4, 3] ..., [4, 3] ..., [4, 3] ...)`, `groupsOf []`
  - two writers `row [c 3, c 5]`: `... | route-err routeUnsupportedMultiWriter "S" | ref-ok | ([8, 3] ..., [8, 3] ..., [8, 3] ...)`
  So the published shape of `S` depends on the writer COUNT (`[4,3]` vs `[8,3]`) for the same pinned
  declaration, which is exactly what B5c set out to remove ("a pinned declaration decides the published
  shape for every writer count", `boxedSingleGroups` docstring). All three legs agree and the oracle agrees
  (`declaredShapeWins` is false, so it raises `scatterExtentOverridesDeclared`: a `known:extent`, not a
  false parity), so no wrong value; the defect is the rule and the plan's claim.
- Plan claim affected: B-D3 "A single constant or multi-axis writer into a destination declared with every
  axis pinned now publishes the DECLARED shape" is false for any writer with a second, identity slot over a
  declared axis. The "D5 unchanged" clause technically covers it, but the section 5 table has no
  constant-plus-identity cell (only "D5 with multi-axis: R (F5)", a single-slot case) and no fixture pins it.
  The single-axis analogue (`S[2*a + 1, b]` into a larger `k`) is pre-existing since B5c; slice B makes it
  the default outcome of `S[=n, j]`, which is new surface (`S[=3]` syntax, T3).
- Why tests miss it: F4/F5/`constOne`/`fI1`/`fI2`/`fMask` are rank-1 or have no identity slot; D5 fixtures
  (F5, B5c) use the source axis inside the affine slot itself.
- Proposed fix: decide, then either (a) narrow D5 to declared axes that occur in a non-identity position
  (an affine slot, or a free slot whose declared position differs), mirrored in `declaredShapeWins` and
  `singleBoxed`, plus one fixture each for one/two row writers (about 1 dispatch, Direct path, with
  re-pins if any corpus program moves); or (b) keep the rule and correct the B-D3 sentence and the
  `boxedSingleGroups` docstring to say a writer with any identity slot keeps the derived shape, and add the
  `row` pair as a pinned observation (about 0.3). This is a design call (D5 is BINDING); controller decides.

### L1-2 (P3) `route` (`TLProgram.compile`) accepts boxed single writers that native refuses, now also for constant and multi-axis writers

- Identifier: `route` @ `LeanNCD/DSL/Pipeline/Lowering.lean:594-599` calls `desugarMultiWriters logical`
  with the default `pinned := {}`, so `boxedSingleGroups` is empty there and the shape-obligation check
  never runs on the route path.
- Observed: `S[=4] := A[a]` into `axis k = 4`: native `prep-err shape multi-writer S: writer 1, dimension 0:
  extent 5 exceeds declared box extent 4`, reference the same error, route `route-ok`. `convBoxed`: native
  publishes `[8]`, route `route-ok` (the routed diagram never sees the box). Pre-existing control:
  single-axis `S[2*a]` into `axis k = 4`: native `writerExtentExceedsBox` (`extent 8 exceeds ... 4`), route
  `route-ok`, so this is the documented B5c behaviour (`DSL/AGENTS.md`: route "does not see single boxed
  writers") extended to the new forms.
- Why it matters little: route is documented as not checking boxes; JAX refuses every scatter step
  categorically (`experiments/jax_bridge/EvalPlanCodegen.lean:352,561,767`, `unsupportedStep`). Plan section
  2 says route is "unchanged", which is true; it does not say route now accepts programs native refuses.
- Fix: one sentence in the plan's "Does NOT do" table (or the T5 docs patch) naming it; no code (about 0.1).

### L1-3 (P3) Zero-coefficient degenerate slots: an all-zero multi-axis slot is a range error, and a zero-coefficient declared axis triggers D5

- Identifier: `LHSSlot.outExtent` @ `DSL/Ast.lean:508-531` (no nonzero term falls to the `legacy` arm) and
  the D5 `sourceUIDs` (keeps zero-coefficient UIDs via `idxAffineForm`).
- Observed:
  - `S[0*a + 0*b + 3] := A[a]*B[b]` (surface-spellable per B-D4) into a box `k = 8`, alone or grouped with
    `S[=3]`: native `prep-err shape scatter S#1: dimension 0: writes span [3, 3] but the destination extent
    is 3`, reference `write to output coord [3] ... is outside the destination extent`; unboxed single the
    same. The constant `S[=3]` it equals gets extent 4. Loud in every leg, not silent.
  - `tensor S(a)` (`a = 4` pinned) with `S[0*a + b] := A[a]*B[b]`: shape `[3]`, `groupsOf []` (D5 fires on
    the zero-coefficient `a`); the same writer into `S(k)`, `k = 4`: shape `[4]` (boxed). The
    zero-coefficient term changes boxing although it does not change the image.
- Plan cell: section 2 parks degenerate-slot validation for `a + a` and `0*a + b` only; neither sub-case above
  is named. Oracle and production agree on both (same `idxAffineForm`), so no differential error.
- Fix: name both in the parked degenerate-slot row (no extra cost; that row's validation would refuse them).

## Unconfirmed

- None of substance. The route diagram's published shape for `convBoxed` was not inspected (only that
  `TLProgram.compile` succeeds); I did not decode the `ThreadedComposed`.

## Checked and clean (with evidence)

- Rank-0 destination (plan section 5 last row, asked to observe): production refuses at
  `compileToScheduled` with `rankMismatch "S" 0 1` for `S[=3]`, for `S[a+b]`, and for two `S[=3]` writers
  (route the same error). The source oracle refuses it too: `admitAffineOutput` throws `.rank` when
  `forms.length != sig.length` (`Semantics/Source/Admission.lean:828-830`). So the vacuous
  `declaredShapeWins` on rank 0 is unreachable with a non-empty write, and a rank-0 empty write is not a
  `nonBareWrite`. The cell can be marked R (refused at compile), not S.
- Zero coefficient in a multi-writer GROUP (asked to observe): two `S[0*a + b] := A[a]*B[b]` writers,
  unboxed `k` unpinned: `[20, 200, 2000]` in ref f64, checked f64, checked f32 (bit-equal); boxed `k = 8`:
  `[20, 200, 2000, 0, 0, 0, 0, 0]` all legs; bare `S[a]` plus `S[0*a + b] := B[b]` over declared `S(a)`:
  `[11, 102, 1003, 4]` all legs. Route refuses the groups (`routeUnsupportedMultiWriter`).
- Undeclared destination whose writers are only `S[a+b]` and `S[=2]`: `validateScheduled` gives
  `multiWriterNeedsDeclaredShape "S"`, reference `compile failed: ... multiWriterNeedsDeclaredShape "S"`,
  route the same. Sane message.
- Constant plus multi-axis writer into a rank-2 box: `rankMismatch "S" 2 1` at `compileToScheduled`.
- Synthetic unit axis vs `pinned`: `lowerConstSlots` appends `.axis #const<u> (some 1)`, so the synthetic
  UID is in `declaredAxisSizes`; it can never be a destination axis (fresh UID, no tensor declares it), so it
  cannot change `boxed`. For the D5 test production sees `[u]` and the oracle sees `[]` for a constant
  slot; neither can hit a destination UID. Agree.
- Constant coordinate equal to the box size (`S[=4]`, `k = 4`), single and group: `writerExtentExceedsBox`
  payload `writer 1, dimension 0: extent 5 exceeds declared box extent 4` in native and reference.
- Tropical `.max` group of constants only (`S[=1] := A`, `S[=3] := A`, `k = 4`): `[-inf, 4, -inf, 4]` in all
  three legs (bits `0xFFF0...`/`0xFF800000` for the holes).
- Two writers to the same constant under f32: already pinned by F1 (`S[3]` twice plus `S[a]`, all legs);
  not re-probed.
- Axis-NAME anti-goal: `rg` for `.name` reads and `"#const"` over `LeanNCD/DSL`, `LeanNCD/Eval`,
  `Differential.lean` and `test/`: the only `#const` producer is `lowerConstSlots` (`Structural.lean:1146`);
  name reads elsewhere are diagnostics, `assignUIDs` memo (runs before `lowerArith`), and route's
  `AxisP (some name) (var name)` (`Lowering.lean:239-247`). Probe: a hand-built user axis spelled exactly
  like the synthetic one (`#const3`, size 8) next to a constant writer whose synthetic axis is `#const3`
  (size 1): decls carry both `("#const3", 1, some 8)` and `("#const3", 3, some 1)`; reference, checked f64
  and f32 all give `[1] [36]`; the routed `ThreadedComposed` repr equals the `#constZ` program's with the
  name substituted (the synthetic axis does not appear in the routed diagram at all). No name-dependent
  behaviour observed after the B-D2 guard deletion.
- Second extent formula: every `outExtent`/`affineImageBounds` call site re-grepped (`Eval/Eval.lean`,
  `Eval/Scan.lean`, `Eval/SizeInfer.lean`, `Eval/CollectorShape.lean`, `Eval/Plan/Check.lean`
  `scatterDestExtent`/`scatterImageBounds`, `Eval/Plan/Compile.lean`, `Differential.lean` `derivedShape`):
  all call the one home. The only restatement is test-side `predictedExtent`
  (`test/Semantics/OracleSortRules.lean:267-285`, legacy sum for multi-axis), already parked in section 2.
- Callers: `LHSSlot.collectable` is called only at `Collect.lean:158` and `:196`; `scatterAffineClass` only
  at `Eval/Plan/Compile.lean:127`. Matches section 5.
- Source oracle "declared extents are taken as pinned": sound, every source axis must have a size
  (`Adapter.lean:282`, `missingDomain`).
- Source `WriteForm`s come from `idxAffineForm` itself (`Admission.lean:801`), so zero-coefficient terms
  are kept on both sides of the D5 comparison.
- JAX path: every scatter step is refused categorically (`unsupportedStep`), so newly admitted groups cannot
  reach JAX emission.
- B-D3 numbers re-derived: `convBoxed` base pin `(some [6], some [6], some [6])` at `eab7dded`
  `ScatterGeometryTest.lean:135`, tip pin `[8]` and probe `[8]`; `pinAll 8 S3` base `[4]` (`:281`), tip `[8]`;
  C1 counts base `[222, 195, 88]` (`OracleSortRulesTest.lean:113` at `eab7dded`), tip `[281, 186, 38]`
  (`:115`), both sum to 505; `concreteC1.length` base 81, tip 99.
- Raw `.affine (.const _)` reachability: `lowerArith` lowers every non-scan constant of both `.assign` and
  `.scatter`; the surface has no `.scatter` spelling (`Elab.lean:303`), and statements that keep a raw
  constant carry a scan slot. Consistent with B-D1.
