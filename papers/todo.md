# Future work

## Fork logical Eval scheduling from route-specific nonlinearity lowering

> **Permanently archived — do not execute this section.** Superseded by
> [`papers/nonlinearity_split_pair_direct_lowering.md`](nonlinearity_split_pair_direct_lowering.md).
> The canonical design schedules one logical unsplit `ScheduledProgram`, then uses a private,
> collision-free `PhysicalRouteProgram` immediately before existing `routeCore`; it has no second
> scheduler, keeps scans opaque, and reuses existing `RouteSpec` statements. The fork/shared-split and
> generated-pair recommendations below are retained only as rejected historical context.

**Priority:** Archived. Reconsider architecture only under the replacement plan's explicit triggers.

### Problem

`TLProgram.compileToScheduled` currently runs `splitNonlins` before scheduling. The resulting
`ScheduledProgram` is shared by two consumers with different needs:

- `route` needs separate contraction and nonlinearity statements for categorical lowering;
- Backend Eval IR can represent contraction, pointwise, and axiswise steps directly.

Backend Eval IR therefore receives a route-oriented incidental encoding. A source expression such as
`Y := relu(contraction)` is first split into a generated `%nl...` assignment and nonlinear consumer,
then the plan compiler lowers that consumer into another assignment followed by a nonlinear step.
The result is a redundant three-step plan:

```text
assign -> assign -> pointwise/axiswise
```

The planned nonlinear-scan work currently compensates for the same mismatch by teaching
`compileScan` to recognize adjacent `%nl...` pairs, reconstruct one logical statement before
state/scratch classification, and then split it again during plan lowering. This makes nonlinear
scans safe, but it leaves both architectural concerns in place:

1. redundant nonlinearity lowering;
2. a later compiler phase depending on a generated-name, adjacency, and trivial-read protocol to
   recover an earlier logical operation.

### Decision

Introduce a late pipeline fork after the common semantic phases, ideally after `finalizeScans`:

```text
assignUIDs
-> resolveDecls
-> validation
-> lowerArith
-> finalizeScans
-> fork
     |-> logical scheduling -> Backend Eval IR
     `-> splitNonlins -> route scheduling -> categorical route
```

Backend Eval IR should consume logical, unsplit nonlinear statements and lower each exactly once:

```text
assign -> pointwise/axiswise
```

The categorical route may retain route-specific splitting. Its existing nonlinear-scan
representative-label bug must be handled explicitly in its own scope rather than leaking its
representation requirements into Backend Eval IR.

### Required design work

- Define the last common pipeline representation and the two post-fork contracts.
- Prefer distinct types or opaque wrappers for logical and route-linearized schedules. Do not use one
  `ScheduledProgram` type with two undocumented invariants.
- Preserve a route-specific factorization theorem such as:

  ```text
  TLProgram.compile = compileToRouteScheduled >>= route
  ```

  The current `compile = compileToScheduled >>= route` relationship and its bridge proofs cannot be
  silently invalidated.
- Decide whether `compileToScheduled` retains its current route-prefix meaning, becomes a compatibility
  alias, or is deliberately migrated to a more explicit API.
- Define the public observation boundary. Generated `%nl...` intermediates should normally become
  unnamed internal slots rather than materialized result names, but that behavior change must be
  stated and tested.
- Verify logical scheduling independently: dependency order, repeated names, external-name discovery,
  scan outputs, error order, and warning order.
- Keep the scan oracle independent of plan-compilation helpers when removing its current dependence on
  `%nl...` advancing scratch.
- Account for branch-specific `FreshM` allocation. Semantic or alpha-equivalence, not identical fresh
  counters or generated names, is the relevant cross-branch relation.

### Implementation sequence

1. **Specify and test current observations.** Pin pipeline errors, warnings, user-visible outputs,
   scheduling, route agreement, and nonlinear examples before changing the boundary.
2. **Introduce the late fork.** Share all phases through `finalizeScans`; add explicit logical-Eval and
   route-linearized scheduling entry points.
3. **Switch top-level Eval nonlinearity.** Make one real nonlinear source expression produce exactly
   two plan steps, one unnamed preactivation slot, and one published result slot.
4. **Revise the nonlinear-scan plan.** Retain the block-operation work but remove split-pair
   recombination, `malformedNonlinSplit`, three-step expectations, and tests that exist only to pin the
   recovery protocol.
5. **Implement nonlinear scan blocks.** Lower logical nonlinear base and recurrence statements
   directly to assignment plus pointwise/axiswise `BlockStep`s.
6. **Address categorical routing separately.** Add nonlinear-scan route tests and fix or explicitly
   reject the current `repStmt`-based mislabeling behavior.

### Nonlinear-scan work that remains necessary

The fork removes only the split-pair workaround. The following planned work remains:

- `BlockStep = assign | pointwise | axiswise`;
- corresponding checked block-step evidence;
- block checker and Dense worker dispatch;
- shared top-level/block nonlinearity chaining;
- admission and validation of `LHSSlot.freeNorm` inside scan blocks;
- remapping a marked axis from the full scan LHS to the retained local tensor slice;
- one-slot allocation for identity statements and two-slot allocation for nonlinear statements;
- publication of only the nonlinear result slot;
- base-block, recurrence-block, state, scratch, pointwise, and axiswise fixtures;
- differential, mutation, and corpus re-verification.

### Risks and downsides

- The current compile-prefix identity and bridge agreement proofs must change.
- Two scheduled representations can drift unless their shared prefix and separate invariants are
  explicit.
- Scheduling and oracle tests require revision.
- Removing materialized `%nl...` values changes the complete result environment, even if user-level
  numerical outputs are unchanged.
- The fork does not by itself fix categorical routing's nonlinear-scan behavior.
- Every future source feature must identify whether its lowering is common, Eval-specific, or
  route-specific.

These costs are preferable to making `%nl...` recovery a permanent protocol used by future backends,
optimizers, predicate lowering, masked axiswise operations, and serialization.

### Definition of done

- A top-level nonlinear expression produces exactly:

  ```text
  assign -> pointwise/axiswise
  ```

- A nonlinear scan-block statement produces exactly the same two-operation shape in `BlockStep`.
- `compileScan` contains no `%nl` prefix, adjacency, or trivial-read pair recognition.
- No `malformedNonlinSplit` diagnostic is needed by Backend Eval IR.
- Preactivation slots are internal and unnamed; only source-level results are materialized.
- Logical Eval and route-linearized schedules have explicit, non-interchangeable contracts.
- The route-specific compile factorization and bridge properties are restored under the new API.
- The legacy evaluator, checked Dense evaluator, and independent scan oracle agree on all admitted
  user-visible results.
- Error and warning ordering is either preserved or intentionally documented and tested.
- Nonlinear scan routing is tested and either correctly represented or rejected explicitly.
- The full Lean build and the complete differential/mutation corpus pass.
