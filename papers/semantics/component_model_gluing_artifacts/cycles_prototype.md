# Cycle and hidden-store component donors (authoring prototype)

Source: `leanncd/experiments/indexed_execution/IndexedComponentModelCycleFixtures.lean`.
This is a non-default experiment fixture, not a rank/execution theorem or a
generic gluing theorem.

## Donors and deltas

- `cycleUpstream := upstreamComponent false`: finite rational scalar tensors
  `privateTensor = 0`, `boundaryTensor = 1`, no input; the private whole-store
  equation is `t = t²`, and the output boundary copies `t`.
  `cycleDownstream := downstreamComponent true`: input `t`, strict reciprocal
  output `u = 1/t`, with `cycleBoundary := scalarBoundary false true`.
- `hiddenUpstream := upstreamComponent true`: **same** private `t = t²`,
  but its output boundary is constant zero independently of `t`.
  `totalDownstream := downstreamComponent false`: total output `u = t + 1`,
  with `hiddenBoundary := scalarBoundary true false`. The private upstream
  tensor is still a defined tensor in the complete store; it is not erased.

Both component pairs carry explicit `SourceContractMatch` certificates and
scalar `Boundary` equivalences. The source contracts include the cyclic
self-read in their readable sets. The sole producer delta is the boundary
body/read footprint; the sole consumer delta is strict reciprocal versus
total addition. No generic composite witness or dependency on ModelInputs
or ModelTransport is included.

## Exported signatures

`upstreamProgram (hidden : Bool) : Program ...`;
`downstreamProgram (strict : Bool) : Program ...`;
`upstreamMatch hidden : SourceContractMatch ...`;
`downstreamMatch strict : SourceContractMatch ...`;
`upstreamComponent hidden : MatchedComponent declarations`;
`downstreamComponent strict : MatchedComponent declarations`;
`scalarBoundary hidden strict : Boundary (upstreamComponent hidden) (downstreamComponent strict)`;
`upstreamInput hidden : (upstreamProgram hidden).Input`;
`downstreamInput strict (x : ℚ) : (downstreamProgram strict).Input`;
`scalarStore (t u : ℚ) : Store RationalReference.Carrier declarations`.

The proof exports are `cycle_upstream_zero_model`,
`cycle_upstream_one_model`, `cycle_upstream_not_admissible`,
`reciprocal_zero_no_model`, `reciprocal_one_model`,
`reciprocal_one_unique`, `hidden_upstream_zero_model`,
`hidden_upstream_one_model`, `hidden_boundary_equal`,
`hiddenStore_distinct`, and `total_zero_model`.

## Observations and mutation candidates

Controller reported baseline `LeanNCD` and `IndexedExecutionExperiment` green
before these single-file checks (no independent Lake build). Both
`bash leanncd/scripts/lean-file.sh /Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-model/leanncd experiments/indexed_execution/IndexedComponentModelCycleFixtures.lean`
and `bash .claude/skills/slice-plan/check-snippet.sh /Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-model/leanncd/experiments/indexed_execution/IndexedComponentModelCycleFixtures.lean`
completed successfully, without warnings. The three in-file `#eval` results
were, exactly, `(some 0, some 1)`, `(none, some 1)`, and
`(0, 0, some 1)`: upstream square body at 0/1; downstream reciprocal body
undefined at 0 and defined at 1; hidden upstream boundary values equal zero
and total consumer body at 0 equal one. These are body/output observations,
**not** proofs that the executor resolves a cyclic model or has a rank.

Proposed single-replacement mutations (not run; no diagnostics claimed):
replace `else if hidden then .lit 0 else readScalar _ privateTensor` with
`else readScalar _ privateTensor` to break the hidden producer's source/fragment
match (a proof-elaboration kill); replace
`if strict then reciprocalBody _ else totalBody _` with
`if strict then totalBody _ else totalBody _` to break the strict downstream
source/fragment match (a proof-elaboration kill); replace
`(upstreamInput false) (scalarStore 1 1) :=` with
`(upstreamInput false) (scalarStore 1 0) :=` in `cycle_upstream_one_model` to
falsify the complete boundary equation (a model-counterexample proof kill).

Authoring estimate was 25–35 tool turns; actual Lean elaboration/debugging
exceeded that estimate and likely the 60-turn ceiling. Context-token usage was
not measured; no claim of staying under the token cap is made.
