# Slice T1 — logical schedule + private physical route fragments

**Scope:** Task 1 only of
[`papers/nonlinearity_split_pair_direct_lowering.md`](../../../../papers/nonlinearity_split_pair_direct_lowering.md)
(that document's §3.3, "atomic architecture gate"). That document remains the canonical design
record; this is the executable plan for its first slice and nothing else.

**Deliberately NOT in this slice** (each is a later slice, planned only once this one lands, per
CLAUDE.md Rule 13):

| Master-plan task | Deliverable | Owned by |
|---|---|---|
| Task 2 | 145-case route corpus + 19 named payload fixtures | a later slice |
| Task 3 | `RawPlanBlock.steps : Array BlockStep` generalization | a later slice |
| Task 4 | nonlinear Plan scan admission + independent oracle | a later slice |
| Task 5 | differential + stale-document sweep + closure | a later slice |

Nothing here admits a new EvalPlan/backend capability, changes `routeCore`, changes any `RouteSpec`
theorem statement, introduces a second scheduler, or adds structured categorical scan bodies.

---

## §0 Verified baseline

Everything in this section was executed against `main` at `a063944` on 2026-08-26. Re-run it in the
worktree before editing; a failure at that point is base drift, not a transplant defect.

### 0.1 Donor artifacts typecheck against current `main`

All five donors pass from their final durable paths (`cd leanncd` first):

```bash
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/adapter_proof/RouteFragmentsSeed.lean
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/fixtures/FixtureSupportSeed.lean
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/fixtures/RouteFragmentDiagnosticSeed.lean
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/fixtures/PayloadConservationSeed.lean
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/fixtures/RouteFragmentCorpusSeed.lean
```

Observed 2026-08-26: **all five exit 0**; the adapter donor completes in ~5.3s with its 15 `#guard`s
and five `run_cmd` blocks silent. The plan's acceleration story is therefore live, not stale — the
implementer copies *reviewed, compiling* declarations rather than retyping design prose.

**Consequence for this plan: it contains almost no retyped Lean.** Re-typing donor code into a plan
would create a second, unverified copy of something already verified at its own path. Where this
plan needs an implementation, it names the donor declaration to copy. The only new Lean this plan
authors is in §0.3, and it is verified below.

### 0.2 Structural claims checked against the tree

| Master-plan claim | Verified? | Exact finding |
|---|---|---|
| `splitNonlins` runs pre-`schedule` in both public chains | yes | `DSL/Compile.lean`, in `TLProgram.compile` and `TLProgram.compileToScheduled` |
| `LinearProgram` differs from `ScanProgram` only by prose | **yes** | both are `decls / stmts / env / extNames`; the only difference is `LinearProgram`'s `-- no nonlinearity in RHSExpr.nonlin` comment |
| "six current `LinearProgram` matches" | **yes, exactly 6** | `Pipeline/Types.lean` (the structure), `Pipeline/Lowering.lean` (`splitNonlins` result, `schedule` argument), `test/DSL/Pipeline/LoweringTest.lean` (3 fixtures) |
| `LHSSlot.toReadIdx` lives in `Lowering` and is reused | yes | defined in `Pipeline/Lowering.lean`, consumed by `splitStmt`; the donor calls it, so the move to `DSL/Ast.lean` is real work, not optional tidying |
| public `route` = `routeCore` + `wellFormedDom` guard | yes | `Pipeline/Lowering.lean`; `routeCore` itself is untouched by this slice |
| `compile_eq_route` is the Agreement witness to replace | yes | `Bridge/Agreement.lean`; `compile_wellFormed` consumes it via `obtain ⟨sp, s₁, _hsp, hrc, hne, hwfd⟩` |
| "10 production / 27 test / 4 experiment `compileToScheduled` call sites" | **partly — corrected below** | see §0.4 |
| `Tests` lakefile uses an explicit `globs` list, not a wildcard | yes | `lakefile.toml`; a new test module is invisible until added there |
| `LeanNCD.lean` imports `DSL.Pipeline.{Types,Structural,Lowering,RouteSpec}` explicitly | yes | so `RouteFragments` needs its own import line to be discoverable |

### 0.3 Authoring finding — the recurring-defect instance this slice would otherwise ship

This is the sweep the `slice-plan` skill requires when a task touches a known defect family. The
family here is *a predicate that is sound only by an unenforced call-site precondition* — the same
shape as `baseWriteRowsOk` in Wave F F4.

Today, `splitStmt` (`Pipeline/Lowering.lean`) handles scatter with:

> `| .scatter .. => return [s]   -- always identity-nonlin here (rejected upstream otherwise)`

That comment is accurate **today** and the code is sound **today**, for one reason only: `splitStmt`
is reachable solely from `splitNonlins`, which is reachable solely from the two `DSL/Compile.lean`
chains, both of which run `checkScatterNonlin` upstream. `checkScatterNonlin` (`Pipeline/Structural.lean`)
throws `unsupportedNonlinScatter` for a non-identity nonlin on either `.assign`-that-becomes-scatter
or `.scatter`. So the precondition holds for every caller that exists.

The donor carries the same assumption forward as a catch-all:

> `physicalizeOne`: `| _ => ([sc], ⟨logicalIndex, firstStep, firstStep, none⟩)`
> `fragmentWidth`: `| _ => 1`

**This slice changes the caller set that assumption depends on.** After the flip, public `route`
accepts a *logical* `ScheduledProgram` from any caller — that is the entire point of §2.4 of the
master plan, and `compileToScheduled >>= route` plus direct `route` are both supported surfaces. A
hand-built logical schedule containing `.plain (.scatter nm slots rhs opts)` with
`rhs.nonlin ≠ .identity` never passes through `checkScatterNonlin`, reaches the catch-all, and is
copied as a single physical step. It then routes as **one** `BrBase` with the nonlinearity absent
from the categorical presentation, silently. Because `fragmentWidth` mirrors the same catch-all,
`fragmentLayoutOk` *agrees* with the miscount and cannot detect it.

Two properties make this exactly the family the skill describes:

- it is a **write-path** classifier (which statements produce which physical writes), not a
  read-path one backstopped elsewhere;
- **no diff shows it.** `splitStmt`'s `.scatter` arm text does not change in this slice. Only the
  set of callers relying on its precondition changes. A reviewer reading any Task diff sees nothing.

**Required deliverable (Task 1): the case × class table.** Every physicalization input class must be
classified *required-split* / *required-copy* / *required-reject*, with **no cell left "silently
ignored."** The classes are the full constructor cross-product, not a sample:

| # | Input class | Reachable from surface `compile`? | Required classification |
|---:|---|---|---|
| 1 | `.plain (.assign …)`, `nonlin = .identity` | yes | copy, width 1 |
| 2 | `.plain (.assign …)`, `nonlin = .pointwise _` | yes | split, width 2 |
| 3 | `.plain (.assign …)`, `nonlin = .axiswise _ none` | yes | split, width 2 |
| 4 | `.plain (.assign …)`, `nonlin = .axiswise _ (some mask)` | yes | split, width 2; mask rides the consumer |
| 5 | `.plain (.scatter …)`, `nonlin = .identity` | yes | copy, width 1 |
| 6 | `.plain (.scatter …)`, `nonlin ≠ .identity` | **no** — `checkScatterNonlin` rejects | **decide: reject, never silent copy** |
| 7 | `.plain (.recurMorphism …)` | no — `unsupportedRecurMorphism` | copy, width 1 (carries no `RHSExpr`) |
| 8 | `.scan …` (`isAffine = false`) | yes | copy verbatim, width 1 |
| 9 | `.scan …` (`isAffine = true`) | yes | copy verbatim, width 1 |
| 10 | `.scanPre …` | no from surface; yes hand-built | copy verbatim, width 1 |

Class 6 is the open decision and Task 1 must close it explicitly. The master plan's non-goals say
nonlinear scatter semantics are undefined in this slice — but "undefined" must mean **reject**, not
**silently mis-route**. The recommended resolution reuses the existing constructor rather than
inventing a diagnostic, keeping common-domain error precedence unchanged (nothing reachable from
`compile` can hit it):

```lean
import LeanNCD.DSL.Pipeline.Types

namespace LeanNCD

/-- Classes 6 of the physicalization case table: a nonlinear scatter cannot be split into a
    contraction/nonlinearity pair (activation-before-or-after collision reduction is undefined),
    and must never be silently copied as one step. Unreachable from `TLProgram.compile`
    (`checkScatterNonlin` rejects first); reachable only for a hand-built logical schedule. -/
def nonlinScatterName? : ScanStmt → Option String
  | .plain (.scatter nm _ rhs _) => if rhs.nonlin == Nonlin.identity then none else some nm
  | _ => none

end LeanNCD
```

Verified with `bash .claude/skills/slice-plan/check-snippet.sh` on 2026-08-26 — see §0.5.

Classes 8/9 carry a second, *intentional* change worth pinning in the same table so a later reader
does not mistake it for a defect: old `splitScan` splits nonlinearities **inside** scan base/recur
bodies; new physicalization copies the scan node verbatim. That is the scan-semantics fix, not a
regression — it is why the interleaved-axiswise recurrence stops producing uniform `0.5` slices. For
*routing* it must be projection-equal, because scan routing uses a representative statement and does
not encode the body (master plan §2.5). Assert both halves separately.

### 0.4 Corrections to the master plan the implementer needs

These are authoring-time corrections. The master plan is not wrong in substance, but three of its
pointers would cost the implementer a search or a false expectation.

**(a) The `compileToScheduled` census mixes two different units.** Verified counts:

| Location | Raw mentions | Actual call expressions | Note |
|---|---:|---:|---|
| `LeanNCD/` (production `.lean`) | 10 | **1** | the single runtime caller is `Eval/Entry.lean`; `DSL/Compile.lean` is the definition; **7 of the 10 are `Bridge/Agreement.lean` proof references** |
| `test/` | 30 | **27** | 3 are prose in `PropertyOracle/Gen.lean`, `Eval/Plan/NonlinCompileTest.lean`, `Eval/Plan/ContractTest.lean` |
| `experiments/jax_bridge/` | 6 | **4** | 2 are prose; the 4 calls are in `EvalPlanSmoke.lean` (×2), `EvalPlanAffineSmoke.lean`, `EvalPlanAffineCorpus.lean` |

The master plan's "27 test / 4 experiment" are correct **call** counts. Its "10 production calls" is
a *mention* count: there is **one** production runtime caller. The other nine are the definition, one
comment in `Pipeline/Lowering.lean`, and seven Agreement proof references — and those seven are
precisely the proof surface Task 2 repairs, not call sites to re-verify. Budget accordingly.

**(b) Two donor fixtures are not where the master plan's directory naming implies.** Verified paths:

| Symbol the master plan names | Actual file |
|---|---|
| `MaxReduceTest` predicate-aggregation case | `test/DSL/MaxReduceTest.lean` |
| `ScatterNonlinRejectTest.RSN1` | `test/Eval/Portfolio/ScatterNonlinRejectTest.lean` |
| `RejectTest.SS4` / `RejectTest.UF5` | `test/Eval/Portfolio/RejectTest.lean` |
| `StructuralTest` rank/dtype/predicate/scatter | `test/DSL/Pipeline/StructuralTest.lean` |
| `IterDeclTest` undeclared scan-axis | `test/DSL/IterDeclTest.lean` |
| `NonlinCompileTest.reluProg` / `.softmaxProg` | `test/Eval/Plan/NonlinCompileTest.lean` |
| `CompileTest.acceptedSched` | `test/Eval/Plan/CompileTest.lean` |
| `ScanCompileTest.coupledSched` / `coupledInputs` | `test/Eval/Plan/ScanCompileTest.lean` |
| `LoweringTest` AGG1 / identity cycle / strided reads | `test/DSL/Pipeline/LoweringTest.lean` |
| `RecurMorphismTest.stepTC` | `test/DSL/Pipeline/RecurMorphismTest.lean` |
| `ParsePredicatesTest.band` | `test/DSL/ParsePredicatesTest.lean` |
| `AcsetCodecTest` causal-attention mask | `test/Bridge/AcsetCodecTest.lean` |

**(c) `new-slice`'s SKILL.md calls the plan "gitignored"; it is not.** `leanncd/docs/superpowers/plans/`
is tracked (21 files). Committing this plan to `main` before branching means the worktree inherits
it and `--plan` is a harmless no-op. Not a blocker; noted so the implementer does not go hunting.

### 0.5 Snippet verification

The one Lean block this plan authors (§0.3) was checked with the repo's own tool:

```bash
bash .claude/skills/slice-plan/check-snippet.sh /tmp/nonlin_scatter_snippet.lean
```

Result recorded in the ledger at execution time. Every other Lean artifact in this slice is a
*copy* of an already-passing donor declaration, so its verification is §0.1's donor run plus the
task gates.

---

## §1 Global constraints

Exact values, and what is deliberately excluded.

- **Exactly one scheduling pass.** `physicalizeForRoute` must not call `schedule` or `topoSort`.
- **Zero generated names in `compileToScheduled` output.** No `%nl` producer/consumer pair survives
  into the shared schedule.
- **No user-namespace reservation.** Internal names are `#`-strings of length
  `maxSourceNameLength + ordinal + 1`; strict length growth is what proves freshness and
  injectivity. A `%nlN` fallback with an unchecked freshness assumption is forbidden.
- **Route fragments split only top-level `.plain (.assign …)` with non-identity nonlin.** Every other
  class is copy-or-reject per §0.3's table — no cell silently ignored.
- **Scan and `scanPre` nodes are copied verbatim**, including opaque nested payloads.
- **`routeCore` and every `RouteSpec` theorem statement are unchanged.** If preserving route equality
  appears to require changing either, stop (§4).
- **`compile_wellFormed`'s public type is unchanged.** Agreement consumes only successful `routeCore`,
  external-count equality, and `wellFormedDom` — *not* fragment evidence.
- **FreshM state policy.** `compile` and `compileToScheduled >>= route` return the same final state.
  Every failure *before* the former split phase preserves its exact old state. After it, the counter
  is intentionally not preserved, and every explained delta must equal exactly the number of removed
  split mints. **Compensating UID mints to reproduce old counters are forbidden.**
- **`splitNonlins`, `splitStmt`, `splitScan` survive as non-production regression helpers** — the
  old/new differential needs them. They leave the production chain, not the tree.
- **`LinearProgram` stays as a deprecated compatibility alias** for this slice.
- **No new EvalPlan/backend capability** is admitted; unmasked pointwise/axiswise `f64` only.
- Import graph is exact and acyclic:
  `DSL/Ast.lean ← DSL/Pipeline/Types.lean ← DSL/Pipeline/RouteFragments.lean ← DSL/Pipeline/Lowering.lean`.
  `RouteFragments.lean` must not import `Lowering`, `Structural`, `Agreement`, or any `Eval` module.
  The donor's `LeanNCD.Bridge.Agreement` import is a donor-only convenience and must not be copied.

**Discoverability** (a `slice-plan` requirement, and a thing this repo has shipped wrong before —
Wave C's C0–C4 left ten files unreachable from `import LeanNCD`): `RouteFragments` is not done when
it compiles. Task 1 must also add its explicit `import LeanNCD.DSL.Pipeline.RouteFragments` line to
`LeanNCD.lean` alongside the existing `DSL.Pipeline.*` imports, and a row to `LeanNCD/DSL/AGENTS.md`'s
phase table. Transitive reachability through `Lowering` does not count.

---

## §2 Task breakdown

Three tasks. Boundaries chosen by the reviewer test: *a reviewer could meaningfully reject one while
approving its neighbour.*

| Task | Deliverable | Fixtures | Mutation cycles | Risk driver |
|---|---|---:|---:|---|
| 1 | `RouteFragments.lean` + `toReadIdx` move + case×class table + route-equality fixtures | 12 | **10** | proof volume; largest single deliverable; **verifiable without the flip** |
| 2 | Atomic flip (Types/Lowering/Compile/Agreement) + all fallout | 1 | **2** | integration blast radius: 27 test + 4 experiment call sites, 7 Agreement proof references |
| 3 | `RouteFragmentDiagnosticTest.lean` — 19 compile + 2 route-domain + 9 composition observations | 30 obs. | **3** | exactness: every constructor, payload, and final state pinned |

Total 15 mutation cycles — the master plan's §3.3 list (14, plus the class-6 cycle this planning pass
added to it), mapped 1:1 with none dropped:

| Master §3.3 mutation | Task |
|---|---:|
| `maxLen` instead of `maxLen + ordinal + 1` | 1 |
| one internal name used twice | 1 |
| map a logical output to fragment **entry** | 1 |
| split a scan body | 1 |
| invoke `schedule` during physicalization | 1 |
| remove internal-name freshness checking | 1 |
| remove fragment-coverage checking | 1 |
| remove fragment-exit checking | 1 |
| reverse physical topology | 1 |
| restore the class-6 catch-all so a nonlinear `.scatter` copies instead of rejecting | 1 |
| reinsert `splitNonlins` into `compileToScheduled` | 2 |
| restore the old split-shape oracle guard after the flip | 2 |
| change the production rank-error constructor/payload | 3 |
| swap `checkReadRanks` / `checkDtypes` | 3 |
| corrupt successful routed `nExternal` | 3 |

**Every cycle means: mutate the implementation under test, _observe failure_, restore, _observe
pass_ — recorded in the ledger with the failing assertion named.** Predicting a failure, or mutating
the assertion instead of the implementation, does not count.

**Sizing note:** Task 1 is the expensive one (9 cycles + 11 fixtures + the proof set), not Task 2,
even though Task 2 is the architecturally scary one. Size the dispatches to the fixture-and-mutation
count, not the diff.

---

### Task 1 — `RouteFragments.lean`, verifiable before the flip

**Why this is separable.** Route equality can be established *without* changing any public API:
compare `splitNonlins → schedule → routeCore` (old) against `schedule → physicalizeForRoute → routeCore`
(new) on the same source. The donor does exactly this. So Task 1 lands as a pure addition, its
fixtures pass on an otherwise-unmodified tree, and a reviewer can reject it while the rest of the
tree stands.

**Files**

- `LeanNCD/DSL/Ast.lean` — receives `LHSSlot.toReadIdx` (moved, not copied; no reverse import)
- `LeanNCD/DSL/Pipeline/RouteFragments.lean` — **new**
- `LeanNCD/DSL/Pipeline/Lowering.lean` — `toReadIdx` removal only; `route`/`routeCore` untouched here
- `LeanNCD.lean` — explicit import line
- `LeanNCD/DSL/AGENTS.md` — phase-table row
- `test/DSL/Pipeline/RouteWeaveTest.lean` — route-equality fixtures
- `lakefile.toml` — only if a new test module is added

**Implementation** — transplant from `adapter_proof/RouteFragmentsSeed.lean`, in the donor README's
order. Copy declarations; do not redesign them:

1. Move `LHSSlot.toReadIdx` to `DSL/Ast.lean`.
2. Name inventory + generation: `declaredTensorName?`, the route reads/writes/outputs accessors,
   `routeNameInventory`, `maxSourceNameLength`, `routeName`, and the three theorems
   (`routeName_length`, `routeName_not_mem`, `routeName_injective`).
3. `RouteFragment`, `PhysicalizeAcc`, `producerSlots`, `physicalizeOne`, `physicalizeStep`,
   `physicalizeRaw`, `physicalizeRaw_fragmentCount`, `generatedRouteNames`, `routeNamesFresh`,
   `fragmentWidth`, `checkFragmentAt`, `fragmentLayoutOk`, `fragmentExitsOk`, `physicalRouteInOrder`.
   Keep the fold-count helper private.
4. `PhysicalRouteProgram` + `physicalizeForRoute`, with the **real constructor private** (`private mk ::`
   — note that a bare `private` on a structure does **not** privatize its constructor). Successful
   construction must carry: declaration/env/external preservation, fragment nonemptiness/coverage/
   contiguity, freshness/injectivity, unique logical exits, physical topological order.
5. **Close case-table class 6** per §0.3: nonlinear scatter must reject, never silently copy. Update
   `physicalizeOne` *and* `fragmentWidth` together — leaving `fragmentWidth`'s catch-all in place
   makes `fragmentLayoutOk` agree with the defect.
6. Ship the §0.3 case × class table into `LeanNCD/DSL/AGENTS.md`, with every one of the ten classes
   classified and **no cell reading "silently ignored."**
7. Add the explicit `LeanNCD.lean` import.

**Fixtures** — each names its donor, so nobody rediscovers it:

| # | Fixture | Donor + change |
|---:|---|---|
| 1 | ReLU: 1 logical stmt, 0 generated names, exact old/new route equality | clone `NonlinCompileTest.reluProg`'s **source construction** locally in `RouteWeaveTest`; do not import the test module |
| 2 | Axiswise softmax equivalent | clone `NonlinCompileTest.softmaxProg` source construction |
| 3 | ReLU → downstream contraction | fixture 1, append a contraction reading its output; asserts fragment-**exit** lookup |
| 4 | Two nonlinear branches → one join | fixture 1 ×2 with distinct names, plus a joining stmt; asserts private-name injectivity |
| 5 | Unread secondary nonlinear output | fixture 4, drop the join; asserts survival through scheduling + physicalization |
| 6 | **Named public** axiswise source fixture (`.freeNorm` degradation on producer only) | new, from source syntax, in `RouteWeaveTest`; **must be public** — the later corpus slice reuses this exact construction |
| 7 | ReLU scan → one opaque copied node | clone `DSL/Pipeline/ScanAffineTest.reluScan`'s source construction locally; it is private, so clone it, do not cite it |
| 8 | Axiswise recurrence → one opaque copied node | fixture 6's construction placed inside a recurrence |
| 9 | Coupled scans | clone public `ScanCompileTest.coupledSched` / `coupledInputs` constructions locally |
| 10 | Adversarial long-`#` source names | fixture 1, rename the output tensor to an all-`#` name longer than any other; generated names must still be absent from the source set |
| 11 | Existing identity schedule unchanged | reuse a `LoweringTest` identity fixture; asserts step/slot/routed values byte-identical |
| 13 | **Nonlinear `.plain (.scatter …)` is rejected**, not copied as one step (§0.3 class 6) | new; hand-build the logical schedule directly and call public `route` — this class is unreachable from `TLProgram.compile` (`checkScatterNonlin` rejects first), so a source-level fixture cannot reach it. Numbered 13 to match the master plan; fixture 12 is Task 2's. |

Fixtures 1–2 assert route equality **only** in this task. Their "two Plan steps instead of three"
assertions live in `NonlinCompileTest` and belong to Task 2, which is when that becomes true.

**Mutation cycles (10)** — all against `RouteFragments.lean`:

1. `maxLen` instead of `maxLen + ordinal + 1` → fixture 10 fails.
2. Reuse one internal name across fragments → fixture 4 fails.
3. Map a logical output to fragment **entry** instead of exit → fixture 3 fails.
4. Split a scan body → fixtures 7/8 fail.
5. Call `schedule` inside physicalization → the no-second-scheduler guard fails.
6. Remove internal-name freshness checking → checked construction or fixture 10 fails.
7. Remove fragment-coverage checking → checked construction or the coverage theorem fails.
8. Remove fragment-exit checking → fixture 3 fails.
9. Reverse physical topology → checked construction or route equality fails.
10. Restore the class-6 catch-all so a nonlinear `.scatter` is copied as one step instead of
    rejected → fixture 13 fails. Mutate `physicalizeOne` **and** `fragmentWidth` together; leaving
    both catch-alls in agreement is precisely the defect being guarded, so mutating only one would
    prove less than it appears to.

**Gate**

```bash
cd leanncd
"$HOME/.elan/bin/lake" build LeanNCD.DSL.Pipeline.RouteFragments
"$HOME/.elan/bin/lake" build DSL.Pipeline.RouteWeaveTest DSL.Pipeline.LoweringTest DSL.Pipeline.ScanAffineTest
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

`Tests` and `LeanNCD` must be green **without** any behaviour change: this task adds code and adds
fixtures, and nothing existing may move. No `sorry`, `admit`, or `axiom` in the new module.

---

### Task 2 — the atomic flip

**Atomicity.** The logical API flip, the public route wiring, and the Agreement repair land
**together**. There is no green intermediate state in which `compileToScheduled` is logical but
`compile` keeps an independent old split route chain. Intermediate commits within this task are
allowed only if each one preserves `compile = compileToScheduled >>= route` and leaves
`compile_wellFormed` provable.

**Files**

- `LeanNCD/DSL/Pipeline/Types.lean` — `LinearProgram` → deprecated alias; `schedule` accepts logical
- `LeanNCD/DSL/Pipeline/Lowering.lean` — public `route` physicalizes then calls unchanged `routeCore`
- `LeanNCD/DSL/Compile.lean` — both chains drop `splitNonlins`
- `LeanNCD/Bridge/Agreement.lean` — `compile_eq_route` → `compile_eq_physical_route`; restore `compile_wellFormed`
- `LeanNCD/DSL/Pipeline/RouteSpec.lean` — statements unchanged; add named projections only if a test needs one
- `LeanNCD/Eval/Entry.lean` — the single production runtime caller (§0.4a)
- `LeanNCD/Eval/Eval.lean`, `LeanNCD/Eval/Scan.lean` — verification + split-specific comment repair
- `test/DSL/Pipeline/LoweringTest.lean` — the 3 `LinearProgram` fixtures
- `test/Eval/Plan/NonlinCompileTest.lean` — top-level Plan expectations **3 steps → 2**
- `test/Eval/PropertyOracle/ScanUnroll.lean`, `test/Eval/PropertyOracle/ScanOracle.lean` — guards, **only if** they observe scheduled shape; preserve oracle independence, import no route/Plan helper
- `test/Bridge/AgreementTest.lean` — fixture 12 below
- remaining consumers: `test/Eval/EntryTest.lean`, `test/Eval/Plan/{CompileTest,SignatureTest,AdapterTest,DifferentialTest,ContractTest}.lean`, `test/Eval/PropertyOracle/Gen.lean`, `test/DSL/CompileExamplesTest.lean`, `test/Eval/PropertyOracleScanTest.lean`
- `experiments/jax_bridge/{EvalPlanSmoke,EvalPlanAffineSmoke,EvalPlanAffineCorpus,EvalPlanCodegen}.lean`

**Implementation**

1. `schedule` accepts the post-`finalizeScans` logical program; `LinearProgram` becomes a deprecated
   alias; `splitNonlins` returns the same schedulable type for regression callers. Six known match
   sites (§0.2).
2. Public `route` = checked `physicalizeForRoute` then existing `routeCore`, preserving the
   `wellFormedDom` guard and its exact `shapeMismatch` payload.
3. Flip `compileToScheduled` and `compile` **in the same change**, keeping the public factorization.
4. Agreement: port `compile_eq_physical_route`; restore `compile_wellFormed` with its **type
   unchanged**. Do not thread fragment evidence into `wf_typeMatch`, `wf_singleOutput`, or `wf_topo`
   — the donor proves Agreement needs only successful `routeCore`, external-count equality, and
   `wellFormedDom`.
5. Apply the FreshM policy in §1 and add an exact regression that `compile` and
   `compileToScheduled >>= route` agree on result, error, **and final state**.
6. Delete the donor-only `scheduleLogical` record adapter once `schedule` takes the logical shape.
7. Work the consumer list above. Most updates are mechanical (fewer statements, no `%nl` names).

**Fixture (1)** — fixture 12 of the master plan, the only one this task adds:

| # | Fixture | Donor + change |
|---:|---|---|
| 12 | Exact-type regression pinning the **unchanged** public `compile_wellFormed` statement | new, in `test/Bridge/AgreementTest.lean`. Verified 2026-08-26: that file is 12 lines and `#check`s only `@realize_fromThreadedComposed_agree`, `@agree_dom`, `@agree_cod` — **`compile_wellFormed` is genuinely unguarded**, so a silent weakening would currently go unnoticed. Follow the file's existing idiom: add `#check @compile_wellFormed`. |

**Mutation cycles (2)**

1. Reinsert `splitNonlins` into `compileToScheduled` → logical-count / no-generated-name fixtures fail.
2. Restore the old split-shape oracle guard after the flip → the oracle guard fails.

**Gate** — the full master-plan day-5 gate; every command must be green:

```bash
cd leanncd
"$HOME/.elan/bin/lake" build DSL.Pipeline.LoweringTest DSL.Pipeline.RouteWeaveTest DSL.Pipeline.ScanAffineTest
"$HOME/.elan/bin/lake" build Bridge.AgreementTest Bridge.AcsetCodecTest Eval.Plan.NonlinCompileTest Eval.Plan.DifferentialTest
"$HOME/.elan/bin/lake" build DSL.CompileExamplesTest Eval.EntryTest Eval.Plan.AdapterTest Eval.Plan.CompileTest Eval.Plan.ContractTest Eval.Plan.SignatureTest
"$HOME/.elan/bin/lake" build Eval.PropertyOracle.ScanOracle Eval.PropertyOracleScanTest
"$HOME/.elan/bin/lake" build JaxExperiment
"$HOME/.elan/bin/lake" env bash experiments/jax_bridge/run-evalplan.sh
"$HOME/.elan/bin/lake" env bash experiments/jax_bridge/run-evalplan-affine.sh
"$HOME/.elan/bin/lake" env bash experiments/jax_bridge/run-evalplan-affine-corpus.sh
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

> **Known pre-existing gap (confirmed 2026-08-26, while executing Task 2):** `lake build
> JaxExperiment` fails in `experiments/jax_bridge/EvalPlanCodegen.lean` — stale `RawEvalPlan`/
> `CheckedPlanStepEvidence` field references, untouched by any Task 1/2 commit (`git diff` against
> each confirms it), so this predates the branch. Matches the "repair experiments/jax_bridge" item
> already open from the 2026-08-21 checkpoint. The `run-evalplan*.sh` scripts depend on
> `JaxExperiment` and so also fail. Out of scope for Task 2; everything else in the gate was
> independently verified green (`Tests` 8657 jobs, `LeanNCD` 8543 jobs, commits `4e49935` +
> `041696a`). Carried into the master plan (§3.3) too.

---

### Task 3 — diagnostic differential

**Outcome.** `test/DSL/Pipeline/RouteFragmentDiagnosticTest.lean` pins that removing the split phase
changed *no* common-domain diagnostic, and that every state delta is exactly the removed split mints.

**Files**

- `test/DSL/Pipeline/RouteFragmentDiagnosticTest.lean` — **new**
- `lakefile.toml` — add `"DSL.Pipeline.RouteFragmentDiagnosticTest"` to the `Tests` `globs` list
  (it is an explicit list, not a wildcard — §0.2 — so an unregistered module silently never runs)

**Implementation.** Transplant the 19 named cases from
`fixtures/RouteFragmentDiagnosticSeed.lean`, then **replace every local scheduler / physicalizer /
compiler reference with the production entry point**. A passing test that still exercises the seed's
local pipeline is not a production regression — this is the single most likely way this task is
completed wrongly.

Retain exactly: all 19 case identities, constructors, payloads, error precedence, and final states;
the two direct-route cases at start 7; composition checks for cases 1, 2, 16 at starts 0, 7, 41
(nine observations, not extra corpus cases). Preserve the intentional distinctions rather than
smoothing them:

- removed split mints on cases 5, 16, 17, 18;
- case 16: same `cyclicDataflow`, old state 4 → new state 2;
- case 19 (escaped `%nl2`): **old rejects, new accepts** — an intentional bug fix, not a regression.

Donor paths for the cloned cases are in §0.4b.

**Mutation cycles (3)** — against **production** check order and route output, never a cloned helper:

1. Change the production rank-error constructor/payload → case 2 fails.
2. Swap `checkReadRanks` / `checkDtypes` → the dual-defect precedence case (4) fails.
3. Corrupt successful routed `nExternal` → exact result comparison fails.

**Gate**

```bash
cd leanncd
"$HOME/.elan/bin/lake" build DSL.Pipeline.RouteFragmentDiagnosticTest
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

---

## §3 Review plan

Per-task review after each task. Then **two independent whole-branch reviews with different lenses** —
this is the tier that has produced every slice's most valuable finding, and it is explicitly not the
place to economise:

1. **Pipeline lens** — logical scheduling, physicalization, collision proofs, route equality, the
   case × class table's completeness (every cell classified; no silent-ignore survivors).
2. **Proof/consumer lens** — Agreement evidence and unchanged public `compile_wellFormed`, unchanged
   `RouteSpec` statements, oracle independence, FreshM state policy, and the 31 consumer call sites.

Reviewer 1 owns the §0.3 finding specifically: confirm class 6 is closed and that `physicalizeOne`
and `fragmentWidth` were changed *together*.

---

## §4 Stop conditions

Stop and report rather than improvise (CLAUDE.md Rule 13's "genuinely blocked" clause) if:

- physicalization needs to invoke scheduling;
- an internal identifier can collide with any source name;
- a logical output cannot map uniquely to one fragment exit;
- old and new routed presentations differ on any common-domain case;
- `compileToScheduled >>= route` compatibility or final-state equality is lost;
- any common-domain error constructor, payload, or precedence changes;
- any pre-split failure state changes, or a post-split delta is not exactly the removed split mints;
- preserving route equality would require splitting scan bodies;
- any existing `RouteSpec` theorem statement must change;
- `compile_wellFormed` cannot be restored through a physical witness;
- the independent oracle would have to import Plan or route implementation;
- closing case-table class 6 would change a diagnostic reachable from `TLProgram.compile`.

Do **not**, under any of these: land a partial API flip, generalize `routeCore`, extend categorical
scans opportunistically, add compensating UID mints, or revive the rejected shared-split design.

The master plan time-boxes Task 1 to five focused days with a day-3 checkpoint (adapter compiles
`sorry`-free, collision proofs complete, no scheduler call in physicalization, five decisive
equality cases passing). In this decomposition that checkpoint is **Task 1's gate**; if Task 1's gate
cannot be reached, stop there rather than starting Task 2.

---

## §5 Definition of done

- `compileToScheduled` returns logical nonlinear assignments with zero route-generated names.
- `compile = compileToScheduled >>= route`, including final FreshM state, over one scheduling pass.
- Public `route` accepts logical schedules and owns checked private physicalization;
  `PhysicalRouteProgram`'s real constructor is inaccessible outside the route boundary.
- `LinearProgram` remains a deprecated compatibility alias.
- Fragments are contiguous, collision-free, non-rescheduling; every top-level nonlinear assignment
  routes as exactly two generators.
- **Every one of the ten physicalization input classes is classified, with class 6 closed to a
  reject and no cell reading "silently ignored."** `physicalizeOne` and `fragmentWidth` agree.
- Scans remain one opaque categorical node; `.scan`/`.scanPre` payloads survive byte-for-byte.
- `routeCore` and every `RouteSpec` statement unchanged; public `compile_wellFormed` restored with
  its exact original type and guarded by fixture 12.
- All 19 compile-diagnostic + 2 route-domain + 9 composition observations exact, with every state
  delta explained as removed split mints.
- `RouteFragments` is reachable from `import LeanNCD` and documented in `LeanNCD/DSL/AGENTS.md`.
- All three task gates green, all **15** mutation cycles run as mutate/fail/restore/pass with the
  failing assertion named, and both whole-branch reviews green or their findings adjudicated.
- No `sorry`, `admit`, or `axiom` added.

**Not done here, and not to be quietly started:** the 145-case corpus, `BlockStep` generalization,
nonlinear scan admission, and the documentation sweep. Those are the next four slices.
