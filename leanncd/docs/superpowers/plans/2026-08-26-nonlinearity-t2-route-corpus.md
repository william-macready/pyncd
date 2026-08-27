# Slice T2 — durable nonlinear route corpus, payload matrix, and Bridge regression

**Scope:** Task 2 only of
[`papers/nonlinearity_split_pair_direct_lowering.md`](../../../../papers/nonlinearity_split_pair_direct_lowering.md)
(that document's §3.4, "durable nonlinear route corpus and realization regression"). That document
remains the canonical design record; this is the executable plan for its second slice.

**Deliberately NOT in this slice** (each is a later slice, planned only once this one lands, per
CLAUDE.md Rule 13):

| Master-plan task | Deliverable | Owned by |
|---|---|---|
| Task 3 | `RawPlanBlock.steps : Array BlockStep` generalization | a later slice |
| Task 4 | nonlinear Plan scan admission + independent oracle | a later slice |
| Task 5 | differential documentation + stale-document sweep + closure | a later slice |
| (carried) | closing the **third class-6 door** (`LHSSlot.toReadIdx` collapsing `.iterAt`/`.iterNext`) | a later slice — see §0.4, verified out of scope here |
| (carried) | repairing `experiments/jax_bridge/EvalPlanCodegen.lean` | pre-existing gap, see §0.6 |

This slice adds **tests only**. It changes no production module, no `RouteSpec` statement, no
`routeCore`, no public API. If a corpus case appears to require a production change, that is a §4
stop condition, not a fix to make here.

---

## §0 Verified baseline

Everything in this section was executed in this worktree against `main` at `7cc8e4d` on 2026-08-26.
Re-run §0.1 before editing; a failure at that point is base drift, not a transplant defect.

`"$HOME/.elan/bin/lake" build LeanNCD` — **exit 0** at `7cc8e4d`.

### 0.1 Donor artifacts — CURRENT status, not the recorded one

The master plan's §1.3.1 "Verified baseline" says all five donors typecheck. **That is no longer
the whole truth, and the part that is still true is misleading.** Run from `leanncd/`:

```bash
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/fixtures/FixtureSupportSeed.lean
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/fixtures/PayloadConservationSeed.lean
"$HOME/.elan/bin/lake" env lean ../papers/implementation_seeds/nonlinearity_route_fragments/fixtures/RouteFragmentCorpusSeed.lean
```

Observed 2026-08-26 in this worktree:

| Donor | Exit | What it means |
|---|---|---|
| `FixtureSupportSeed.lean` | **1 (FAILS)** | `sameOldAndProposedRoute supportSmoke` and `… supportBranch` both `did not evaluate to true` |
| `PayloadConservationSeed.lean` | 0 | **false green** — see below |
| `RouteFragmentCorpusSeed.lean` | 0 | **false green** — see below |

**Root cause — one defect, three donors.** Since Task 1, public `route` *itself* physicalizes. Every
one of these donors pre-physicalizes locally and then hands the already-split program to `route`,
which splits the still-nonlinear consumer **a second time**. Measured directly (`H[i] := relu(W[i,j]
· x[j])`, one logical statement):

```
production route of LOGICAL:                      steps = 2
donor leg (pre-physicalize, then public route):   steps = 3
donor "old" leg (splitNonlins, then public route): steps = 3
```

- `FixtureSupportSeed` **fails** because it compares its pre-physicalized leg against public
  `TLProgram.compile`, which is now single-physicalized: 3 ≠ 2.
- `PayloadConservationSeed` and `RouteFragmentCorpusSeed` **pass** because *both* of their legs are
  double-physicalized, so they agree with each other at 3 steps while production is at 2. Their
  green is evidence that two equally-stale legs match — **not** evidence that any transplanted
  assertion will hold.

This is the same staleness family the previous slice found in `RouteFragmentDiagnosticSeed`, and
production already documents the trap: `Pipeline/Lowering.lean`'s `route` docstring says
*"Regression tests that compare the old split pipeline against the new one must therefore terminate
at `routeCore`, not at public `route`"*, and `test/DSL/Pipeline/RouteFragmentDiagnosticTest.lean`'s
`case19` pins a 2-statement pre-split program compiling to 3 physical steps.

**Consequence for this plan.** The donors' *case constructions* and *assertion shapes* are the
valuable part and transplant directly. Their *legs* do not. Every leg is respecified in §0.2 and
re-verified there. **`FixtureSupportSeed.lean`'s failure is expected and must not be "fixed"** — it
is a disposable donor whose entire local pipeline (`logicalSchedule`, `physicalizeForRoute`,
`RouteFragment`, `internalName`, `fragmentsContiguous`, `privateNamesFresh`, `fragmentShapesOk`) is
superseded by production `LeanNCD/DSL/Pipeline/RouteFragments.lean` and by
`test/DSL/Pipeline/RouteWeaveTest.lean`'s fixtures. **This slice takes nothing from
`FixtureSupportSeed.lean`.** Its two smoke shapes (`H[i] := relu(W[i,j] · x[j])`, and the
relu/tanh/join branch) are already live as `RouteWeaveTest`'s fixtures 1 and 4.

### 0.2 The corrected legs, and the corpus re-verified end to end

Both legs were respecified to terminate at `routeCore` (mirroring `RouteWeaveTest`'s
`oldRouteCore` / `newRouteCore`), the whole 145-case corpus was regenerated verbatim from
`RouteFragmentCorpusSeed.lean`, and every assertion re-run against **production**
`physicalizeForRoute` / `route`. Compiled and executed via
`bash .claude/skills/slice-plan/check-snippet.sh` on 2026-08-26:

```
corpus size = 145
commonExact FAILURES = 0 : ids []
collisionTransition FAILURES = 0 : ids []
cases with .plain carrying iter slots = 0
scan-family cases = 40
non-aroundScans scan cases = 32
collision old error = LeanNCD.CompileError.cyclicDataflow "routeCore: cyclic dataflow (topoSort fallback)"
collision new steps = 3
```

and the 19 named payload fixtures, against production `physicalizeForRoute`:

```
fixtures = 19, distinct names = 19
payloadConserved FAILURES = 0 : []
representedMatchesOld FAILURES = 0 : []
route+ACSet round-trip FAILURES = 0 : []
opaque mask pair equal     = true
opaque iverson pair equal  = true
opaque metadata pair equal = true
opaque scanPre pair equal  = true
```

**The slice's central premise is therefore verified before a line of it is written**: all 137
common-domain cases are exactly route- and ACSet-equal, all 8 collision cases transition from
`cyclicDataflow` rejection to acceptance, and all 19 payload fixtures conserve their payloads. The
implementer is transcribing a measured result, not discovering one.

The two leg definitions below are the **only Lean this plan authors**; both were compiled with
`check-snippet.sh` in the exact form printed here.

```lean
import LeanNCD.DSL.Pipeline.Lowering

namespace T2Legs
open LeanNCD Std

def toLinear (sp : ScheduledProgram) : LinearProgram :=
  { decls := sp.decls, stmts := sp.stmts, env := sp.env, extNames := sp.extNames }

/-- OLD leg: `splitNonlins → schedule → routeCore`, wrapped into a complete `ThreadedComposed`.
    It must NOT end at public `route`: `route` physicalizes, so it would split the already-split
    consumer a second time (2 steps become 3). -/
def oldTC (sp : ScheduledProgram) : Option ThreadedComposed :=
  match (do
      let split ← splitNonlins (toLinear sp)
      let ordered ← schedule split
      match routeCore { ordered with explicitSizes := sp.explicitSizes } with
      | .error e => throw e
      | .ok (steps, routing) =>
          return ({ steps, routing, nExternal := ordered.extNames.card } :
            ThreadedComposed)).run 0 with
  | .ok tc _ => some tc
  | .error .. => none

/-- NEW leg: public `route` on the LOGICAL schedule — one physicalization, production code. -/
def newTC (sp : ScheduledProgram) : Option ThreadedComposed :=
  match (route sp).run 0 with
  | .ok tc _ => some tc
  | .error .. => none

end T2Legs
```

An `oldErr` companion (identical body, returning the `CompileError` instead of the value) supplies
the collision family's old-rejection observation; it was compiled and run alongside the above.

### 0.3 The corpus is hand-built `ScheduledProgram`s, not `tlprog!` sources

Verified by reading `RouteFragmentCorpusSeed.lean`: every one of the 13 generators returns a
`ScheduledProgram` assembled from `ScanStmt` constructors (`scheduled [...] {"X"}`), and likewise
all 19 payload fixtures (`one (.plain (.assign …))`). **No corpus case goes through `tlprog!`,
`assignUIDs`, `lowerArith`, or `finalizeScans`.** Two consequences the implementer must hold onto:

1. This is deliberate and correct for the task: §3.4 wants the *route boundary* exercised, and
   hand-built schedules are exactly the widened caller set §2.4 admits. Do not "improve" the corpus
   by rewriting families as surface programs — that would silently shrink what it covers.
2. It also means the corpus **can** present shapes unreachable from `TLProgram.compile`. That is
   what makes §0.4 a question rather than an assumption.

The single source-level cross-check in this slice is `RouteWeaveTest.freeNormAxiswiseProg`, which
the previous slice made **public on purpose** for exactly this slice (its own docstring says so).

### 0.4 The third class-6 door — verified OUT OF SCOPE for this slice

The open gap recorded in `LeanNCD/DSL/Pipeline/RouteFragments.lean`'s header, `LeanNCD/DSL/AGENTS.md`'s
case table, and the master plan's §2.4 table: `LHSSlot.toReadIdx` (`LeanNCD/DSL/Ast.lean`) maps
`.iterAt a n` and `.iterNext a` both to `.axis a`, discarding the pinned literal / the `+1` shift. A
`.plain (.assign …)` carrying an iteration slot would therefore take `physicalizeOne`'s split arm and
emit a producer/consumer pair whose read and write coordinates disagree.

**Two independent checks, both run, both negative:**

1. **`finalizeScans` structurally cannot produce it.** Read directly
   (`LeanNCD/DSL/Pipeline/Structural.lean`): the *only* expression in `finalizeScans` that builds a
   `ScanStmt.plain` is `plainStmts.map ScanStmt.plain`, where
   `plainStmts := nonPre.filter (fun s => s.iterInfo.isEmpty && (dep.getD s.lhsName []).isEmpty)`.
   `Stmt.iterInfo` (`LeanNCD/DSL/Ast.lean`) is nonempty **iff** the statement has an `.iterAt` or
   `.iterNext` slot. Every statement with a nonempty `iterInfo` lands in `iterStmts`, is placed in a
   connected component by the union-find over iteration-axis UIDs, and is emitted inside a
   `ScanStmt.scan` node (as `baseStmts` or `stateRecur`); `.recurMorphism` becomes `.scanPre`.
   `schedule` only reorders. So on the surface-compile chain the door is unreachable — this
   confirms, rather than assumes, the reasoning recorded in the `RouteFragments.lean` header.
2. **This corpus does not open it either.** Because §0.3's corpus bypasses `finalizeScans`, check 1
   is not sufficient on its own. Measured over all 145 generated cases *and* all 19 payload
   fixtures: **0 cases contain a `.plain` statement with a nonempty `Stmt.iterInfo`.** Every
   `.iterAt`/`.iterNext` in the corpus sits inside a `.scan` node (families `nonlinearBase`,
   `nonlinearRecurrence`, `coupledScans`, `multiAxisScans`, and `aroundScans`' scan node); the
   `aroundScans` family's two `.plain` statements use `.free l`, not `.iterAt`/`.iterNext`.

**Decision (state this in the completion record):** the third class-6 door is out of scope for this
slice, because no case in the 145+19 corpus reaches it and no surface program can construct one.
It remains open and remains a later slice's work.

**But the corpus must not silently drift into it.** Task 1 ships a mechanical guard so a future
generator edit cannot open the door without failing the build. Compiled with `check-snippet.sh`:

```lean
import LeanNCD.DSL.Pipeline.Lowering

namespace T2Door
open LeanNCD

/-- The open third class-6 door: no generated logical program may present a `.plain` statement
    carrying an `.iterAt`/`.iterNext` slot. `finalizeScans` cannot produce one, and this corpus
    bypasses `finalizeScans`, so the invariant is asserted rather than inherited. -/
def plainIterSlots (sp : ScheduledProgram) : Bool :=
  sp.stmts.any fun
    | .plain s => !s.iterInfo.isEmpty
    | _ => false

end T2Door
```

### 0.5 Structural claims checked against the tree

| Claim | Verified? | Exact finding |
|---|---|---|
| `test/DSL/Pipeline/RouteFragmentCorpusTest.lean` does not exist; its parent does | yes | `test/DSL/Pipeline/` holds 8 files (`LoweringTest`, `RecurMorphismTest`, `RouteFragmentDiagnosticTest`, `RouteWeaveTest`, `ScanAffineTest`, `StructuralTest`, `TargetTest`, `TraverseTest`) |
| `test/Bridge/RealizeTest.lean` exists | yes | 75 lines; imports only `LeanNCD.Bridge.Realize` |
| `test/Bridge/AcsetCodecTest.lean` exists | yes | 52 lines; 5 bare `#guard` round trips over `tl!{…}` sources, **no named defs** — appending fixtures cannot collide |
| `RouteWeaveTest.lean` has room for more fixtures | yes, but see §0.7 | 561 lines, namespace `LeanNCD`; fixtures 1–11, 13, 14; **every helper and fixture except `fixedNames` and `freeNormAxiswiseProg` is `private`** |
| `Tests` lakefile uses an explicit `globs` list | yes | a new test module is invisible until added |
| Test modules may import other test modules | yes | e.g. `Eval.Plan.AdapterTest` imports `Eval.Plan.ScanCompileTest`; `Eval.Plan.EvalPlanTest` imports `Eval.Plan.ScanTest` |
| `NonlinCompileTest.reluProg` / `.softmaxProg` are public | yes | `test/Eval/Plan/NonlinCompileTest.lean`, both plain `def` |
| `CompileTest.acceptedSched` is public | yes | `test/Eval/Plan/CompileTest.lean` |
| `RecurMorphismTest.stepTC` is **private** | yes | must be **cloned**, cannot be imported |
| `ParsePredicatesTest.band` is **private** | yes | must be **cloned**, cannot be imported |
| `LoweringTest` carries the cross-call-site `producerSlots` guard | yes | its `PRODUCERSLOTS` fixture runs `splitStmt` and `physicalizeOne` on the same statement and compares producer slot lists directly |
| `realize` is **noncomputable** | yes | `RealizeTest.lean` uses `noncomputable example` + `#print axioms`; there is no `#eval` of a realized value anywhere in it |

### 0.6 Pre-flight conflict scan against the just-finished slice

§3.4 was written before Task 1's implementation existed. Five of its statements need adjusting;
none of them invalidates the task.

**(a) §3.4's Files list names `RouteWeaveTest.lean`; this plan does not modify it.** Verified reason:
`RouteWeaveTest`'s 14 fixtures are `TLProgram`-sourced and its legs are typed `TLProgram → ScanProgram
→ FreshM (List BrBaseP × List (List Wire))`; this slice's corpus is `ScheduledProgram`-sourced and
needs `ScheduledProgram → Option ThreadedComposed`. The signatures do not meet, so there is nothing
genuinely duplicated to factor out — the ~10 lines of §0.2 are defined locally in the new module and
a cross-reference comment is shipped in each direction. `RouteWeaveTest` is **imported** (for the
public `freeNormAxiswiseProg` only) but not edited, so its 14 fixtures cannot be disturbed and no
`private` needs lifting. Record this reasoning in the completion record so a reviewer does not read
it as unnoticed duplication.

**(b) §3.4's Files list is otherwise correct**, with `test/DSL/Pipeline/RouteFragmentCorpusTest.lean`
new and `lakefile.toml` needing `"DSL.Pipeline.RouteFragmentCorpusTest"` added to the `Tests` globs.

**(c) §3.4 says "compare … `Bridge/RealizeTest` realization output". Realization output is
not computable.** `realize` is noncomputable and requires a `tc.WellFormed` proof. What
`RealizeTest` actually asserts, and what this slice must therefore assert, are the *shaped*
surrogates that file already uses: `wellFormedDom`, `externalPort`, `(realizeDom tc).length`,
`ThreadedComposed.codObj.length`, `wirePlan` selections, plus `noncomputable example`
typechecks. §1.3.1's own wording — "**shaped** runtime realization assertions" — is the accurate
one; §3.4's "realization output" is not. Do not attempt to `#eval` a realized morphism.

**(d) §3.4's Task-2-owns-Agreement implication is stale.** The previous slice already restored
`compile_wellFormed` and landed `compile_eq_physical_route`; `test/Bridge/AgreementTest.lean` already
`#check`s `@compile_wellFormed`. This slice adds no Agreement work.

**(e) `lake build JaxExperiment` and the three `run-evalplan*.sh` scripts fail on `main` at
`7cc8e4d`** — a pre-existing gap in `experiments/jax_bridge/EvalPlanCodegen.lean` recorded by the
previous slice. They are **not** in this slice's gate and must not be repaired here.

### 0.7 Recurring-defect sweep — where §3.4's own numbers do not survive contact

The `slice-plan` skill's rule for "instance N of a known family" applies here in an unusual form:
the recurring family is **a predicted count that was derived against a stale leg**. §3.4's twelve
mutation predictions were written before this design existed in code. Each was re-derived against
the actual corpus, measured in this worktree:

| §3.4 prediction | Measured basis | Verdict |
|---|---|---|
| Reuse one internal name → **48** failures | **48** cases have ≥2 nonlinear plain statements (chains depth≥2: 24, branches 8, unreadOutputs 8, aroundScans 8) | ✅ consistent |
| Reorder fragment steps → **113** failures | **113** cases have ≥1 nonlinear plain statement (⇒ ≥2 physical steps) | ✅ consistent — but note this is 113 **of 145**, including all 8 collision cases; 105 of the 137 |
| Recompute externals from private reads → **113** failures | same 113 | ✅ consistent, same caveat |
| Split nested scan bodies → **32** structural failures | **32** scan-family cases excluding `aroundScans` | ✅ consistent |
| Route from fragment **entry** not exit → **64** failures | **48** cases read a name written by a nonlinear (width-2) fragment — the only cases where entry ≠ exit is observable. Composition: chains depth≥2 (24), branches (8), repeatedReads (8), aroundScans (8) | ❌ **64 is not derivable.** 48 is. |
| Mishandle `.freeNorm` → **48** structural/value failures | **9** cases contain a `.freeNorm` slot at all (the whole `freeNormPositions` family) — and **route equality detects none of them** | ❌ **wrong twice**, see below |

**The `.freeNorm` finding is the one with teeth.** Measured directly: physicalizing all three
`.freeNorm` slot positions *without* the `producerSlots` degrade yields a routed presentation
**identical** to production's in every position (`route-equal under the .freeNorm mutation = true`,
n = 0, 1, 2), while the producer slot lists differ visibly (`.freeNorm i` vs `.free i` in slot 0).
This matches `LeanNCD/DSL/Ast.lean`'s `producerSlots` docstring, which states that `.free a` and
`.freeNorm a` produce the same `slotWeave` axes and that route equality cannot detect drift.

So: a corpus-wide route-equality assertion is **structurally incapable** of catching the `.freeNorm`
mutation, at any count. Its guard must be a **structural producer-slot comparison**, and the ceiling
is 9 corpus cases plus the payload matrix's two axiswise fixtures plus the source-level
`freeNormAxiswiseProg` cross-check. **Task 1 must assert `.freeNorm` degradation structurally on all
9 cases**, not rely on aggregate route equality; a plan that only tightened the number would still
have shipped a mutation cycle that cannot fail.

**Rule for every mutation cycle in this slice: record the *observed* failure count from the
mutate/fail cycle, not the predicted one.** Where the observed count differs from §3.4's, the
completion record says so and the master plan's §3.4 text is corrected in the Task 5 sweep. A cycle
that produces **zero** failures is a defect in the fixture, not a pass.

### 0.8 Snippet verification

Every Lean block in this document (§0.2's `toLinear`/`oldTC`/`newTC`, §0.4's `plainIterSlots`) was
compiled in its final printed form with:

```bash
bash .claude/skills/slice-plan/check-snippet.sh <file.lean>
```

All other code in this slice is a transcription of a donor fixture construction that was executed
against production in §0.2. Bash blocks are shell commands, not Lean, and are exempt.

---

## §1 Global constraints

Exact values, and what is deliberately excluded.

- **The old leg terminates at `routeCore`. Never at public `route`.** Public `route` physicalizes;
  routing an already-split program through it splits the consumer again (measured: 2 steps → 3).
  Any old/new comparison that calls public `route` on a pre-split program is wrong regardless of
  whether it passes.
- **No local physicalizer survives anywhere in this slice.** Production `physicalizeForRoute` is the
  only physicalization. If a transplanted donor helper named `physicalize`, `physicalizePlain`,
  `physicalizeLoop`, `privateName`, `internalName`, `fragmentsContiguous`, `privateNamesFresh`, or
  `fragmentShapesOk` appears in the diff, it is a defect.
- **Nothing under `papers/` is imported.** `papers/` never enters Lake's module search path.
- **Exactly 145 generated cases in 13 families, and exactly 19 named payload fixtures, counted
  separately.** Family counts: chains 32, contractions 24, `freeNormPositions` 9, branches 8,
  repeatedReads 8, unreadOutputs 8, adversarialNames 8, `nl0Collisions` 8, nonlinearBase 8,
  nonlinearRecurrence 8, aroundScans 8, coupledScans 8, multiAxisScans 8. Derived counts to pin:
  **137** non-collision, **8** collision, **40** scan-family, **32** scan-family excluding
  `aroundScans`. Semantic overlap must never be allowed to inflate 145 or 137.
- **The `%nl0` family's old rejection is `CompileError.cyclicDataflow "routeCore: cyclic dataflow
  (topoSort fallback)"`, and its new acceptance is real.** Do not weaken the common-domain equality
  claim to pretend the old bug accepted them.
- **Projection equality is never relabelled as semantic equivalence.** For masks, Iverson
  predicates, dtype metadata, and `scanPre` bodies, the assertion is "the physical field is
  preserved **and** the current categorical projection omits it" — two claims, stated separately.
- **No `.plain` statement in any generated program carries an `.iterAt`/`.iterNext` slot** (§0.4),
  guarded mechanically.
- **`Bridge/RealizeTest` assertions are shaped surrogates**, not realized values (§0.6c).
- **No production file changes.** No `sorry`, `admit`, or `axiom`.

**Discoverability.** `RouteFragmentCorpusTest` is not done when it compiles: `lakefile.toml`'s
`Tests` `globs` is an explicit list, so an unregistered module silently never runs. Registration is
part of Task 1's deliverable, and Task 1's gate includes `lake build Tests`.

---

## §2 Task breakdown

Three tasks. Boundaries chosen by the reviewer test: *a reviewer could meaningfully reject one while
approving its neighbour.*

| Task | Deliverable | Fixtures | Mutation cycles | Risk driver |
|---|---|---:|---:|---|
| 1 | 145-case generated corpus, 13 families, + differential legs + door guard | 145 cases + 25 named guards (G1–G25) | **6** | one generator bug moves many cases at once; the `.freeNorm` guard must be structural, not route-based |
| 2 | 19-case named payload matrix + opacity pairs | 19 fixtures + 4 opacity pairs | **6** | each fixture is hand-picked and hand-verified; the failure mode is *asserting the wrong thing*, not a systemic bug |
| 3 | Bridge regression: ACSet round trips + shaped realization | 8 fixtures | **1** | different files, different conventions; realization is noncomputable so the assertions are structurally unlike Tasks 1–2 |

**Why 1 and 2 are separate.** They share a file but not a failure mode. Task 1's cases come from one
deterministic generator: a single arithmetic slip in `chainProgram` moves 32 cases at once, and the
reviewer's job is to check the generator and the counts. Task 2's 19 fixtures have no shared
generator; each is a hand-picked clone of a named donor and the reviewer's job is to check that each
one asserts what its name claims — in particular that the four opaque classes are not quietly
described as semantically preserved. A reviewer could accept the generator and reject the opacity
framing, or vice versa.

**Why the 13 families are *not* split further.** Splitting the 5 scan families (40 cases) out of the
8 routing families would leave Task 1 shipping a `corpus` list that fails its own
`corpus.length == 145` and family-count guards by construction — an artificial boundary whose first
task cannot be green against its own spec. They share the generator infrastructure, the `corpus`
list, the count guards, and one test cycle, and a bug in `scanNode` breaks the scan families
together rather than independently. Per the skill's merge rule, they merge. The scan-specific
observations are instead an *enumerated* sub-deliverable inside Task 1 with their own gate line, so
a reviewer can still reject them by name.

**Why 3 is separate despite being small.** It touches two existing files with dependents, both
already in the `Tests` globs; §3.4 itself demands two reviews split exactly along
"route/indexing equality" vs "scan/realization/ACSet preservation"; and its distinctive failure mode
— writing a realization assertion that `realize`'s noncomputability makes vacuous — cannot occur in
Tasks 1 or 2.

**Mutation-cycle mapping — all twelve of §3.4's, plus one this plan adds, none dropped:**

| §3.4 mutation | Task | Predicted → plan's expectation |
|---|---:|---|
| Route from fragment entry rather than exit | 1 | 64 → **expect 48**, record observed |
| Reuse one internal name | 1 | 48 → 48 |
| Reorder fragment steps | 1 | 113 → 113 (of 145) |
| Recompute externals from private reads | 1 | 113 → 113 (of 145) |
| Split nested scan bodies | 1 | 32 → 32 |
| Mishandle `.freeNorm` | 1 | 48 → **≤ 9, and only against a structural guard** |
| Drop nonlinear aggregation to sum | 2 | max/min physical + route assertions fail |
| Drop an axiswise mask | 2 | pre-route conservation fails; route stays equal |
| Change a nonlinearity tag | 2 | exact generator sequence fails |
| Clear declarations / environment / explicit sizes | 2 | metadata conservation fails |
| Replace a nontrivial affine read by identity | 2 | exact reindexing fails |
| Replace a nested `scanPre` body by default | 2 | byte-for-byte payload conservation fails |
| **(added here)** corrupt the ACSet encoding of a nonlinear op tag | 3 | the new nonlinear ACSet round-trip fixture fails — otherwise Task 3 would ship with no cycle at all |

**Every cycle means: mutate the implementation under test, _observe failure_, restore, _observe
pass_ — recorded in the ledger with the failing assertion named and the observed failure count.**
Predicting a failure, or mutating the assertion instead of the implementation, does not count.

---

### Task 1 — the 145-case generated corpus

**Outcome.** `test/DSL/Pipeline/RouteFragmentCorpusTest.lean` deterministically generates 145 cases
in 13 families, proves all 137 common-domain cases exactly route- and ACSet-equal between the old
split leg and production `route`, proves the 8 `%nl0` cases transition from `cyclicDataflow`
rejection to acceptance, pins the scan-opacity observations, and mechanically forbids the third
class-6 door.

**Files**

- `test/DSL/Pipeline/RouteFragmentCorpusTest.lean` — **new**
- `lakefile.toml` — add `"DSL.Pipeline.RouteFragmentCorpusTest"` to the `Tests` `globs` list

**Implementation**

1. Transplant the 13 generators from
   `papers/implementation_seeds/nonlinearity_route_fragments/fixtures/RouteFragmentCorpusSeed.lean`
   **verbatim**: `chainProgram`, `contractionProgram`, `freeNormProgram`, `branchProgram`,
   `repeatedProgram`, `unreadProgram`, `adversarialProgram`, `collisionProgram`, `scanNode`,
   `nonlinearBaseProgram`, `nonlinearRecurrenceProgram`, `aroundScanProgram`, `coupledProgram`,
   `multiAxisProgram`, plus `axis`/`i`/`j`/`k`/`l`/`m`, `rhs`, `rhs2`, `scheduled`, `Family`,
   `CorpusCase`, `generateFamily`, `corpus`. Preserve every offset and count. Do **not** import
   `ScanGen.template2`.
2. Define the legs from §0.2 locally (`toLinear`, `oldTC`, `oldErr`, `newTC`). Ship the
   cross-reference comment required by §0.6a. Delete the donor's `physicalize`,
   `oldRoute`, `newRoute`, `oldPhysicalSchedule?`, `allSourceNames`, `declName?`, `producerSlot`,
   `mutateRouteFromEntry`, `mutateRoutedProgram`, and the three `enable…Mutation` toggles — every
   mutation in this slice is a **production** mutation, per §1.3.1 item 8.
3. `import LeanNCD.DSL.Pipeline.Lowering`, `import LeanNCD.Bridge.AcsetCodec`, and
   `import DSL.Pipeline.RouteWeaveTest` (for the public `freeNormAxiswiseProg` only).
4. Ship the §0.4 `plainIterSlots` guard and assert it is `false` for every one of the 145 cases.
5. Register the module in `lakefile.toml`.

**Fixtures and guards** — 145 generated cases plus 14 named guards. Every generator's donor is the
same file; the per-family donor shapes are recorded in the seed's own README table.

| # | Guard | Expected (measured 2026-08-26) |
|---:|---|---|
| G1 | `corpus.length` | 145 |
| G2 | `corpus.map (·.id) == List.range 145` | true |
| G3–G15 | the 13 per-family counts | 32, 24, 9, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8 |
| G16 | non-collision cases | 137 |
| G17 | collision cases | 8 |
| G18 | scan-family cases | 40 |
| G19 | scan-family excluding `aroundScans` | 32 |
| G20 | **common-domain exact**: for all 137, `oldTC == newTC`, ACSet encodings equal, ACSet decode∘encode is the identity on `newTC`, and `newTC.wellFormedDom` | 0 failures |
| G21 | **collision transition**: for all 8, `oldErr` is `cyclicDataflow "routeCore: cyclic dataflow (topoSort fallback)"` and `newTC` succeeds, well-formed, ACSet-round-tripping | 0 failures |
| G22 | **scan opacity**: for the 40 scan cases, `physicalizeForRoute`'s scan payloads (`name`, `axes`, `base`, `recur`, `isAffine`) are byte-identical to the logical ones; for the 32 non-`aroundScans` cases the OLD split leg's scan payloads **differ** (`splitNonlins` splits inside scan bodies) while the complete routes are still equal | 0 failures |
| G23 | **third-door guard** (§0.4): no case has a `.plain` with nonempty `iterInfo` | 0 cases |
| G24 | **`.freeNorm` structural guard**: for each of the 9 `freeNormPositions` cases, `physicalizeForRoute`'s producer slot list equals `producerSlots slots` and carries **no** `.freeNorm`, while the consumer keeps the marker. **Must be a slot-list comparison — route equality cannot detect this (§0.7).** | 0 failures |
| G25 | source-level `.freeNorm` cross-check: `RouteWeaveTest.freeNormAxiswiseProg` compiles to one logical statement, two physical, with the same producer/consumer slot relationship | passes |

G20–G22 were executed against production in §0.2 with 0 failures; G23–G24 were executed in §0.4
and §0.7. The implementer transcribes measured results.

**Mutation cycles (6)** — all against **production** `LeanNCD/DSL/Pipeline/RouteFragments.lean`:

| # | Mutation | Expected failing guard | Expected count |
|---:|---|---|---:|
| 1 | in `physicalizeOne`, map a logical output to the fragment **entry** instead of its exit | G20 | **48** (not §3.4's 64) |
| 2 | make `routeName` ignore its ordinal so two fragments share one internal name | G20 | 48 |
| 3 | reorder the emitted producer/consumer pair | G20 | 113 of 145 |
| 4 | recompute externals from the private producer reads | G20 | 113 of 145 |
| 5 | split nested scan bodies instead of copying `.scan` verbatim | G22 | 32 |
| 6 | drop the `producerSlots` degrade so the producer keeps `.freeNorm` | **G24** | ≤ 9 — and **G20 must remain green**, which is the point of the cycle |

Cycle 6 is the plan's most informative: it demonstrates that the corpus-wide route comparison is
blind to this defect and that only the structural guard catches it. Record both observations.

**Gate**

```bash
cd leanncd
"$HOME/.elan/bin/lake" build DSL.Pipeline.RouteFragmentCorpusTest
"$HOME/.elan/bin/lake" build DSL.Pipeline.RouteWeaveTest DSL.Pipeline.LoweringTest
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

`Tests` and `LeanNCD` must be green **without** any behaviour change: this task adds a test module
and a lakefile line, and nothing existing may move.

---

### Task 2 — the 19-case named payload matrix

**Outcome.** The same module gains a clearly separated section holding 19 named payload fixtures,
counted **separately** from the 145. Represented payloads (operation tags, aggregation, affine
reads) keep exact physical statements *and* exact categorical outputs. Opaque payloads (masks,
Iverson predicates, dtype metadata, nested `scanPre` bodies) keep exact physical fields *and* are
explicitly shown to be omitted by the current projection — two separate claims, never merged.

**Files**

- `test/DSL/Pipeline/RouteFragmentCorpusTest.lean` — new section (Task 1 created and registered it)

**Implementation**

1. Transplant the fixture builders from
   `papers/implementation_seeds/nonlinearity_route_fragments/fixtures/PayloadConservationSeed.lean`:
   `readBody`, `one`, `PayloadClass`, `NamedPayloadFixture`, `pointwise`, `axiswise`, `aggregate`,
   `masked`, `iversonFixture`, `metadataFixture`, `affineFixture`, `scanPreFixture`, `causal`,
   `antiCausal`, `band`, `nestedStepA`/`nestedStepB`, `nestedA`/`nestedB`, and the `fixtures` list.
2. Transplant the assertion helpers `plainPayloadConserved`, `metadataConserved`,
   `scanPreConserved`, `payloadConserved` unchanged — they already read the *physical* program and
   are correct as written.
3. **Replace the donor's local `physicalize` with production `physicalizeForRoute`** (its
   `.scheduled` field), and replace `representedMatchesOld`'s `routeOf (physicalize …)` with Task
   1's `oldTC`/`newTC` legs.
4. Delete the donor's `privateName`, `mutateDropMask`, `mutateAggregation`, `oldPhysicalize`,
   `routeOf`, `acsetOf`, and the four `enable…Mutation` toggles — cycles are production mutations.
5. Keep the payload fixtures out of `corpus`; assert `fixtures.length == 19` and that all 19 names
   are distinct, separately from Task 1's `corpus.length == 145`.

**Fixtures (19)** — each names its donor, in `clone X, change one field` form:

| # | Fixture name | Donor + the single field changed |
|---:|---|---|
| 1–4 | `sigmoid`, `tanh`, `gelu`, `leaky-relu` | clone `NonlinCompileTest.reluProg`'s construction (public, `test/Eval/Plan/NonlinCompileTest.lean`), change **only** the `PointwiseFn` tag |
| 5–6 | `normalize`, `l2-normalize` | clone `NonlinCompileTest.softmaxProg`'s construction (public), change **only** the `AxiswiseFn` tag |
| 7–8 | `relu-over-max`, `relu-over-min` | clone `LoweringTest`'s AGG1 construction, change **only** `agg` to `.max` / `.min`; surface grammar unchanged |
| 9–10 | `causal-mask`, `negated-causal-mask` | clone `AcsetCodecTest`'s causal-attention mask, change **only** the predicate (negate it) |
| 11–12 | `band-iverson`, `negated-band-iverson` | clone `ParsePredicatesTest.band` (**private** — clone, do not import) into the ReLU donor's body; change **only** the Iverson predicate (negate it) |
| 13–14 | `tensor-metadata`, `predicate-metadata` | clone `CompileTest.acceptedSched`'s declaration/environment shape (public), change **only** the `Decl` to `.tensor` / `.predicate` |
| 15–16 | `scale-read`, `shift-read` | clone `LoweringTest`'s strided read, change **only** the `IdxExpr` to `.scale 2 i` / `.shift i 1` |
| 17 | `general-affine-read` | clone `AcsetCodecTest`'s strided convolution read, change **only** the `IdxExpr` to `.affine 1 [(2, i), (-1, j)]` |
| 18–19 | `scan-pre-operation`, `scan-pre-output-weave` | clone `RecurMorphismTest.stepTC` (**private** — clone, do not import), change **only** the nested `op` / **only** the nested output weave. Adapter-local hand-built `scanPre` input; public `recurMorphism` rejection is unchanged |

**Assertions.** Three families, kept separate:

| Guard | Content | Measured 2026-08-26 |
|---|---|---|
| P1 | `fixtures.length == 19` and 19 distinct names | holds |
| P2 | **physical conservation, all 19**: metadata (`decls`, `extNames`, `explicitSizes`, `env`) preserved; for split fixtures, producer body/agg/degraded-slots and consumer name/slots/nonlin/`agg = .sum` exact; for `scanPre`, name/axis/nested body byte-identical | 0 failures |
| P3 | **represented classes match the old leg**: for the 11 `.represented` fixtures, `oldTC == newTC`, ACSet encodings equal, decode∘encode identity | 0 failures |
| P4 | **opacity, 4 pairs**: `causal-mask` vs `negated-causal-mask`, `band-iverson` vs `negated-band-iverson`, `tensor-metadata` vs `predicate-metadata`, `scan-pre-operation` vs `scan-pre-output-weave` each have **equal** routes and **equal** ACSet encodings despite differing physical payloads. Documented in the module as *the current projection omits this field*, explicitly **not** semantic equivalence | all four `true` |

**Mutation cycles (6)** — production mutations only:

| # | Mutation | Expected failing guard |
|---:|---|---|
| 1 | in `physicalizeOne`, force the producer's `agg` to `.sum` | P2 on `relu-over-max` / `relu-over-min`; P3 on the same two |
| 2 | in `physicalizeOne`, drop the axiswise mask when building the consumer | P2 on `causal-mask` / `negated-causal-mask`; **P4 must stay green** — record that the route is unchanged |
| 3 | in `physicalizeOne`, rewrite the consumer's `nonlin` tag | P2 and P3 on all four pointwise + both axiswise fixtures |
| 4 | in `physicalizeForRoute`, clear `decls` / `env` / `explicitSizes` on the physical program | P2 on all 19 |
| 5 | in `physicalizeOne`, replace a nontrivial read index by identity when building the producer body | P2 and P3 on `scale-read` / `shift-read` / `general-affine-read` |
| 6 | in `physicalizeOne`'s `.scanPre` arm, replace the nested body with `default` | P2 on `scan-pre-operation` / `scan-pre-output-weave` |

Cycle 2 is the mirror of Task 1's cycle 6: it must demonstrate that the *route* comparison stays
green while the *physical* assertion fails. Record both observations.

**Gate**

```bash
cd leanncd
"$HOME/.elan/bin/lake" build DSL.Pipeline.RouteFragmentCorpusTest
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

---

### Task 3 — Bridge regression: ACSet round trips and shaped realization

**Outcome.** Nonlinear routed programs round-trip through the ACSet codec at the theorem-level test's
own idiom, and their realization *shape* is pinned in `RealizeTest` — using the shaped surrogates
that file already uses, because `realize` is noncomputable (§0.6c).

**Files**

- `test/Bridge/AcsetCodecTest.lean` — append fixtures 6–9
- `test/Bridge/RealizeTest.lean` — append 4 shaped-realization fixtures

**Implementation**

1. `AcsetCodecTest` uses bare `#guard toThreadedComposed (fromThreadedComposed (tl!{…})) = tl!{…}`
   over source programs and defines no names, so appending cannot collide. Follow that idiom
   exactly.
2. `RealizeTest` imports only `LeanNCD.Bridge.Realize` and builds `ThreadedComposed` values by
   hand (`mkStep`, `tcMatmul`, `tc2Layer`, `tcFan`). To assert on a *routed* program it must also
   `import LeanNCD.DSL.Compile`. Follow the file's `private def` + `#guard` / `example : … := by rfl`
   idiom; keep `noncomputable example` for anything touching `realize`.
3. **Do not** attempt to evaluate a realized morphism, and do not introduce a `WellFormed`
   obligation this slice would have to discharge.

**Fixtures (8)**

| # | File | Fixture | Donor + change |
|---:|---|---|---|
| B1 | `AcsetCodecTest` | pointwise ReLU round trip | clone its fixture 1 (matmul), change the statement to `NonlinCompileTest.reluProg`'s source |
| B2 | `AcsetCodecTest` | axiswise softmax round trip | clone fixture 1, change the statement to `NonlinCompileTest.softmaxProg`'s source |
| B3 | `AcsetCodecTest` | nonlinear chain (two nonlinear statements) round trip | clone B1, append a second nonlinear statement reading its output |
| B4 | `AcsetCodecTest` | nonlinear **scan** round trip | clone its fixture 5 (coupled scan), reduce to a single ReLU recurrence |
| B5 | `RealizeTest` | routed ReLU: `wellFormedDom`, `externalPort` for each external, `(realizeDom tc).length`, `codObj.length` | clone `tcMatmul`'s assertion block, replace the hand-built `tc` with `tl!{ H[i] := relu(W[i,j] · x[j]) }` |
| B6 | `RealizeTest` | routed ReLU `wirePlan` selections + final selection | clone `tc2Layer`'s `wirePlan` block, same substitution |
| B7 | `RealizeTest` | routed nonlinear **chain**: the fragment exit, not its entry, is the wire source | clone B5, use `RouteWeaveTest`'s fixture-3 chain shape (ReLU then a downstream contraction), asserting the `.internal` wire indices |
| B8 | `RealizeTest` | routed opaque **scan**: one step, shaped dom/cod | clone B5, use B4's single-recurrence scan source |

Every asserted value in B5–B8 must be **observed from a real run and transcribed**, not predicted;
the plan deliberately does not pre-state them, because they depend on step and slot numbering the
implementer will read off directly (`slice-plan`: "For fixtures asserting values, also verify the
values").

**Mutation cycle (1)** — the cycle this plan adds so Task 3 is not shipped unguarded:

1. In `LeanNCD/Bridge/AcsetCodec.lean`, corrupt the encoding of a step's nonlinear `op` tag (e.g.
   encode every `op` as `.contract`) → **B1–B4 fail**; restore → pass. Record the observed count.

**Gate**

```bash
cd leanncd
"$HOME/.elan/bin/lake" build Bridge.AcsetCodecTest Bridge.RealizeTest
"$HOME/.elan/bin/lake" build Bridge.AgreementTest
"$HOME/.elan/bin/lake" build Tests
"$HOME/.elan/bin/lake" build LeanNCD
```

---

## §3 Review plan

Per-task review after each task. Then **two independent whole-branch reviews with different lenses**,
exactly the split §3.4 itself requires — this is the tier that has produced every slice's most
valuable finding, and it is explicitly not the place to economise:

1. **Route / indexing lens** — the 13 generators and their counts; that the old leg terminates at
   `routeCore` and never at public `route`; internal-name freshness and injectivity across the
   corpus; fragment entry-vs-exit routing; external arity, degrees, weaves, and reindexings;
   `wellFormedDom`. Owns §0.7's finding specifically: confirm the `.freeNorm` guard is **structural**
   and that a route-only guard was not shipped in its place.
2. **Scan / realization / ACSet-preservation lens** — scan payload byte-identity and the 40/32
   accounting; that the four opacity pairs are described as projection omission and never as
   semantic equivalence; that the Bridge realization assertions are shaped surrogates that can
   actually fail; that no `papers/` seed is imported and no local physicalizer survived. Owns §0.4
   specifically: confirm the third-door guard is present and green, and that the door was not
   quietly closed as a side effect.

---

## §4 Stop conditions

Stop and report rather than improvise (CLAUDE.md Rule 13's "genuinely blocked" clause) if:

- any of the 137 common-domain cases fails exact route or ACSet equality under the §0.2 legs (§0.2
  measured 0 failures; a nonzero count means the tree moved under this plan);
- any of the 8 `%nl0` cases fails to show old rejection *and* new acceptance;
- a scan payload is not byte-identical between the logical program and `physicalizeForRoute`'s
  output, or the 40/32 accounting cannot be reproduced;
- preserving corpus equality appears to require **any** production change — this slice adds tests
  only;
- a corpus case can only be made to pass by routing the old leg through public `route`;
- any mutation cycle produces **zero** failures (the guard is vacuous — a defect, not a pass);
- the corpus cannot be built without a `.plain` statement carrying an `.iterAt`/`.iterNext` slot
  (that would move the third class-6 door into scope and invalidate §0.4);
- an opaque-payload observation cannot be stated without claiming semantic equivalence;
- `Bridge/RealizeTest` would need a `WellFormed` proof obligation this slice must discharge;
- a donor fixture cannot be reproduced without importing something under `papers/`.

Do **not**, under any of these: weaken an equality claim to make a case pass, relabel projection
equality as semantics, retain a local physicalizer, inflate 145 or 137 with semantically overlapping
cases, or repair `experiments/jax_bridge` opportunistically.

---

## §5 Definition of done

- `test/DSL/Pipeline/RouteFragmentCorpusTest.lean` exists, is registered in `lakefile.toml`'s `Tests`
  `globs`, and generates exactly **145** cases in **13** families with the counts in §1.
- All **137** common-domain cases are exactly equal on: complete `ThreadedComposed`, generator
  sequence and routing wires, external arity/domain, degrees, weaves and reindexings, `wellFormedDom`,
  and ACSet encode/decode round trip — with the old leg terminating at `routeCore`.
- All **8** `%nl0` cases show old `cyclicDataflow "routeCore: cyclic dataflow (topoSort fallback)"`
  rejection and new acceptance, stated as a separate claim from the 137.
- The **40** scan-family and **32** split-body observations are pinned separately, so opaque scan
  handling cannot disappear inside aggregate equality.
- The third class-6 door is **guarded**: 0 of the 145 generated programs and 0 of the 19 payload
  fixtures contain a `.plain` statement with a nonempty `iterInfo`. The door itself stays open and
  is recorded as a later slice's work.
- All **19** named payload fixtures pass, counted separately from the 145/137, with physical
  conservation and categorical opacity as **two distinct claims**.
- The four opacity pairs are shown route- and ACSet-equal and are documented as projection omission,
  never as semantic equivalence.
- Bridge fixtures B1–B8 are green, with every asserted value transcribed from an observed run.
- No local physicalizer, no `papers/` import, no production file changed, no `sorry`/`admit`/`axiom`.
- All three task gates green; all **13** mutation cycles run as mutate/fail/restore/pass with the
  failing assertion named **and the observed failure count recorded**; both whole-branch reviews
  green or their findings adjudicated.
- The completion record carries: the §0.1 donor-staleness diagnosis, the §0.4 third-door decision
  with its two verified checks, the §0.6a "no RouteWeaveTest edit" reasoning, and every §0.7
  count correction (64 → 48; `.freeNorm` 48 → ≤ 9 and structural-only) so the Task 5 sweep can
  correct §3.4's text.

**Not done here, and not to be quietly started:** `BlockStep` generalization, nonlinear Plan scan
admission, the differential documentation sweep, closing the third class-6 door, and repairing
`experiments/jax_bridge`. Those are the next slices.
