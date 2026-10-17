**Verdict: APPROVE WITH MINORS** (0 Critical, 0 Major, 4 Minor). Reviewed from git objects of b1e32963 (parent 7a6a1dfb); nothing built or run.

## 1. Theorem touch: clean

- `compile_eq_physical_route`: the new statement is true and not vacuous. `route` now matches on `desugarMultiWriters logical` and then on `physicalizeForRoute collected`. The new existential witnesses exactly those two results (`hcd`, `hp`), and the hypothesis is a real `compile` success. The proof adds one `rcases hcd` whose error arm closes with the existing `simp [EStateM.run, throw, throwThe, MonadExceptOf.throw, EStateM.throw]` set, unchanged from the other error arms. The rest of the proof is unchanged apart from the witness tuple.
- `compile_wellFormed`: the statement text (signature and `: tc.WellFormed`) is byte-identical before and after. Only the `obtain` pattern grew two binders.
- In Agreement.lean, `sorry|axiom|native_decide|admit` gives 1 hit both before and after, and that hit is prose ("the former `wf_dom` sorry"). No weakening.
- Dependents: the only use of the theorem is in `compile_wellFormed`. `RouteFragmentDiagnosticTest` mentions it only in prose (see the note in §6). No lemma restates the old `physicalizeForRoute logical` shape.

## 2. `route`: clean, apart from F2 and F3

- (a) Identity on single-writer schedules. `scanWriterConflict?` needs 2 or more writer nodes, and `writerGroups` needs `writers.length ≥ 2`. When neither holds, `groups.isEmpty` returns `(sched, [])` unchanged, so physicalization, inventory and route names are byte-identical. The commit touches only 5 files: `RouteFragmentCorpusTest`, `RouteFragmentDiagnosticTest`, `RouteWeaveTest` and `LoweringTest` are not edited.
- (b) `desugarMultiWriters` is pure `Except CompileError`. `route` rethrows it in `FreshM` with `throw e`, the same pattern as `physicalizeForRoute`, and never calls `fresh`, so no counter is consumed. The state pins (`routeErrorIs … 7 7`) are untouched.
- (c) For a hand-built `[Y:=A, U:=Y, Y:=B]`, the collected schedule is `[Y#1:=A, U:=Y, Y#2:=B, Y:=Y#1+Y#2]`. `U` at step 1 reads `Y`, whose only writer is now at step 3, so `routableInOrder` rejects it as `cyclicDataflow`. Before the change, last-wins put `Y` at step 2, which was also rejected. The three diagnostic payload pins were not edited.

## 3. Route-name freshness: clean

`physicalizeForRoute collected` computes `sourceNames := routeNameInventory collected`, which includes `T#k` both as writes and as collector reads. Route names are made of `#` only and are longer than every inventory name, and `T#k` contains a non-`#` character, so they cannot collide. `routeNamesFresh` and the `PhysicalRouteProgram` fields are unchanged, with no new hypothesis. Route-name strings do get longer on multi-writer programs, which has no effect because `ThreadedComposed` carries no names.

## 4. Fixtures: clean (no fixture is vacuous against its stated purpose)

- RT1, RT2, RT3, RT5 and RT6 each differ from the old route in step count:
  - RT1, RT2, RT3: 3 → 4 steps;
  - RT5: 4 → 5 steps;
  - RT6: 5 → 6 steps.
- RT4 passes both before and after by design. It does catch a mutant that collects single-writer names (an A1-M7 analogue: it would add a collector step).
- RT3 (f64) is a dtype-neutrality twin of RT1. `toBrBaseP` and `BrBaseP` carry no dtype, and the `Y#k` clones only add declarations. So no route-side mutant separates RT3 from RT1, which is expected: it witnesses that routing is dtype-neutral. Default f32 is covered by RT1, RT2, RT4, RT5 and RT6.
- Acset fixture 10: the round-trip guard holds both before and after the change, so it cannot fail under A6-M1. It is a codec witness only. `steps.length = 5` is the pin (old: 4).

## 5. Sibling cells

| Cell | Verdict |
|---|---|
| `route` R | confirmed |
| `buildNameToStep` F after `route`; S for direct `routeCore` callers | confirmed; PARKED (not a finding) |
| `routableInOrder` F | confirmed; see F2 for the "agree" prose |
| `routeNameInventory`/`routeNamesFresh` F | confirmed (§3) |
| `physicalizeForRoute` R (caller only) | confirmed; RouteFragments.lean is not in the diff |
| `PhysicalRouteProgram.logical` = collected | confirmed. Consumers of the field are only the package's own invariants (`sourceInventory`, `exactPhysicalization`, `fragmentCount`, `*Preserved`, `layoutChecked`, `exitsChecked`). The `c.logical`/`fixture.logical` hits in `RouteFragmentCorpusTest` are `CorpusCase` fields passed to `physicalizeForRoute` directly, so they are unaffected. `RouteWeaveTest`'s `logical.stmts.length` is a local. |
| `toBrBaseP` F | confirmed, but see F1 |
| `ScheduledValidation` docstring | accurate |

## 6. Prose

The diff adds no `File.lean:NNN` references.

Pre-existing and out of scope (park): `RouteFragmentDiagnosticTest` says that `compile_eq_physical_route` "proves the same thing as a `FreshM` function equality" and that it "pin[s] the routed steps directly". Both were already inaccurate before T6 (the theorem is an existential factorization), and the new conjunct does not change that.

### F1 [Minor] The collector's routed step cannot be told apart from a product (pre-existing gap, now on every multi-writer program)

`ScanStmt.toBrBaseP` @ Lowering; `BrOp.contract` @ DSL/Target ("standard tensor contraction (×, Σ, 0)").

A `BrBaseP` records `op`, `degree`, `inputWeaves`, `outputWeaves` and `reindexings`. All of them are computed from read factors, the LHS and the nonlinearity, never from the term grouping of `body.terms`. So the collector `Y := Y#1[i] + Y#2[i]` (RT2: step 2, `[.internal 0 0, .internal 1 0]`) gets the same step record as `Y := Y#1[i] · Y#2[i]` would. Under `BrOp.contract`'s documented (×, Σ, 0) reading, that record denotes the Hadamard product, while the evaluator and checked plan compute `Y#1 + Y#2`.

This is not a T6 regression. A user-written `A[i] + B[i]` already routes this way, and the old multi-writer route was wrong in a different way (dead step, reader sees the last writer only). But the T6 docstring ("one `.assign` (sum aggregation, identity nonlinearity, labelled `.contract`) publishes `T`") and plan decision 4 present `.contract` as the right label. `agg := .sum` is Σ over contracted axes, not the ⊕ across terms.

Fix: in T8, state in the `route` docstring and in DSL/AGENTS.md that routing erases sum-of-products term structure, so the collector's step is not distinguishable from a product. Park a real fix (an additive `BrOp`, or splitting terms into steps) with S3's `BrOp`/bridge lockstep. Cost: 0 extra dispatches for the documentation; the real fix is S3-sized.

### F2 [Minor] "The two agree once every name has one writer" overclaims

This claim appears in the `route` docstring, the `collectDefinitions` docstring and p2b_findings. Counter-scenario: a hand-built plain node that reads a scan-scratch name (in `writes` but not in `outputs`). `isTopoOrdered`'s `eligible` never makes it ready, so it is rejected there. `routableInOrder` finds no `buildNameToStep` entry and returns `true`, and `buildStep` then throws `undeclaredName`. Both reject, but with different arms and payloads.

Fix: reword to "they accept the same collected schedules" (or "agree on plain dataflow"). This is prose only.

### F3 [Minor] On hand-built `route`, collection now runs before `rejectComplexDecls`

`desugarMultiWriters` classifies writers before `physicalizeForRoute` runs `rejectComplexDecls`. Scenario: a hand-built `ScheduledProgram` with a complex `typedTensor` declaration and two `.scatter` writers of one name. It now reports `multiWriterScatter` instead of `unsupportedElementType`. For an admitted set, `Decl.cloneAs` also clones the complex declaration under `T#k` before it is rejected.

This is unreachable from `compile`, because `buildDeclEnv` rejects complex declarations first. Every such program is still rejected, only with a different payload. But DSL/AGENTS.md says a complex declaration is "rejected, used or not, before anything classifies it", and `route` is listed as an entry that enforces this.

Fix: call `rejectComplexDecls logical.decls` at the top of `route`, or record `route`'s new precedence in the case × entry table of `ComplexElementTypeTest`. Cost: Direct path, about 1 small dispatch, or a T8 note.

### F4 [Minor] No fixture pins the deviation's safety claim on the direct-`route` path

The claim that `route` can skip `collectDefinitions` rests on `routableInOrder` rejecting a reader that comes before the last writer once the schedule is collected (§2c). RT1 cannot show this, because `compile` reorders it before `route` sees it. Suggested pin: `route` on the hand-built `[Y:=A, U:=Y, Y:=B]` (donor: an existing hand-built schedule in `RouteFragmentDiagnosticTest`) gives `cyclicDataflow "routeCore: cyclic dataflow (topoSort fallback)"`. This is optional; cost is 1 fixture on the Direct path.
