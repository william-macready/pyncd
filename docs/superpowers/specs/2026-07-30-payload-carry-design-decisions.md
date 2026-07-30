# Payload-carry pass — settled design decisions (pre-plan)

> **Status:** decisions SETTLED, plan NOT YET WRITTEN. Written 2026-07-30 at a session boundary so the
> implementation plan can be authored without re-deriving any of this. Evidence base:
> [`papers/semantic_payload_audit.md`](../../../papers/semantic_payload_audit.md) plus a ~230k-token
> code survey (findings inlined below with `file:line`).
>
> **Next action:** write the implementation plan (superpowers:writing-plans), then execute
> subagent-driven. Do **not** re-litigate the decisions in §2; they were made with the user.

## 1. Scope of this pass

From the audit's three buckets, the user chose **bug fixes + the carry bucket**. The routed
*reject* gates (mask, `UnaryOp`, `ScatterOpts`, iverson, `recurMorphism`) are **OUT** — a later pass.

| Item | What |
|---|---|
| **D14** | Fix the stale `elementwiseFn` comment (`Bridge/AcsetCodec.lean:172-180`) |
| **D12** | `splitStmt` drops `rhs.agg` (`Lowering.lean:45`, and `:47-49`) |
| **D13** | `brOpOfIdx`'s `_ => .contract` is reachable from CSV (`AcsetCodec.lean:87-103`) |
| **Carry** | dtype tag + auxiliary nonlin/agg tag on `BrBaseP`, threaded to codec + realize |
| **Docs** | Two stale docs claiming `splitNonlins` splits scans (`leanncd/realize.md:194`, `papers/code_walkthrough.md:378`) |

## 2. Decisions made with the user (do not re-open)

**D-1. The dtype tag is STEP-LEVEL on `BrBaseP`** (not per-weave on `AxisP`). Rationale: a
step-level field is being added anyway for D-2, so the marginal cost is ~zero; per-axis dtype
denormalizes an array-level property across N axes (a representable illegal state — exactly what
this codebase's thesis opposes) and has no home for rank-0; and eval's own notion is per-step-output
(`combineFor` keys on the output *name*). **Accepted cost:** `weaveToArrayType_congr`
(`Bridge/Agreement.lean:67-70`) no longer holds as stated → Agreement conjunct-2 (`:188-233`) needs
rework. This is the largest non-mechanical cost in the pass and it is *bounded and located*.

- **Sub-decision (mine, open to revision):** the tag means **this step's OUTPUT dtype**. `cod` uses
  it; each input's dtype is derived from its *producing* step's tag via `nameToStep`, falling back to
  `.reals` for externals. This keeps `dom` correct without denormalizing.

**D-2. The scan op-label loss is fixed by an AUXILIARY TAG, not by touching `op`.** A relu-scan
keeps `op = .scan` and surfaces the relu in the new tag. **Consequence worth knowing:**
`ScanAffineTest.lean:25-26` (`#guard hasOp reluScan .scan`, `#guard ! hasOp reluScan .scanAffine`)
therefore stays true — **no test renegotiation**. That cost evaporates precisely because `op` is
untouched.

**D-3. `brOpOfIdx?` is the totality-preserving variant** — `brOpOfIdx n := (brOpOfIdx? n).getD .contract`,
plus the `#guard` totality check. The fully-partial variant restates 5 theorems and `realizeSBr`
and is a project, not a fix. Note `restructure_suggestions.md:155-158` holds a counter-position
(keep the table, add a `#guard`) — this decision honors both.

## 3. Reuse design (the user's explicit instruction: no parallel code paths)

These are the four places a naive implementation would fork a parallel path. **Each has a reuse
answer already worked out.**

**R-1. dtype classification must be SHARED with `combineFor`, not mirrored.** `combineFor`
(`Eval/Contract.lean:133-139`) already encodes "how do I decide this output's semiring/dtype":
```lean
def combineFor (decls : List Decl) (nm : String) (agg : AggOp) : Combine :=
  match agg with
  | .max => Combine.max
  | .min => Combine.min
  | .sum => match decls.find? (fun d => d.name == nm) with
      | some (.predicate _ _) => Combine.bool
      | _                     => Combine.real
```
Writing a new `dtypeFor decls nm` in `Lowering.lean` would be exactly the parallel path to avoid.
**Instead:** extract ONE classifier and make both sides project from it — this is the Spike-2
`Factor.read?` / `LHSSlot.axisSpec?` pattern applied a third time.
- Suggested shape: `inductive SemiringP | real | bool | tropicalMax | tropicalMin` (4 ctors =
  exactly `Combine`'s 4 values), with `def outputSemiring (decls : List Decl) (nm : String) (agg : AggOp) : SemiringP`
  as the single decision site. Then `combineFor` becomes a projection (`.real => Combine.real`, …)
  and the bridge tag is another projection.
- **This subsumes the agg half of D-2**: `agg = .max` ⇒ `.tropicalMax`, so the auxiliary tag does not
  need a separate agg field.
- **Placement/import check (MUST verify first):** needs `Decl` + `AggOp` (both `DSL/Ast.lean`).
  `Ast.lean` imports `DSL/Target.lean`, so **`Target.lean` must NOT import `Ast.lean`** — see R-2.
  `Eval/Contract.lean` and `Lowering.lean` both reach `Ast.lean`, so `Ast.lean` is a viable home.

**R-2. The auxiliary nonlin tag is `Option BrOp` — do NOT invent a new enum.**
- **Hard constraint:** `Nonlin` cannot go in `BrBaseP`. `Ast.lean` imports `Target.lean`, so
  `Target.lean` cannot import `Ast.lean` (cycle) — and `Nonlin` carries `BoolExpr` anyway, which is
  the mask, which is explicitly OUT of scope this pass.
- **Reuse answer:** `BrOp` *already* has `relu | sigmoid | tanh | gelu | leakyrelu | softmax |
  normalize | l2normalize` (`Target.lean:54-70`), and `PointwiseFn.toBrOp` / `AxiswiseFn.toBrOp`
  (`Ast.lean:88-94`) already compute exactly this. So the tag is `Option BrOp`, populated by the
  existing functions. No new enum, no cycle, and the codec can reuse `brOpIdx` for it.
- **Computing it for a scan:** must scan ALL of `sc.stepStmts` (`Lowering.lean:338-341`) for a
  non-identity `nonlinOf`. **NOT `repStmt`** — `repStmt` takes the head recurrence stmt
  (`Lowering.lean:302-305`) and `splitStmt` always emits the `.identity` pre-activation first
  (`Lowering.lean:38-51`), so `repStmt.nonlinOf` is *always* `.identity` for a split scan. Verified
  empirically.

**R-3. `brOpOfIdx?` must be the ONLY table.** Define `brOpOfIdx? : Nat → Option BrOp` and redefine
`brOpOfIdx n := (brOpOfIdx? n).getD .contract`. Two independent 15-arm tables would be the parallel
path. The existing `@[simp] brOpOfIdx_brOpIdx` restates to `brOpOfIdx? (brOpIdx op) = some op` and
the old form follows.

**R-4. The codec must reuse existing slots, not add new ones.**
- **dtype → `ArrayRow.datatypeTag`** — it *already exists* (`Acset/SBrInstance.lean:22,37`), is
  already `| reals | natural | bool`, and **already round-trips through CSV**
  (`Acset/Io.lean:26,95`; `Acset/Csv.lean:138,144-148`). Only `blankArrayRow`'s hardcoded `.reals`
  (`AcsetCodec.lean:179`) changes. ⚠ `from_outputRows` (`:466-477`) / `from_inputRows` (`:481-494`)
  state their RHS as a literal `blankArrayRow i s false`, so both statements change.
- **`DTypeP` must be a NEW computable tag in `Target.lean`** — `Base/Br.lean:6-8`'s `DType` has **no
  `deriving` clause at all**, no `bool` constructor, and lives behind a Mathlib import.
  `BrBaseP` derives `DecidableEq, Repr, Lean.ToExpr, Inhabited` and `TargetTest.lean:13,15`
  exercises `DecidableEq`+`ToExpr`. Mirror `Acset.DataTag`'s three constructors so the codec mapping
  is a straight projection.
- **nonlin tag → pack into `EquationRow.lhsName`** via `Nat.pair` alongside the op index
  (`AcsetCodec.lean:206` is `lhsName := some (natToUnary (brOpIdx b.op))`). Reuses `natToUnary` /
  `unaryToNat` and the existing `Nat.pair` round-trip lemmas; touches only `decode_op` (`:966-989`),
  `mem_from_equations` (`:1349-1367`), `from_equation_find` (`:1370-1379`).

## 4. Survey facts a planner needs (verified; don't re-derive)

- **`decls` is NOT at `toBrBaseP`/`buildStep`** (`Lowering.lean:465-503`) but IS at `routeCore`
  (`:553-560`, via `sp : ScheduledProgram` which carries `decls` and `env`). Threading is a 1-line
  call-site change **plus inserting the parameter into 23 `buildStep` theorem statements** in
  `RouteSpec.lean` (lines 94, 112, 129, 135, 182, 210, 238, 249, 260, 372, 384, 413, 423, 431, 442,
  452, 469, 493, 600, 625, 648, 673, 693). Mechanical, no strategy change. `Agreement.lean` never
  names `buildStep` — only `routeCore_getD`'s statement (`RouteSpec.lean:126-135`) changes there.
- **Spike 6a's claim HOLDS for RouteSpec, NOT for AcsetCodec.** The six field projections are
  single-field `rw [(buildStep_ok_eq h).1]; rfl` off one characterization — a new field needs at most
  **one new `rfl` projection**. But `decodeStep_eq` (`AcsetCodec.lean:1405-1474`) closes by structure
  eta with 6 rewrites; a 6th field needs a **new round-trip `have` + a 6th rewrite**. That is the
  extraction lemma 6a did not anticipate — say so honestly in the completion report.
- **Give the new fields DEFAULTS** (`dtype : DTypeP := .reals`) so the 4 existing `BrBaseP` literals
  keep compiling: `test/Bridge/RealizeTest.lean:26-29` and `:57-58`,
  `test/DSL/Pipeline/TargetTest.lean:8-10`, `test/DSL/Pipeline/RecurMorphismTest.lean:20-21`.
  Remove the default once `toBrBaseP` computes a real value.
- **No positional `⟨…⟩` 5-arg `BrBaseP` construction exists anywhere** — all 6 sites use
  structure-instance syntax, and `BrBaseP` is only ever *read* by field projection. So a new field
  breaks nothing structurally.
- **A free computational tripwire:** `test/Bridge/AcsetCodecTest.lean:15-48` has 5 `#guard`s of
  `toThreadedComposed (fromThreadedComposed P) = P`, decided by `DecidableEq ThreadedComposed` — so
  it compares every field of every step on the nose and **will fire the moment a new field isn't
  encoded/decoded**. Use it; don't write a parallel check.
- **D12 is worse than the audit said:** BOTH halves of `splitStmt` omit `agg` (`:45` semantically
  wrong, `:47-49` harmless-but-should-be-explicit), and it is an **eval bug too** —
  `compileToScheduled` includes `splitNonlins` and `Eval/Scan.lean:35-38` / `Eval/Contract.lean:149`
  read `rhs.agg` off post-split stmts. Unreachable from surface syntax (`Syntax.lean:183-185` makes
  `tl_nonlin (…)` and `tl_agg (…)` mutually exclusive) but reachable programmatically — so **the fix
  needs a programmatic test or nothing guards it**.
- **Baseline is sorry-free** in all seven files involved (`Lowering`, `RouteSpec`, `AcsetCodec`,
  `Realize`, `Target`, `Agreement`, `Structural`). Use `#eval!` in probe scripts — the transitive
  tower has sorries (`Base/Br.lean:307`, `Core/Weave.lean:32`, `Instances/StBr.lean:15-21`) so plain
  `#eval` aborts.
- **Unguarded surfaces to be careful of:** nothing asserts `dtype = .reals` anywhere, so the dtype
  change is **unguarded at the realize layer** — add a test. `BrOp.toString` (`Target.lean:72-87`) is
  pinned by no test at all, though Python dispatches on those strings. Brittle pins to avoid
  disturbing: `test/Acset/IoTest.lean:24-28` (exact 12-column header + data row),
  `test/Acset/FixtureTest.lean:27-44` (byte-for-byte vs Python fixtures — do not regenerate),
  `test/Acset/CsvTest.lean:67-71` (exact `"reals"/"natural"/"bool"` strings).

## 5. Suggested task sequence

1. **D14** — comment-only; it sits on the same 9 lines as the dtype work (`AcsetCodec.lean:172-180`), so do it first to avoid churn.
2. **D12** — one-line fix ×2 + a programmatic regression test.
3. **D13** — `brOpOfIdx?` as the single table + the `#guard` totality check.
4. **R-1** — extract `outputSemiring` and make `combineFor` project from it. **Behavior-preserving, no new field yet** — a clean reviewable unit that proves the shared classifier works before anything depends on it.
5. **Field addition** — `DTypeP` + the two `BrBaseP` fields (with defaults), `decls` threaded from `routeCore`, `toBrBaseP` populating both, the 23 RouteSpec statement edits, one new RouteSpec projection.
6. **Codec** — `datatypeTag` for dtype, `lhsName` packing for the nonlin tag, the new `decodeStep_eq` round-trip `have`. `AcsetCodecTest`'s 5 `#guard`s are the gate.
7. **Realize + Agreement rework** — `weaveToArrayType` consumes the dtype; rework `weaveToArrayType_congr` and Agreement conjunct-2. **Highest-risk task; do it last and alone.**
8. **Docs** — the two stale scan claims; update the audit's rows for what now carries; state honestly that 6a's "zero new extraction lemmas" held for RouteSpec but not for the codec.

## 6. Honest completion claim (write this, don't overclaim)

This pass moves **dtype** and **the scan nonlin label** from *silently dropped* to *carried*. It does
NOT establish semantic closure: the mask, `UnaryOp`, `ScatterOpts`, iverson, `recurMorphism`
payload, and the sum-of-products term structure are still dropped without error (a later reject pass).
It does not make eval-vs-routed agreement provable — that still needs a `Br` denotation, which is a
separate deferred milestone (`Base/Br.lean:285-297`).
