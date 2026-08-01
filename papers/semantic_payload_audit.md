# Semantic payload audit — what survives the routed path?

> **Status:** evidence complete (2026-07-30), decisions **OPEN**. This is roadmap Stage 3 from
> [`restructure_suggestions.md`](restructure_suggestions.md#review-addendum-2026-07-26-correctness-first-reprioritization).
> Every cell carries a `file:line`; the `NONE` rows are established by grep, not inference.
> **Nothing here is implemented.** The right-hand column is a *recommendation* awaiting a decision.

## Why this exists

`TLProgram` has two back-ends from one source AST:

```
TLProgram ─ compileToScheduled ─→ ScheduledProgram ─→ Eval/*            (interpreted, numeric)
          └ compileToScheduled ─→ ScheduledProgram ─ route →
                                    ThreadedComposed ─→ ACSet codec ─→ Bridge/Realize
```

The routed step record is `BrBaseP` — **exactly five fields** (`DSL/Target.lean:93-99`):
`op : BrOp`, `degree : StObjP`, `inputWeaves`, `outputWeaves`, `reindexings`. Everything the
source can express must fit in those five, or it is silently gone.

The establishing grep over `Lowering.lean`, `Target.lean`, `Bridge/AcsetCodec.lean`,
`Bridge/Realize.lean` for `BoolExpr|iverson|UnaryOp|unaryFn|ScatterOpts|.fill|.reduce|AxisKind|dtype|AggOp`
returns **two** hits total: `Lowering.lean:208` (`Stmt.agg`) and `Realize.lean:38-42` (the
`dtype := .reals` hard-code). Zero hits for the rest.

## Verdict

Of 9 audited features: **6 have no `BrBaseP` field at all**, 2 are *partial and lost entirely
for any scan node*, 1 is structurally collapsed. A tenth loss (sum-of-products term structure)
was found incidentally. **The routed path today faithfully represents a narrow fragment:
contraction/reduction wiring with axis reindexing.** Everything semantic beyond that — masks,
elementwise ops, scatter policy, dtype, per-term scoping — is dropped without error.

There is **no eval-vs-routed agreement theorem, and none is currently constructible** (see
finding F). That is the mechanism by which all of the above stays invisible.

## The table

| # | Feature | Source | Scheduled eval | `BrBaseP` field | ACSet codec | Realization | Guarding test | **Recommendation** |
|---|---|---|---|---|---|---|---|---|
| 1 | Axiswise mask `Option BoolExpr` | `Ast.lean:83` | ✅ both paths (`Eval/Nonlin.lean:103-111` → `perRow` `mask?`) | **NONE** — `Lowering.lean:487` binds it to `_` | not encoded; `ArrayRow.opPredicate` hard-set `none` (`AcsetCodec.lean:180`), doc names masked-softmax as dropped (`:174-176`) | no | **none routed.** `LoweringTest:6-25` only reaches `ScheduledProgram` | **Reject routed** (named error) until carried |
| 2 | The nonlinearity (`PointwiseFn`/`AxiswiseFn`) | `Ast.lean:68,74` | ✅ both paths agree | **`op`, PARTIAL** — `toBrOp` is injective on all 8, **but the label is lost for *any scan node***: `Lowering.lean:483-484` short-circuits to `.scanPre/.scanAffine/.scan` before `s.nonlinOf` is consulted | faithful (`brOpIdx`, `decode_op` proves recovery) | label only → `BrBase.op : String`; **no denotation exists** | partial: softmax only. **No test for relu/sigmoid/tanh/gelu/leakyrelu/normalize/l2normalize** reaching `BrOp` | **Carry** (label already fits); **fix the scan short-circuit**; add per-op tests |
| 3 | `UnaryOp` (incl. `.recip` from `/`) | `Ast.lean:102,108` | ✅ both paths (`Gather.lean:78`) | **NONE — structurally unrepresentable.** Stripped at `Factor.read?` (`Ast.lean:240-243`); no `UnaryOp` value exists downstream | nothing to encode | nothing | **NONE** (eval-only: ST6/CL4/DF4/CM1b/GN5) | **Reject routed** until carried — see *3c note* below |
| 4 | `ScatterOpts.fill` / `.reduce` | `Ast.lean:129-132` | ✅ plain (`Scatter.lean:35,52-55`); **✗ scan — scatter rejected outright** (`Scan.lean:51`) | **NONE** — `Lowering.lean:489` matches `..` | nothing | nothing | **none routed** (op tag only) | **Reject routed** for non-default opts (surface only emits defaults, `Structural.lean:779`) |
| 5 | `AggOp` (sum/max/min) | `Ast.lean:97,118` | ✅ plain; ✅ scan **but see B** | **`op`, PARTIAL** — `.max/.min/.sum → .maxreduce/.minreduce/.contract` only in the `.identity`-nonlin `.assign` arm; lost for scatter **and any scan** | faithful for what reached `op` | label only | **NONE** — `maxreduce`/`minreduce` never appear as `BrOp.*` in `test/` | **Carry** (fits `op`); fix the scan/scatter loss; add tests |
| 6 | Predicate/bool dtype | `Ast.lean:7-9,20`; `Combine.bool` | ✅ plain (`combineFor`); **✗ scan — `evalScan` never receives `decls`** | **NONE** — no dtype field; `decls` dropped at `route` (`ScheduledProgram` has them, `ThreadedComposed` does not) | slot **exists** (`ArrayRow.datatypeTag`, has a `bool` ctor) but hard-set `.reals` (`:179`) | **defaulted** `.reals` (`Realize.lean:41-42`), with a self-documented obligation at `:38-40` | **NONE** | **Carry** — the codec slot already exists; this is the cheapest real win |
| 7 | `Factor.iverson` | `Ast.lean:107` | ✅ both paths (`Gather.lean:76`) | **NONE — structurally unrepresentable.** `Factor.read?` → `none`, so it yields no read, **no wire, and no degree axis** | nothing | nothing | **NONE** (eval-only RL6–RL8) | **Reject routed** until carried |
| 8 | Scan bodies | `Types.lean:16` | ✅ fully (`evalScan`) | **COLLAPSED** to one flat `BrBaseP`; per-stmt nonlinearities and term structure gone. Documented at `Compile.lean:31-33` | what survived | what survived | op tag only; **no body-content test** | **Accept as a documented abstraction boundary** (this one is by design) |
| 9 | `recurMorphism` / `.scanPre` | `Ast.lean:137` | **✗ hard error** on all three eval entries | **NONE — the entire `tc` is discarded.** Emits a literally empty step `{op := .scanPre, degree := [], inputWeaves := [], outputWeaves := [[]], reindexings := []}`; the iteration axis is dropped too | encodes the empty step | realizes an empty step | op tag only — and **demonstrably does not guard content**: `RecurMorphismTest:19-27` feeds `outputWeaves := [[.tiled]]` and asserts only the tag | **Reject at compile** — accepted-then-discarded is the worst state |
| — | *(incidental)* sum-of-products term structure | `Ast.lean:247-248` | ✅ per-term contraction scoping is load-bearing (`Contract.lean:63-69`) | **NONE** — `A·B + C` and `A·B·C` yield identical read-factor lists | — | — | **NONE** | **Reject or carry** — decide with #1/#3/#7 |

## Verification log (2026-07-30) — probes, and one account that was wrong

Executable probes, not code reading. **Apply this lesson to the un-probed findings.**

| Finding | Verdict | Detail |
|---|---|---|
| **C** (`agg` drop) | ✅ **CONFIRMED + FIXED** | Mutation test: reverting the fix yields `[(identity, sum), (relu, sum)]` where `.max` was expected. Fixed in `78dd276`. |
| **D** (`brOpOfIdx` default) | ✅ **CONFIRMED + FIXED** | Fixed in `14b1353`; both round-trip lemmas axiom-free. |
| **#4** (`recurMorphism`) | ✅ **CONFIRMED** | Probe: `compile → .ok, ops=[BrOp.scanPre]`; `eval → .error "scanPre unsupported (S)"`. Payload discarded. Accepted-then-discarded, as described. Fix needs a policy decision (see below). |
| **#17** (CSV error swallowing) | ✅ **CONFIRMED + FIXED** | Probe: `encodeSize` errors on a compound `SizeExpr`, yet `writeSBr` emitted `"axis_uid,size\r\nRawAxis:1,\r\n"` and returned normally. `writeSBr` now returns `Except CsvError` (`b1468cf`). The `encSizeOpt` docstring's "sizes here are `.lit`/`.var` so total" was an assumption stated as fact. |
| **#5** (unsized scan) | ✅ **CONFIRMED + FIXED** — *and my first verdict on it was wrong* | The audit's account was **right**: `evalScan`'s `getD 0` was the mechanism, and the fix (`0f58e0b`) closes it — re-probed, the panic is **gone** and the error is the new one (`unsized iteration axis 'l' (uid 3)`). My earlier "MECHANISM WRONG" verdict was **my** error: when writing the structure probe I retyped the program as `l + 1` instead of the reported `l +1`, so I compared two *different* programs. One variable at a time. |
| **#5b** (NEW — found while re-probing) | ✅ **CONFIRMED + FIXED 2026-07-31** | `l + 1` and `l +1` used to elaborate to **different LHS slots**: `` `(tl_lhs_slot\| ident "+1") `` is a single ATOM (`Syntax.lean:192`), so `l +1` → `.iterNext` (a scan recurrence) while `l + 1` → `.affine (.shift l 1)` (a shifted write) — it even flipped the axis kind `nat`→`real`. `finalizeScans` then found no `iterNext` and emitted `SCAN … axes=[]`, a degenerate axis-less scan. **The natural spacing silently meant something else** rather than failing. Fixed by the `iter` declaration (both spacings now elaborate identically; a new compile phase, `reclassifyIterSlots`, promotes to `.iterNext` iff the axis is declared `iter`, else rejects with `CompileError.scanAxisNotIter`) — see `docs/superpowers/specs/2026-07-30-scan-axis-declaration-spike.md` and `DSL/AGENTS.md`. |

| **H** (NEW 2026-07-30 — probed) | 🔴 **OPEN, unfixed** | The size carried by an axis **kind** (`axis l : ℕ[3]`) is **write-only**: it is parsed into `AxisKind.nat (some (.lit 3))` (`Elab.lean:39`) and never read. Probe (three programs differing only in the axis declaration): `axis l : ℕ = 3` → `OK`; **`axis l : ℕ[3]` → the same "unsized iteration axis" error as declaring nothing at all**. So the language has a spelling that *looks* like an extent pin and pins nothing. See finding **H** below. |

**Method note.** #5's write-up was right that something is broken and wrong about what. Both it and
the original restructuring doc were produced by reading; the corrections came from running. Treat the
remaining un-probed findings (#6/#17, and the routed-payload rows in the table below) as *unverified
mechanisms* until a probe says otherwise.

## Cross-cutting findings

> **These letters are the canonical labels for the actionable items.** Wave A of the
> [work order](restructure_suggestions.md#suggested-spike-ordering-and-dependencies) is
> **finding C** (`agg` drop), **finding D** (`brOpOfIdx?`), and the carved-out actionable half of
> **finding E** (the stale `elementwiseFn` comment — cited as *finding E-comment* / *E'*). An earlier
> draft numbered these `D12`/`D13`/`D14` after a subagent survey's section headings; that numbering is
> **retired** (it was untraceable to any document, and its `D` prefix collided with finding D).

**B. A second eval divergence — plain vs scan, on dtype.** `evalScan`'s signature never takes
`decls` (`Eval/Scan.lean:68-69`), so it picks its `Combine` from `rhs.agg` alone
(`:36-40`) and never reaches `combineFor`'s predicate branch (`Contract.lean:133-139`). A
`predicate`-declared tensor written **inside a scan** therefore contracts in ℝ `(×,+,0)`
instead of Boolean `(∧,∃)`. This is the same bug Spike **4c** describes — the audit supplies
the mechanism and confirms 4c's prescribed fix (thread `decls` through `evalScan`) is the right
one. Second scan divergence: `Stmt.scatter` is rejected inside a scan (`Scan.lean:51`), so
feature 4's payload is unreachable there.

**C. A latent `agg` drop on BOTH paths (new — in no spike).** `splitNonlins` builds the linear
pre-activation step as `{ body := rhs.body, nonlin := .identity }` (`Lowering.lean:45`) —
**without `agg := rhs.agg`** — so it silently takes the `.sum` default, dropping max/min.
Currently unreachable from surface syntax (the grammar makes `tl_nonlin (…)` and `tl_agg (…)`
mutually exclusive, `Elab.lean:217-222`, so `relu(maxreduce(…))` cannot be parsed) but
reachable for a programmatically built AST. **Cheap fix, worth doing regardless of the audit.**

**D. `brOpOfIdx` is a confirmed meaning-changing default.** `AcsetCodec.lean:87-103`, final arm
`| _ => .contract`. Reachable from CSV: `decodeStep` gets the tag via `unaryToNat` of a raw
string (`:300-301`), and a **missing `EquationRow` yields `"" ⇒ 0 ⇒ .contract`**. So a garbled
relu/softmax/scatter/scan tag becomes a plain contraction with no error. `brOpOfIdx_brOpIdx`
proves the round trip only in range. **Fix: expose `brOpOfIdx? : Nat → Option BrOp`** at the
boundary (bridge hardening).

**E. What the codec drops by construction.** `blankArrayRow` (`:177-180`) sets `name`,
`operatorTag`, `normAxis`, `maxValue`, `bias`, `elementwiseFn`, `opPredicate`, `wireLabel` to
`none` and `datatypeTag := .reals`. Only `slot`, `isInput`, and input-row `wireLabel` carry
content; the op index rides in `EquationRow.lhsName`. Note the doc at `:172-176` claims
`elementwiseFn` carries the op index — **that comment is stale**; the code sets it `none`.

**F. There is no eval-vs-routed agreement theorem, and none is constructible today.** This is
the most consequential finding, and it reshapes **E5**.

`Bridge/Agreement.lean` proves two things, *neither* of which is eval-vs-routed:
1. `compile_wellFormed` (`:379-382`) — every compiled program is `WellFormed`: four
   *combinatorial* wiring conjuncts (rank agreement, producer⊳consumer weave match, ≥1 output,
   reads ⊆ live pool). Says nothing about values, ops, dtypes, or masks.
2. `realize_fromThreadedComposed_agree` (`:407-413`) — this is **DSL-routed vs CSV-routed**:
   both sides are the *same* routed path differing by an acset round trip. It reduces to
   `toThreadedComposed (fromThreadedComposed tc) = tc`. Also: `test/Bridge/AgreementTest.lean`'s
   own `#print axioms` records it **uses `sorryAx`**.

The blocker is structural: the routed path terminates in `BrMorph`, a `Quotient` of raw `Hom`
syntax (`Base/Br.lean:52-58`), and **no denotation into numbers exists** — interpreting `Hom`
into a concrete model is an explicitly deferred milestone (`Base/Br.lean:285-297`, "THE PLANNED
ROUTE — NbE / initiality"). Every `realize*` is `noncomputable`, so it cannot even be `#eval`'d.

⟹ **E5 as written ("prove `evalScheduled … ≈ interpret (realize (route …))`") is not merely
unscheduled — it is currently impossible.** It requires the `Br` interpreter first. The
tractable interim is a *shape/label* agreement theorem plus per-feature reject gates (below),
not a numeric commuting diagram.

**G. A scan base case does not name its own iteration axis; base↔recur pairing is positional
(new 2026-07-30, PROBED 2026-07-30 — turned out UNREACHABLE via surface syntax).**
`Elab.lean:244` elaborates a literal LHS slot as `.iterAt (scanAxis "") n` — **empty name, uid 0**.
So `G[j, 0]` never records *which* axis it pins. `finalizeScans` repairs this after the fact
(`Structural.lean:849-851`): it finds the same-named stmt carrying a recur slot and has each base
`iterAt` adopt that step's `iterNext` axis **at the same slot position**.

The precise miss arm is `Stmt.adoptBaseIterAxes` (`Structural.lean:827-835`): a base `iterAt` whose
position has no matching step `iterNext` is **"left as-is"**, keeping `name ""` / `uid 0`. The
concern was that grouping-by-UID would then land such a base in a uid-0 group *separate from its
own recurrence*, silently zero-filling the boundary.

**Probed: three constructions, all fail loud, none silent.** (1) single-axis, iteration axis
last-in-base/first-in-step (`G[j,0]` / `G[l+1,j]`) ⇒ `missingBaseCase`. (2) multi-axis, one axis
adopts correctly and one doesn't ⇒ `inconsistentScanAxes` (the mismatched slot's placeholder-uid
leaks into the stmt's own axis set via the *correctly*-adopted sibling slot, so the component's
axis count no longer matches the recurrence's advance set). (3) two independently-mis-ordered
scans in one program ⇒ `missingBaseCase` fires on the first, not masked by the second.

**Root cause it's unreachable — verified by direct inspection, not just inference:**
`assignUIDs` (`Structural.lean:572-578`) mints exactly one fresh, mutually-distinct, non-zero UID
per *distinct axis name* in the whole program (`p.axisNames`, a de-duplicated name list) via a
`memo : HashMap String UID`, then relabels every occurrence of that name to its minted UID. The
empty string `""` — the anonymous placeholder's name (`Elab.lean:244`, `scanAxis ""`) — is just
one more entry in that name list: it gets minted its OWN UID like any other name, not left at its
construction-time default of `0`. Confirmed by dumping `resolveDecls`'s output directly on a
correctly-adopted program (`axis l : ℕ = 3 / G[j,0] := Z[j] / G[j,l+1] := …`): `l` → uid 1, `j` →
uid 2, and the base's placeholder (name `""`) → uid **3** — not 0. (An earlier draft of this
finding claimed uid 0 stays exclusively reserved for the placeholder; that's not the mechanism —
the placeholder is relabeled too, just to a value distinct from every *other* name's value.) The
guarantee that actually holds: **two axes are only ever merged into the same component if they
share a name**, since the memo is name-keyed and injective (`freshNonZero` is strictly
increasing, so distinct memo entries are distinct UIDs). A real, surface-declared axis is never
named `""`, so its UID can never coincide with the placeholder's — an un-adopted base's axSet can
never *quietly* equal a real recurrence's axSet; it always ends up a strict superset (case 2,
loud) or disjoint (cases 1/3, loud). The `outputAxesConsistent` (`Lowering.lean:457-460`) guard
is unrelated (compares outputs of an already-grouped coupled scan, post-grouping) and was never
the mechanism that closes this — `missingBaseCase`/`inconsistentScanAxes` are.

**The residual risk is programmatic ASTs only** — code that builds `AxisSpec`/`Stmt` values
directly (bypassing `assignUIDs`'s name-based minting entirely) *could* deliberately give a real
axis the same UID as some placeholder it constructs, at which point the "left as-is" arm's
silence would matter. `ScanGen.lean` is the one place in the repo that builds ASTs this way, and
it already assigns distinct, proper non-zero UIDs (e.g. `202`, `L`) to every axis it constructs —
the collision has never occurred in practice. **Still don't detect a placeholder by `uid == 0` in
new code** — that was never the actual invariant (see above), and a hand-built AST is free to pick
any UID for anything.

**Decided 2026-07-30: docs-only.** No code change for G — recorded here and in the #5b spec's
Part 5, which is closed as "probed unreachable" rather than implemented. The single-candidate
adoption rule and the fail-loud `unresolvedBaseIterAxis` rejection remain available as optional
future ergonomic/defense-in-depth work (not safety fixes) if anyone wants to revisit; see the
spec for the shape.

**H. An axis kind's size is write-only — `axis l : ℕ[3]` looks like an extent pin and is not
(new 2026-07-30, PROBED, FIXED 2026-07-30).** `AxisKind` was `real/nat : Option SizeExpr → AxisKind`
(`Ast.lean:7-10`) and `Elab.lean:37,39` populated that `SizeExpr` from the `ℝ[…]`/`ℕ[…]` kind
forms. **Nothing ever read it.** The only consumers of `AxisSpec.kind` were the two dtype checks
`iterAxisNotNat` / `normAxisNotReal` (`Structural.lean:700,702`), which test `isNat`/`isReal`
and discarded the payload. Extents came from a *different* channel: `explicitSizes` is folded from
`| .axis ax (some n) => …` alone (`Lowering.lean:176-178`).

Probe (three programs differing only in the axis declaration, all else identical):

| Declaration | Result |
|---|---|
| `axis l : ℕ = 3` | `OK` — extent pinned |
| `axis l : ℕ[3]` | `ERROR — evalScan: unsized iteration axis 'l'` |
| *(none)* | `ERROR — evalScan: unsized iteration axis 'l'` |

**`ℕ[3]` was indistinguishable from declaring nothing.** Directly load-bearing for **#5b**, whose
whole premise is "require a *pinned* axis": any "is this axis sized?" check must test
`Decl.axis _ (some n)`, because a `kind`-based test would accept the decoy.

**Fix applied (Part 2b of the #5b spec, docs/superpowers/specs/2026-07-30-scan-axis-declaration-spike.md):**
deleted the dead payload rather than adding a rejection for it — `AxisKind` is now `real | nat`
(no argument), the `ℝ[…]`/`ℕ[…]` grammar productions and their two elaborator arms are gone, and
the state `axis l : ℕ[3]` used to parse into is no longer representable at all. Mechanical rewrite
across 72 sites in 20 files (`.real none`/`.nat none` → `.real`/`.nat`, `.real (some (.lit n))` →
`.real`, etc.); `lake build` green at the same 8610-job baseline, no new sorries. `tl_size` was kept
(the syntax category, `elabTLSize`, and `SizeExprTest.lean`) per `papers/leanncd.md` §14.3, which
specifies `ℕ[n]` as an unfinished feature (wiring to the affine size solver), not cruft — only the
*reachable, silently-inert* bracket-in-an-axis-declaration form was removed.

**DECIDED 2026-07-30 — remove the payload from the type, not the spelling from the grammar.**
`AxisKind` becomes `| real | nat`. `AxisKind` is mentioned in only five places in `LeanNCD/`
(definition, the `AxisSpec.kind` field, the elaborator, and `isNat`/`isReal`, which discard the
payload with `_`) and is not serialized anywhere, so the payload is provably write-only. This
deletes the two `ℝ[…]`/`ℕ[…]` productions with it, and costs a mechanical rewrite of **70
construction sites across 20 files** (`.real none` → `.real`, `.real (some (.lit 2))` → `.real`).

Two weaker fixes were considered and rejected. *Wiring the size in* is not like-for-like: `tl_size`
yields a general `SizeExpr` (`var/add/sub/mul/div`) while `explicitSizes` is `HashMap UID Nat`, so
only `.lit` could be wired and symbolic extents need the affine solver — a feature, not a fix.
*Rejecting the form with a named `CompileError`* was the first recommendation here and was **wrong**:
it kept the state representable (so a programmatic AST could still carry it) and it contradicted the
argument used for `iter` in the same spec — make the bad state ungrammatical rather than validated.
A check can be bypassed by a new entry point, as Task-0 / #4 showed; a deleted payload cannot.

That the trap is live, not cosmetic: the property oracle writes the same size through both channels
— `⟨"l", 202, .nat (some (.lit L))⟩` (dead) alongside `.axis l (some L)` (live) — at all 15 sites
carrying a kind size.

**H is an UNFINISHED FEATURE, not accidental cruft (established 2026-07-30).** `papers/leanncd.md`
**specifies** the bracket forms — `:1421-1431`, "Layer 1", commented *"bracket holds a `tl_size` term
elaborating to `SizeExpr`, §14.3"*. So the parser and the AST field were built to spec and the
*consumer* was never written. That is also why 15 oracle sites populate the kind size: the authors
were following the specified design. Three positions follow, and the paper's own answer is the third:

| | Action | Cost |
|---|---|---|
| Delete | drop `tl_size` + `elabTLSize` + 4 tests | **spec deviation** — needs a `leanncd.md` update |
| **Keep** *(chosen)* | Part 2b only; parser survives orphaned but tested | zero — it is a leaf |
| Finish | wire `ℕ[n]` to the affine size solver | a feature; out of scope, but the specified endpoint |

Deleting is *mechanically* safe — the cost is exactly the four `run_cmd` blocks at
`SizeExprTest.lean:40-67`; the 20 `SizeExpr` guards at `:10-38` never touch `tl_size`. So this is a
judgement call, not a constraint. **Related dead code in the same bucket: `SizeExpr.eval` has zero
production callers** (`Base/SizeExpr.lean:21-27`, self-recursive only); `SizeExpr` is used in
production purely as inert labels (`AxisP.mk (some a.name) (SizeExpr.var a.name)`). Keep, record.

Note this is *not* the "keep it for the future solver" argument rejected above. That argument would
have kept a **reachable** trap — `axis l : ℕ[3]` writable in a real program, silently doing nothing.
Part 2b removes the reachability; afterwards no program can reach `tl_size`, so it cannot mislead.
The trap was the bracket form *in an axis declaration*, not the size parser behind it.

## ⚠️ Revision 2026-07-30 — these decisions now target `EvalPlan`, not `BrBaseP`

The terminal goal is a **PyTorch/JAX execution layer** lowered from a backend-neutral **`EvalPlan`**
(`copilot_code_analysis.md` Appendix A). Execution branches off `ScheduledProgram` → `EvalPlan`, **not**
off the routed `ThreadedComposed` — which ends in `BrMorph`, a `Quotient` of raw syntax with no
denotation into numbers (finding F above) and therefore cannot execute anything.

**Every payload in the table above is a required `EvalPlan` field**, so "reject routed" is a temporary
staging device, never the long-term answer — you cannot reject `log(X[i])` if the goal is to emit
`torch.log`:

| Audited payload | Required `EvalPlan` home (Appendix A) |
|---|---|
| #1 axiswise mask | nonlinearity step: function, resolved axis, **mask**, exceptional-row policy |
| #3 `UnaryOp` | pointwise function step |
| #4 `ScatterOpts` | scatter step: destination map, output shape, **fill, collision op**, OOB policy, injectivity |
| #5 `AggOp` + #6 dtype | `ContractionAlgebra` (`factorOp`/`factorId`/`reduceOp`/`reduceId`) + `TensorSig.dtype : ScalarDType` |
| incidental term structure | contraction step: factors, **per-term reduction axes**, factor op/id, term op/id |
| #8 scan bodies | scan step: state sigs, **base plan, step plan**, iteration order, causality cert |

**Consequences for the buckets below:** the *carry* bucket's destination changes — dtype belongs in
`ContractionAlgebra`/`TensorSig`, not `BrBaseP`, and the expensive `weaveToArrayType_congr` /
`Agreement.lean` conjunct-2 rework buys **nothing** for execution, so defer it. The *reject* bucket
remains useful only as an honest interim gate while each payload's `EvalPlan` representation is built.
#8 (scan bodies) stays an accepted boundary for the *routed* path but must be **carried** for the
backend (`base plan` + `step plan`). See the terminal-goal section of
[`restructure_suggestions.md`](restructure_suggestions.md).

## Recommended decision set (routed-path framing — superseded in part by the revision above)

The honest intermediate property is **"preserve all payload, or reject with a named error."**
Concretely, three buckets:

1. **Carry (payload already fits, or the slot exists):** #2 nonlinearity label — fix the scan
   short-circuit; #5 `AggOp` — same; #6 dtype — `ArrayRow.datatypeTag` already has a `bool`
   constructor and `Realize.lean:38-40` already asks for this. These need no `BrBaseP` shape
   change except dtype, which needs one tag.
2. **Reject routed, with a named `CompileError`** (the Task-0 pattern from Spike 3): #1 mask,
   #3 `UnaryOp`, #4 non-default `ScatterOpts`, #7 iverson, #9 `recurMorphism`, and the
   incidental term-structure row. ⚠️ **Unlike Spike 3's scatter case, several of these work
   today on the eval path** and are used by real portfolio programs (log/sqrt/sin, iverson
   RL6–RL8). So the reject must be scoped to the **routed** entry point (`TLProgram.compile`),
   leaving `TLProgram.eval` untouched — otherwise working functionality breaks.
3. **Accept as a documented boundary:** #8 scan bodies (already documented at
   `Compile.lean:31-33`).

Plus three standalone fixes independent of the above: finding **C** (the `agg` drop), finding
**D** (`brOpOfIdx?`), and finding **E**'s stale comment.

## Interaction with Spike 4

Spike 4 is eval-side; this audit is routed-side. Mostly orthogonal, with three couplings:

- **Do the audit's decisions before 4d, 4g, 4b.** 4d (`normMask?` + `Except`-returning
  `applyNonlin`) should know whether the mask becomes a *shared* resolved form (decision #1);
  4g (`ReduceOp` for the stringly-typed reduce) should define an enum that serves eval **and**
  the eventual codec (decision #4); 4b (⊗-unit) ties to the dtype/semiring row (#6).
- **4a, 4c, 4e, 4f are independent — do them now.** 4a and 4c each close a real bug, and this
  audit *validates and sharpens* 4c: finding **B** gives its exact mechanism (`evalScan` never
  receives `decls`).
- **4h last**, as the doc says.

**Suggested order:** 4a → 4c → 4e/4f → decide this audit → 4d/4g/4b → 4h.
