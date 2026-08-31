import LeanNCD.Exec.Uid
import LeanNCD.DSL.Ast

namespace LeanNCD.Eval

-- Owns every diagnostic the evaluator can produce: `ShapeError` (axis-sizing failures, whether
-- raised by `Contract`/`Scatter`/`Scan` directly or surfaced from the `SizeSolve` affine solver),
-- `EvalWarning` (non-fatal `inferAxisSizes` warnings), and the top-level `EvalError` that every
-- worker's `Except EvalError _` returns. This is a LEAF module in the Eval/ dependency graph:
-- it imports only `Exec.Uid` (for `UID`/`CompileError`) and `DSL.Ast` (for `UnaryOp`/`LHSSlot`),
-- never anything under `Eval/` itself — `Tensor.lean`, `Gather.lean`, `Contract.lean`, etc. all
-- import Error, never the reverse, so there is exactly one place a new diagnostic case can be
-- added without risking an import cycle.
--
-- Design (Wave E, 4h): errors are layered causes, not one flat stringly family —
-- `EvalError.shape` nests a `ShapeError`, `ShapeError.solveFailure` nests a `SolveDiagnostic`
-- (moved here verbatim from `SizeSolve.lean`, which now only CONSTRUCTS diagnostics and never
-- renders them), and `EvalError.compile` nests an already-typed `CompileError` rather than
-- flattening it to a string. Every constructor here is closed and specific to a real throw site
-- inventoried across `Gather`/`Contract`/`Nonlin`/`Scatter`/`Scan`/`SizeSolve`/`SizeInfer`/`Eval`
-- before this file was written — there is no generic `unsupported String` escape hatch, and no
-- speculative backend/phase taxonomy beyond what those real sites need.
--
-- `ToString` instances below are the ONLY renderers for each type (one per family, matching the
-- rule that errors propagate as typed values and are rendered solely at presentation/test
-- boundaries) and are written to reproduce the pre-4h flat message text BYTE-FOR-BYTE — every
-- string literal in this file was copied from the throw site it replaces, not freshly composed,
-- so a diff against the old string constants is the correctness check for this file.

/-- The four ways the affine size system (`SizeSolve.solveSizeConstraints`) can fail to yield a
    valid concrete size assignment. Public (unlike its pre-4h home in `SizeSolve.lean`, where it
    was `private` because `EvalError` was still `String`): `ShapeError.solveFailure` now nests a
    `SolveDiagnostic` built from this, and typed tests (`AffineShapeSolverTest`) match on `.kind`
    directly instead of grepping the rendered message. -/
inductive SolveFailureKind
  | inconsistent
  | underdetermined
  | nonIntegral
  | nonPositive
  deriving Repr, DecidableEq

/-- Everything `renderSolveDiagnostic` needs to produce one rich failure message: which kind of
    failure, which UIDs are implicated, a kind-specific detail string, the contributing source
    labels, and remediation/ml-hint text. Moved here verbatim from `SizeSolve.lean` (same fields,
    same defaults) — `solveSizeConstraints` still constructs these, but only `Error.lean` renders
    or offers remediation for them now. -/
structure SolveDiagnostic where
  kind : SolveFailureKind
  unconstrained : List UID := []
  offendingUid? : Option UID := none
  detail? : Option String := none
  sourceRefs : List String := []
  remediation : List String := []
  mlHints : List String := []
  deriving DecidableEq

/-- Kind-specific remediation guidance, computed lazily by `renderSolveDiagnostic` unless a
    diagnostic already carries an explicit `remediation` list. Public (moved verbatim from
    `SizeSolve.lean`): typed tests can call this directly on a caught `SolveDiagnostic` to assert
    the exact guidance text without re-deriving it from the rendered string. -/
def remediationOfDiagnostic (d : SolveDiagnostic) : List String :=
  match d.kind with
  | .inconsistent =>
      [ "verify cited tensor dimensions and affine offsets are mutually consistent"
      , "if mismatch is intentional, split equations across distinct output axes" ]
  | .underdetermined =>
      [ "bind unconstrained axes with explicit axis declarations"
      , "add independent affine reads so rank matches variable count" ]
  | .nonIntegral =>
      [ "adjust stride/dilation-like coefficients to satisfy divisibility"
      , "shift constants or input extents so inferred size is integral" ]
  | .nonPositive =>
      [ "increase effective input extent or reduce negative shifts"
      , "ensure inferred output window size stays strictly positive" ]

/-- Render a `SolveDiagnostic` to the composite failure message: a kind-specific base clause,
    then optional detail/sources/remediation/ml-hint suffixes, each appended only if present, in
    this fixed order. Moved here verbatim from `SizeSolve.lean`'s `renderSolveDiagnostic` (same
    logic, same text) — this is the sole renderer `ShapeError.solveFailure` delegates to. -/
def renderSolveDiagnostic (d : SolveDiagnostic) : String :=
  let base := match d.kind with
    | .inconsistent => "affine size system inconsistent"
    | .underdetermined => s!"affine size system underdetermined (unconstrained uids: {d.unconstrained})"
    | .nonIntegral =>
        match d.offendingUid? with
        | some u => s!"affine size system non-integral (uid {u})"
        | none   => "affine size system non-integral"
    | .nonPositive =>
        match d.offendingUid? with
        | some u => s!"affine size system non-positive (uid {u})"
        | none   => "affine size system non-positive"
  let withDetail := match d.detail? with
    | some txt => s!"{base} ({txt})"
    | none => base
  let withSources := if d.sourceRefs.isEmpty then
      withDetail
    else
      s!"{withDetail}; sources: {d.sourceRefs}"
  let remediation := if d.remediation.isEmpty then remediationOfDiagnostic d else d.remediation
  let withRemediation := if remediation.isEmpty then
      withSources
    else
      s!"{withSources}; actions: {remediation}"
  if d.mlHints.isEmpty then
    withRemediation
  else
    s!"{withRemediation}; ml-hints: {d.mlHints}"

/-- Which call site raised an `unsizedAxis` failure. Each site's original message wording differs
    (different verb, different parenthetical) even though the underlying condition — an axis-UID
    with no entry in the solved `sizes` map — is the same; this closed enum is exactly as wide as
    the real call sites found by the 4h throw-site inventory (`Contract.evalAssignSeeded` ×3,
    `Scatter.evalScatter` ×1, `Scan.evalScan` ×1), no wider. Adding a new site here is the only
    change needed to preserve its exact wording; `ShapeError.unsizedAxis` itself never changes. -/
inductive UnsizedAxisSite
  | assignOutput     (nm : String)
  | assignSeeded     (nm : String)
  | assignContracted (nm : String)
  | scatterSource
  | scanIteration    (axisName : String)
  deriving DecidableEq

/-- Axis/shape-sizing failures: everything that can go wrong turning read positions and scatter
    outputs into concrete axis sizes. Raised from several modules (`Contract`, `Scatter`, `Scan`,
    `SizeInfer`, `SizeSolve`) — not just `SizeInfer.lean` — since the underlying concern (an axis
    or shape computation lacking a size) is the same regardless of which worker discovers it
    first; nesting under `EvalError.shape` groups them for callers that want to react to "any
    shape problem" without enumerating every producer. -/
inductive ShapeError
  | unsizedAxis (uid : UID) (site : UnsizedAxisSite)
  | unsizedScatterOutput (slot : LHSSlot)
  | sizeConflict (uid : UID) (existing : Nat) (new : Nat)
  | solveFailure (diagnostic : SolveDiagnostic)
  | negativeOnlyAxis (uid : UID) (sources : List String)
  deriving DecidableEq

/-- The sole renderer for `ShapeError` — reproduces every pre-4h message byte-for-byte. -/
def ShapeError.render : ShapeError → String
  | .unsizedAxis uid site =>
      match site with
      | .assignOutput nm =>
          s!"evalAssign {nm}: output axis (uid {uid}) has no inferable size (it appears in no read position)"
      | .assignSeeded nm     => s!"evalAssign {nm}: seeded axis (uid {uid}) has no declared size"
      | .assignContracted nm => s!"evalAssign {nm}: contracted axis (uid {uid}) has no inferable size"
      | .scatterSource        => s!"evalScatter: unsized source axis uid {uid}"
      | .scanIteration nm =>
          s!"evalScan: unsized iteration axis '{nm}' (uid {uid}) — pin it with \
`axis {nm} : ℕ = N`, or ensure some read fixes its extent"
  | .unsizedScatterOutput slot =>
      s!"scatterOutShape: unsized axis in scatter output coordinate for slot {repr slot}"
  | .sizeConflict uid existing new => s!"axis size conflict for uid {uid}: {existing} vs {new}"
  | .solveFailure diagnostic => renderSolveDiagnostic diagnostic
  | .negativeOnlyAxis uid sources =>
      s!"axis uid {uid} is purely negatively constrained (appears only with non-positive \
coefficients in all reads; sources: {sources}); add an explicit axis declaration"

instance : ToString ShapeError := ⟨ShapeError.render⟩

/-- The one non-fatal diagnostic `inferAxisSizes` can emit (Issue H: a fully-known multi-term
    read whose max index reaches or exceeds its tensor's dimension — valid under padded semantics,
    but often surprising). `EvalWarning` is a single-variant enum rather than a bare `String`
    precisely so a future second warning kind is a new constructor, not a new ad-hoc prefix
    convention on an unstructured string. -/
inductive EvalWarning
  | paddedAccess (source : String) (maxIndex : Int) (dimension : Nat)
  deriving DecidableEq

/-- The sole renderer for `EvalWarning` — reproduces the pre-4h warning text byte-for-byte. -/
def EvalWarning.render : EvalWarning → String
  | .paddedAccess source maxIndex dimension =>
      s!"padded-access warning: {source} max-index {maxIndex} ≥ dim {dimension}; \
out-of-range reads will be zero-padded"

instance : ToString EvalWarning := ⟨EvalWarning.render⟩

/-- Deterministic context captured at the `gather` call site for a `.unaryFn` factor: which
    tensor was read and the resolved integer coordinate the read failed at. The original
    `applyUnaryFn` domain-check messages (`log`/`sqrt`/`recip`) carry NO such context — this
    structure exists so a typed test (or a future richer renderer) CAN inspect it, without
    changing what the initial `ToString` text says; `gather`'s `.unaryFn` branch recomputes
    `coord` via `evalIdx` (cheap, already-available data) rather than threading it through
    `gatherRead`'s return type. -/
structure EvalContext where
  tensor : String
  coord  : List Int
  deriving DecidableEq

/-- Which worker discovered a missing tensor name. These are the three real lookup boundaries:
    scalar gathering, assignment's up-front read validation, and scatter's corresponding
    validation. Keeping the site closed preserves each legacy message prefix without allowing an
    arbitrary string to become a second error-dispatch channel. -/
inductive UnknownTensorSite
  | gather
  | assign
  | scatter
  deriving DecidableEq

/-- Partial unary operations whose mathematical domains can reject a gathered value. Keeping this
    narrower than `UnaryOp` prevents diagnostics for impossible cases such as an `exp` domain
    failure; the worker converts to this type only in the three branches that can actually fail. -/
inductive UnaryDomainOp
  | log
  | sqrt
  | recip
  deriving DecidableEq, BEq, Repr

/-- The single, context-free home for every unary transcendental's math and domain partiality
    (`log`/`sqrt`/`recip` fail loud; `exp`/`sin`/`cos` are total). Both evaluators call this and wrap
    the returned `UnaryDomainOp` into their own error channel — the reference `applyUnaryFn` below
    re-attaches its `EvalContext` (`EvalError.unaryDomain`), the checked-plan `gatherFactor`
    (`Eval/Plan/Dense.lean`) attaches a positional slot (`PositionalInputError.unaryDomain`). Adding a
    future unary operator is one `UnaryOp` constructor and one arm here; both evaluators inherit it
    and parity holds by construction. -/
def _root_.LeanNCD.UnaryOp.applyChecked : LeanNCD.UnaryOp → Float → Except UnaryDomainOp Float
  | .log,   v => if v ≤ 0.0 then .error .log else .ok (Float.log v)
  | .sqrt,  v => if v < 0.0 then .error .sqrt else .ok (Float.sqrt v)
  | .exp,   v => .ok (Float.exp v)
  | .sin,   v => .ok (Float.sin v)
  | .cos,   v => .ok (Float.cos v)
  | .recip, v => if v == 0.0 then .error .recip else .ok (1.0 / v)

/-- Why `resolveNonlin` rejected an `.axiswise` nonlinearity. Both cases are direct, unconditional
    throws in `resolveNonlin` (no solver, no context) — a closed two-case enum, not a bare string,
    since there are exactly two ways this can fail and neither will ever need extra payload. -/
inductive NormAxisReason
  | notAmongOutputAxes
  | notMarked
  deriving DecidableEq

/-- Which evaluator entry point rejected the `recurMorphism`/`scanPre` escape hatch. All three
    sites (`Eval.evalPlain`'s `.recurMorphism` case, `Scan.evalScan`'s `.scanPre` case, and
    `Eval.evalScheduled`'s `.scanPre` case) reject the SAME unsupported feature — Wave-A policy,
    `CompileError.unsupportedRecurMorphism`'s runtime counterpart — with only their site prefix
    differing; one constructor with a closed `site` tag keeps that single feature's three
    messages together instead of inventing three unrelated top-level `EvalError` cases. -/
inductive RecurMorphismSite
  | evalPlain
  | evalScanNode
  | evalScheduled
  deriving DecidableEq

/-- Why `evalScan`/`evalStmtSliceSeeded` rejected a scan node's shape. All four cases are direct
    structural throws (wrong `Stmt`/`ScanStmt` variant reaching a function that only handles one
    shape) — a closed enum of the exact sites the 4h inventory found, not a speculative "invalid
    state" catch-all. -/
inductive InvalidScanReason
  | onlyAssignInSlice
  | plainNotHandledHere
  | noIterationAxis
  | baseMustBeAssign
  deriving DecidableEq

/-- Every error any Eval/ worker can raise. Layered: `.compile`/`.shape` nest an already-typed
    cause (never flattened to a string) rather than duplicating that type's cases here; the
    remaining constructors are closed and specific to the real throw sites the 4h inventory found
    in `Gather`/`Contract`/`Nonlin`/`Scatter`/`Scan`/`Eval` — no generic `unsupported String`, no
    broad phase/role taxonomy speculatively added ahead of a second real producer. -/
inductive EvalError
  | compile (cause : CompileError)
  | shape (cause : ShapeError)
  | unknownTensor (site : UnknownTensorSite) (name : String)
  | invalidSeed (nm : String) (uid : UID) (value : Int) (bound : Nat)
  | unaryDomain (op : UnaryDomainOp) (value : Float) (context : EvalContext)
  | invalidNormAxis (reason : NormAxisReason)
  | scatterCollision (nm : String) (outCoord : List Nat) (firstSource : List Nat) (secondSource : List Nat)
  | unsupportedScatterNonlin (nm : String)
  | unsupportedRecurMorphism (site : RecurMorphismSite) (nm : String)
  | invalidScanNode (reason : InvalidScanReason)

/-- The sole renderer for `EvalError` — reproduces every pre-4h message byte-for-byte.
    `.unaryDomain`'s `context` is deliberately NOT rendered (its `EvalContext` carries strictly
    MORE information than the original flat message ever did); surfacing it is a future,
    test/tooling-only concern, not a change to today's user-facing text. -/
def EvalError.render : EvalError → String
  | .compile cause => s!"compile failed: {repr cause}"
  | .shape cause => cause.render
  | .unknownTensor site name =>
      let siteName := match site with
        | .gather => "gather"
        | .assign => "evalAssign"
        | .scatter => "evalScatter"
      s!"{siteName}: unknown tensor {name}"
  | .invalidSeed nm uid value bound =>
      s!"evalAssign {nm}: seed coordinate {value} for axis (uid {uid}) is out of range [0, {bound})"
  | .unaryDomain op value _context =>
      match op with
      | .log   => s!"log domain error: log({value}) undefined for non-positive input"
      | .sqrt  => s!"sqrt domain error: sqrt({value}) undefined for negative input"
      | .recip => s!"div domain error: 1/{value} undefined for zero input"
  | .invalidNormAxis reason =>
      match reason with
      | .notAmongOutputAxes => "resolveNonlin: marked norm axis is not among its output axes"
      | .notMarked => "resolveNonlin: applies softmax/normalize but no output axis is marked (·)"
  | .scatterCollision nm outCoord firstSource secondSource =>
      s!"evalScatter {nm}: collision writing output coord {outCoord} — source coords \
{firstSource} and {secondSource} both write here"
  | .unsupportedScatterNonlin nm =>
      s!"evalScatter: non-identity nonlinearity on scatter {nm} is unsupported (Spike-3 Stage-0 policy)"
  | .unsupportedRecurMorphism site nm =>
      match site with
      | .evalPlain => s!"evalPlain: recurMorphism (escape hatch) unsupported ({nm})"
      | .evalScanNode => s!"evalScan: scanPre (recurMorphism escape hatch) evaluation unsupported ({nm})"
      | .evalScheduled => s!"evalScheduled: scanPre unsupported ({nm})"
  | .invalidScanNode reason =>
      match reason with
      | .onlyAssignInSlice => "evalStmtSliceSeeded: only assign stmts are supported in scans"
      | .plainNotHandledHere => "evalScan: plain handled by evalScheduled, not here"
      | .noIterationAxis => "evalScan: scan node has no iteration axis"
      | .baseMustBeAssign => "evalScan: base stmts must be assigns"

instance : ToString EvalError := ⟨EvalError.render⟩

/-- A fatal evaluation outcome together with every non-fatal warning discovered before it.
    Defined beside the diagnostic types rather than the scheduled worker because shape inference
    itself can now fail after emitting earlier warnings. The underlying `EvalError` remains nested
    for typed matching and byte-compatible rendering. -/
structure EvalFailure where
  error : EvalError
  warnings : List EvalWarning

/-- Render a failed evaluation exactly like its fatal error. Warning presentation remains an
    explicit caller decision instead of being duplicated into the legacy-compatible error text. -/
def EvalFailure.render (failure : EvalFailure) : String :=
  toString failure.error

instance : ToString EvalFailure := ⟨EvalFailure.render⟩

end LeanNCD.Eval
