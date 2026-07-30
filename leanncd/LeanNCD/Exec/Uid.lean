namespace LeanNCD

/-- Human-readable, LaTeX-renderable display name for an axis/array. Display-only and out of scope
    (§13) — a thin `String` wrapper kept so `UData.name` typechecks. -/
abbrev DynamicName := String

/-- A unique identity for a symbolic axis. Carries no semantic content — only equality/inequality
    of two UIDs matters. -/
abbrev UID := Nat

/-- A UID paired with its optional display name. -/
structure UData where
  uid  : UID
  name : Option DynamicName := none
  deriving Repr, DecidableEq, Inhabited

/-- Errors that `FreshM` compilation can throw (the §7.4 / §12 validation failures). -/
inductive CompileError
  | shapeMismatch        : String → String → CompileError   -- expected shape, actual shape
  | missingBaseCase      : String → CompileError            -- tensor name missing iterAt stmt
  | causalityViolation   : String → CompileError            -- l+1 on RHS for iteration axis l
  | overlappingScatter   : String → CompileError            -- non-injective scatter w/o reduce sum
  | linearWeightAmbiguous : String → CompileError           -- linear weight in ≠1 product factors
  | undeclaredName       : String → CompileError            -- name used but not declared
  | rankMismatch         : String → Nat → Nat → CompileError -- tensor name, expected rank, actual rank
  | iterAxisNotNat       : String → CompileError            -- axis used in iterAt/iterNext but kind is ℝ
  | normAxisNotReal      : String → CompileError            -- axis used in freeNorm but kind is ℕ
  | predicateNonlin      : String → CompileError            -- predicate tensor with non-identity nonlin
  | predicateAgg         : String → CompileError            -- predicate tensor with non-sum aggregation
  | cyclicDataflow       : String → CompileError            -- cyclic dataflow (topoSort cycle fallback)
  | inconsistentScanAxes : String → CompileError            -- coupled scan outputs disagree on shared axis order
  | emptyScanOutputs     : String → CompileError            -- scan step with no true outputs (empty base∩recur)
  | scanProjectionUnsupported : String → CompileError       -- per-step stmt inside a scan references the
                                                             -- iteration axis on its own LHS with no base case;
                                                             -- move it after the scan and read the materialized state
  | unsupportedRecurMorphism : String → CompileError        -- Wave-A policy: the §12.2 `recurMorphism`
                                                             -- escape hatch has NO semantics anywhere —
                                                             -- `toBrBaseP` discards the supplied
                                                             -- `ThreadedComposed` and emits an empty
                                                             -- `.scanPre` step, and every evaluator entry
                                                             -- rejects it. Accepted-then-discarded was the
                                                             -- worst state, so `compile` now rejects it
                                                             -- outright (audit finding #4)
  | unsupportedNonlinScatter : String → CompileError        -- Spike-3 Stage-0 short-term policy: a scatter
                                                             -- (affine/diagonal LHS) write may only carry the
                                                             -- identity nonlinearity — `evalScatter` never applied
                                                             -- one (silent-erasure bug), and supporting one needs a
                                                             -- semantic decision (activation before
                                                             -- collision-reduction, or after fill/reduce?) that is
                                                             -- out of scope for now; see `checkScatterNonlin`
                                                             -- (Structural.lean) and `splitStmt`'s `.scatter` arm
                                                             -- (Lowering.lean)
  deriving Repr, DecidableEq

/-- Combined error + UID-counter monad (`EStateM ε σ α = σ → Result ε σ α`, Lean core). Mints fresh
    UIDs and validates structure; the executable side of the seam (it computes, proves nothing). -/
abbrev FreshM := EStateM CompileError Nat

/-- Mint a fresh UID (a counter, not random ints — reproducible and testable). -/
def freshUData : FreshM UData := do
  let n ← get
  set (n + 1)
  return ⟨n, none⟩

end LeanNCD
