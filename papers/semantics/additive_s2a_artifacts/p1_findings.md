# S2a P1 findings: core generalisation to a destination index map

Branch `proto-s2a-p1` (from `proto-s2a-p0` @ 7cd27e2c). Code commits a3e89af6, 42b495ae,
c6de3d98, 979e5ca3, a5fc0677; patches in `p1_patches/0001..0005`.

## Design: the candidate, adopted, with one deviation

The "virtual output shape + destination index map" design typechecked as proposed, with no
change to `Slots`, `Ref`, `projectWithin(_transport)`, `appendLeft` or the linking lemmas.

```lean
structure AdmittedOutput (source : Context) (σ : Declarations Unit) where
  tensor : σ.Tensor
  indices : List UID
  origin : SourceOrigin
  context : Context
  order : context.axes.map Axis.uid = firstUIDs indices
  shape : Shape                                        -- NEW: virtual write shape
  dest : Coord shape → Coord (σ.signature tensor).axes -- NEW: destination index map
  slots : Slots context.axes shape                     -- was: ... (σ.signature tensor).axes
  linked : slots.uids = indices
  sourceSlots : Slots source.axes shape                -- was: ... (σ.signature tensor).axes
  source_linked : sourceSlots.uids = indices
  embedding : IdentityEmbedding context source

def AdmittedOutput.IsBare (output : AdmittedOutput source σ) : Prop :=
  ∃ bare : Slots source.axes (σ.signature output.tensor).axes,
    bare.uids = output.indices ∧
      ∀ w, output.dest (output.sourceSlots.project w) = bare.project w

def AdmittedStatement.destination statement x := statement.output.dest (statement.output.slots.project x)
```

**Deviation: what `IsBare` states.** `IsBare` says "there is a bare slot list for the destination
signature, with the same uids, whose projection the destination is". It is not the structural
equation `shape = signature axes ∧ dest = id`. Reason: the only consumer, the raw chain's
per-coordinate claim (`CertifiedRawStatement.output_projection`), needs a `Slots` at the
*signature* shape so that `RawOutputSlots.coordinate` applies as before. The witness form gives it
one with no casts. The structural equation also exists, as a transport-safe statement:
`admitOutput_identity : ∃ hs : output.val.shape = (σ.signature output.val.tensor).axes, ∀ x, output.val.dest x = hs ▸ x`,
and `AdmittedOutput.isBare_of_identity` turns it into `IsBare` (proof: `cases`, then `subst hs`).

A side effect worth knowing: no field other than `dest` depends on `tensor` now, so
`{ o with tensor := t, dest := d }` retargets an output onto another tensor. The test uses this.

## Per-file changes (lines + / −, from base 7cd27e2c)

| File | +/− | Declarations |
|---|---|---|
| Source/Admission.lean | +48/−5 | `AdmittedOutput` (fields `shape`, `dest`; `slots`/`sourceSlots` at `shape`); new `AdmittedOutput.IsBare`, `AdmittedOutput.isBare_of_identity`, `admitOutput_identity`, `admitOutput_bare`; `admitOutput` builds the identity case `(σ.signature dst).axes, id`; `StatementFields` conjunct 7 is now `(BareOutputSlots … ∧ statement.output.IsBare)`; `admitStatement_fields` proves it |
| Source/Statement.lean | +19/−3 | `AdmittedStatement.destination` composes `dest`; `destination_pullback` RHS is `dest (sourceSlots.project …)`; new `AdmittedStatement.destination_bare` (R1: under `IsBare`, destination = the old bare projection) |
| Source/Fiber.lean | +2/−2 | `Term.globalDestination` composes `dest` (type unchanged); `globalFiber`, `globalFiber_reenumerate`, `uidFiber_reindex` unchanged in statement |
| Source/Correspondence.lean | +14/−13 | `Term.globalDestination_partition`, `Term.fiber_partition`, `Term.collectedBody`, `Term.collectedBody_correspondence`, `Term.empty_fiber` now use `output.dest (output.slots.project x) = p`; `pure_correspondence` unchanged in statement |
| Source/ProgramCorrespondence.lean | +1/−1 | proof of `AdmittedStatement.fiber_partition` only. Its statement was already in terms of `statement.destination`, as were the collection theorems |
| Source/RawCorrespondence.lean | +12/−4 | `RawStatementFields` conjunct 7 is now `(RawOutputSlots … ∧ statement.output.IsBare)`; `rawStatement_fields`, `RawStatementFields.output_slots` and `RawCorrespondence.output` were adjusted (`.1`); new `RawStatementFields.output_bare` |
| Source/RawSemanticConnection.lean | +11/−6 | `CertifiedRawStatement.output_projection` (see gating) |
| lakefile.toml | +1/−0 | `Semantics.SourceAffineDestinationTest` added after `Semantics.SourceCorrespondenceTest` |
| test/Semantics/SourceAffineDestinationTest.lean | +125 (new) | R2 test |
| test/Semantics/SourceRawCorrespondenceTest.lean | +2/−2 | forced edit (below) |

**Needed no edit:** Permutation.lean, Observation.lean, Program.lean, Lowering.lean, Oracle,
NumericalProfile, Diagnostics. Permutation's `destination_transport`/`destinations` and the
`Program.destination` field go through `statement.destination` without unfolding it.
Observation uses `output.indices`, which is unchanged.

## Generalised theorems (R3)

All keep their names, and none was weakened to a bare-only form. `Term.fiber_partition`:
`term.globalFiber output ρ p = ∑ x, if output.dest (output.slots.project x) = p then term.value ρ x else 0`.
`Term.globalDestination_partition`: `globalDestination output term v = output.dest (output.slots.project (term.partitionCoordEquiv v).1)`.
The `Term.collectedBody*` and `Term.empty_fiber` theorems take the same dest-composed form.
`AdmittedStatement.fiber_partition`, `AdmittedSource.globalFiber`/`collect_correspondence` and the
Permutation `destinations`/contribution theorems are stated over `statement.destination`, which
is now dest-composed, so they cover affine outputs with no change to their statements.

## Raw-chain gating

- The gate lives in the certificates. `StatementFields` (Admission) and `RawStatementFields`
  (RawCorrespondence) each pair their bare-slot conjunct with `statement.output.IsBare`. It is a
  left-nested pair in position 7, so every positional `obtain` that wrote `_` there was unchanged.
  The three sites that used the conjunct now take `.1`. `admitStatement_fields` discharges it
  through `admitOutput_bare`.
- `CertifiedRawStatement.output_projection` has the same signature and no new hypothesis. Two
  changes to its conclusion:
  1. The destination equation is now `statement.destination (pullback v) = statement.output.dest (statement.output.sourceSlots.project …)`. This holds for every output.
  2. The per-coordinate raw reading now reads `Coord.raw (statement.output.dest (statement.output.sourceSlots.project …)) q`. It is proved from the certified `IsBare` witness (`hb.2`) and `RawOutputSlots.coordinate` on the bare slots.
- `RawStatementFields.output_bare` exposes the gate. Affine statements get no raw-parse theorem.
- **Consequence for P2 (load-bearing):** once admission accepts affine statements,
  `admitStatement_fields` cannot prove `StatementFields` for them. Both `BareOutputSlots` (already
  there before this change) and `IsBare` fail for them. P2 must therefore either make
  `StatementFields` a sum (bare | affine), or have the raw chain quantify only over bare
  statements. As things stand, `RawCorrespondence` cannot be built for any source that contains
  an affine statement.

## Forced test edits

- `test/Semantics/SourceRawCorrespondenceTest.lean`, `DonorOutputConnection` (line ~802): the
  conclusion `Coord.raw (statement.output.sourceSlots.project …) q` no longer typechecks.
  `sourceSlots.project` now lands in `Coord output.shape`, while `q` indexes the signature axes.
  The edit wraps it as `Coord.raw (statement.output.dest (statement.output.sourceSlots.project …)) q`,
  matching the restated `output_projection`. The proof (`donor_output_connection`) did not change.

No other test file was edited.

## R2 test (`SourceAffineDestinationTest`)

- Source: axis x with extent 4, axis w with extent 8. `X[x]` is an input with values [1,2,3,4],
  `T[x] = X[x]`, and `S[w]` is an output.
- The bare `T` output is retargeted onto `S` with `dest` given by an integer index map. Two
  variants are checked with `#guard`; each checks the images, `Term.globalFiber`,
  `Term.collectedBody` and `AdmittedStatement.globalFiber` (the affine output placed in an
  `AdmittedStatement`).
  - `S[2*x]`: images [0,2,4,6]; fibers [1,0,2,0,3,0,4,0]. The empty fibers read 0.
  - `S[x/2]`: images [0,0,1,1]; fibers [3,7,0,0,0,0,0,0]. Colliding coordinates sum (⊕).
- Bare baseline `#guard`: `T`'s fiber is [1,2,3,4] and `shape = signature axes` (decided).
- Two `example`s: `Term.fiber_partition` applied to a retargeted output with no bare hypothesis,
  and "every admitted statement's output is `IsBare`", proved from `admitSource_fields`.
- Deviation: the carrier is ℚ (`RationalReference.registry`, `ratStore`), not ℝ, because `#guard`
  needs a computable carrier. The core proofs are semiring-generic.
- The test's `indexMap` is total only through a `getD` fallback to coordinate 0 for out-of-range
  images. The `images` guard checks that the fixtures never take the fallback. In admission
  proper, P2 must refuse such writes statically.

## Not done / caveats

- No admission arms, oracle, differential legs or NumericalProfile changes (out of scope).
- The lean-lsp MCP server could not start (`No such file or directory: 'lake'`), so all checks
  used `lean-file.sh` and `lake-build.sh`.
- No `sorry`, `native_decide` or new `axiom` was introduced. `Semantics.AxiomAudit` audits the
  whole namespace, so it covers the new declarations; its result is in the Tests run below.

## Builds

- `LeanNCD.Semantics.Source.ProgramCorrespondence`: green, 8515 jobs (after the core change).
- `LeanNCD.Semantics.Source.RawSemanticConnection`: green, 8517 jobs (after gating).
- `test/Semantics/SourceAffineDestinationTest.lean` via `lean-file.sh`: clean; all `#guard`s pass.
- `LeanNCD` + `Tests` (one run, at code tip a5fc0677): `Build completed successfully (8816 jobs)`.
  The baseline was 8814; the difference is the new test module and its lakefile entry. The run
  includes `Semantics.AxiomAudit` (green) and every `Semantics.Source*` test.

## Budget

About 63 turns, slightly over the ~60 budget. The overrun came from waiting on the background
Tests build: monitors were re-armed twice, once after a false trigger on an `Except.error` info
line. Context peak was about 95k, under 250k.
