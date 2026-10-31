# Additive scatter geometry A — oracle independence review

## Scope and method

Reviewing BASE `d48691daa8d08d45bf8645b21b3b6bc85def18f3` to FINAL
`ba1c783d7d1c971c05e5651f73a14b3284a09538`, using committed FINAL sources.
This separate-context lens covers plan sections 3, 6 and 7: oracle shape
independence, four-leg tropical fixture inputs/wiring, native binary32
discriminators, and the ownership of silently ignored sibling cases.

Controller patch/hash/build checks and concurrent mutation execution are not
repeated. No production, test, manifest or patch changes are made. Findings
are appended incrementally below; the final disposition follows after review.

## Evidence: shape independence and contract classification

**Accept the stated tradeoff; no fix-now finding.** `Differential.derivedShape`
now delegates nonconstant forms to `LHSSlot.outExtent`, with UID-based source
extent lookup. This is a contract-difference predictor, not the value/shape
oracle: `Oracle.runWith` still obtains destination shape from declaration axes
and enumerates destination coordinates independently. Constants retain the
explicit `c + 1` predictor. A shared extent bug can therefore corrupt the
predictor and production together; this is not an independent oracle of the
extent formula. It is the deliberate section-3 single-home choice, supported
by independently declared fixture extents and pinned cell vectors.

`declaredShapeWins` coalesces coefficients per UID before counting nonzero
axes, matching `scatterAffineClass` and `LHSSlot.boundedScatter` for admitted
raw affine forms. It excludes constants and source/destination UID overlap.
`boxedSingleGroups` makes the corresponding checks after lowering; its
`isConstUnit` exclusion preserves the raw-constant exclusion. The predictor
assumes declaration extents are pinned, as documented; that assumption is
not proof of equivalence for arbitrary partially pinned compiler inputs.

`fF` declares `[6]` for `a+b` over `[4,3]`, while `fFbig` independently
declares `[7]` for the identical raw write. The former pins zero conditions
and parity; the latter pins one condition and `known:extent`.
`ComparisonRun.classification` reaches that class only after Core/oracle
agreement and `confirms` requires **both** observed native legs to have
shape/length binding issues on the condition's own declaration with the
predicted actual shape. Thus `fFbig` still detects the declared/derived
divergence; it does not certify that 6 is mathematically correct independently
of `outExtent`. An unrelated runtime failure cannot confirm this condition.
The constant twins `fI1`, `fI2`, and `fMask` exercise the analogous residual
without turning it into parity.

**Park, already owned by slice B:** the hand-maintained collector predicate
copy and synchronized removal of `isConstUnit` when boxed constants become
supported (about 0.5 dispatch). Reject a demand to restore a second extent
formula: it contradicts the agreed single-home anti-goal.

## Evidence: non-tautological tropical and binary32 fixtures

**PASS for the inspected fixtures.** `snapG` binds declaration 3 to
`X[a]=[1,2,3,4]`, declaration 4 to `W[b]=[1,10,100]`, and declaration 6
to `Y` on a fresh destination UID with an explicitly supplied extent.
`xw` places both reads in one product term; it is not a sum of separate
terms. `conv` uses coefficients `(1,a),(1,b)`, and `conv23` uses
`(2,a),(3,b)`, over extents 4 and 3.

`conv .max` cell 1 is `max(1+10,2+1)=11`; max-times would produce 10.
Its Core vector is explicitly pinned, alongside `fourLegParity`, rather
than generated from native output. `conv .min` supplies the complementary
min-plus row. For `conv23`, actual coordinates omit exactly 1 and 11;
coordinate 6 has contributions `4+1=5` and `1+100=101`. The max/min
vectors select 101/5 there and pin the empty cells to `-inf`/`+inf`.

`constSc` and `constAs` both retain raw `.affine (.const 3)` and read only
`X[a]`; their separate max/min rows pin holes 0–2 and coordinate 3 to
4/1. `outputForms` admits the raw form as `(3,[])`, and
`Oracle.destination` evaluates it directly. Core uses the admitted
`output.dest` through `AdmittedStatement.destination`. Neither uses
`lowerConstSlots`, whereas native source compilation invokes
`compileToScheduled` and `lowerArith`, which mint the unit axis. This is
independent evidence for constant lowering, despite shared raw admission
and the deliberately shared tropical semiring instances.

The exact four-leg entry is `compareSortedSource`: `runSourceAt` executes
the semantic Core at `Registry.none`, `Oracle.runWith` independently
enumerates fibres, and published agreement is required before native
agreement. Carrier selection uses the original max/min annotation.
`runNative snapshot (sorted := true)` recompiles the original snapshot;
`legOf` rejects binding issues and `compareBindings` checks native bits
against oracle-derived `SortedCell` values, including distinct infinity
bit patterns. Oracle empty fibres start from semiring zero; the chosen
max-plus/min-plus carriers make that `-inf`/`+inf`, not numeric zero.

**Native binary32 tests are real discriminators, not an f32 tropical
harness claim.** `B5NativeTest.run32` retains f32 declarations and calls
`runPreparedDense32`; `run64` explicitly substitutes f64 declarations.
`twin` performs an ordinary `T[a,b] := A[a]*B[b]` with the same f32
fraction inputs as `conv`, followed by test-side `antiDiagBits`: row-major
`ai*3+bi`, destination `ai+bi`, a-major accumulation, `Float32` addition
and zero seeds. This avoids `ScatterPlan` geometry and reduction. Native
bits are pinned to a nonempty six-word vector, the twin must equal it,
and separately pinned narrowed f64 bits differ at lanes 0, 1 and 3.

For `S3`, `bigIn32` contains `[2^24,1,1,1]`. `twinS` is a free-axis
identity assignment; its test-side Float32 fold gives 1266679808.
Native scatter pins that word at coordinate 3 with three zero holes;
the f64-then-narrow path pins 1266679810 instead. These twins share the
ordinary arithmetic backend, so they are not fully independent scalar
implementations, but their hard bit pins and non-scatter aggregation
exercise the intended geometry/precision distinction.

An independent arithmetic calculation (Python standard-library Float32
packing after each operation; no repository code execution) reproduced both
tropical multi-axis vectors, all six native/narrowed convolution bit words,
and the constant discriminator words. No Lean build or mutation was run.
`NativeLegs.observeBindings` requires every requested output and checks its
declared rank, shape and cell count before exposing bindings to the sorted
comparison; the fixture's `fourLegParity` cannot arise by omitting `Y`.

## Section-6 silently ignored cells and owners

| Cell / limitation | Identifier evidence and disposition |
| --- | --- |
| Boxed single multi-axis writer ignores pinned declaration without a production diagnostic | `boxedSingleGroups` excludes forms with multiple nonzero UID coefficients. `convBoxed` pins derived shape `[6]` and no boxed group; `fFbig` pins the independently declared `[7]` discrepancy as `known:extent`. Real residual; **park with slice B**, about 1 dispatch inside its boxed-geometry work. The oracle diagnostic does not mean production emitted one. |
| Boxed single constant writer ignores pinned declaration without a production diagnostic | Raw constants are excluded by `declaredShapeWins`; lowered constants are excluded by `isConstUnit`/`boundedScatter`. `pinAll 8 S3` and its assign twin pin derived `[4]` on three native/reference legs and no boxed group. `fI1`, `fI2`, `fMask` pin the oracle-facing extent discrepancy. Real residual; **park with slice B**, same boxed-geometry work. |
| Scan-local multi-axis reference/legacy placement replaces instead of summing | `evalStmtSliceSeeded` computes a dense LHS-source slice; `writeScanStmtSlice` evaluates original affine destinations and uses `set!`, not semiring addition. Multiple source pairs can reach one destination. `checkScanScatterLHSSlot` rejects multi-axis rows, and `s6MultiAxis` pins that refusal. Real backend asymmetry; **park with F3**, about 1 dispatch. |
| Hand-built scan-local raw-constant scatter remains outside checked support | `lowerConstSlots` returns scan-bearing slots unchanged; `StructuralTest` pins that raw `.scatter` bypass separately from the `.assign` `overlappingScatter` refusal. Checked scan preflight rejects `.constant`; reference placement remains the same replacement mechanism. Real accepted boundary asymmetry; **park with F3**, about 1 dispatch. This is not evidence that every constant scan has colliding occurrences: RHS contraction can already collapse them before placement. No new constant-scan collision counterexample was executed in this review. |
| Zero-coefficient writer under a boxed single declaration lacks a separate pin | `scatterAffineClass` treats zero/cancelled coefficients as bounded and `boxedSingleGroups` therefore collects a single zero writer when D5 does not exclude it. `zeroScale` is a **two-writer** group, so it does not establish this single-box cell. Real fixture gap, not silently unsupported geometry; **park**, about 0.3 dispatch. |
| Pure repeated-free-slot diagonal scatter inside a scan lacks a dedicated pin | `slotsBecomeScatter` detects repeated free UIDs without any affine slot. `s6Diagonal` is a nearby refusal pin, but its slots are **affine `2*j` plus free `j`**, not the table's pure `Y[i,i]` case. It pins a shared-UID scan restriction, not the no-affine classification path. Retain the narrowly stated exact-case fixture gap; **park**, about 0.3 dispatch. Do not claim there is no related diagonal scan coverage. |

The remaining owner rows are tracking limitations rather than additional
silently ignored geometry cells: the predicate-copy/marker synchronization
belongs to slice B (about 0.5 dispatch); independent mutation liveness of
new-module pins is parked (about 0.3 dispatch). The imported B5/B6
shadowing caveat is explicitly accepted by the plan, not a new finding or a
reason to tighten the oracle here. The pre-existing `LHSSlot.collapses`
comment is the plan's parked 0.1-dispatch documentation item; its cleanup
is outside this lens.

### ORACLE-AUDIT-01 — non-blocking audit-label correction

**Fix now: qualify the scan-local zero-coefficient row in the audit table,
not runtime code.** Section 6 calls it “admitted: R (`s6ZeroBase`)”.
`checkScanScatterLHSSlot` does indeed admit the slot syntactically, but
`s6ZeroBase`/`s6ZeroStep` explicitly pin whole-scan rejection:
`scanWriteRowNotAdmitted` with empty normalized row `#[]` and bias 0.
Thus “syntactically admitted; later zero write-row refusal pinned” is the
accurate description. This is a high-confidence documentation ambiguity
with executable identifier evidence, not newly broken geometry or a
request to broaden scan support. The boxed-zero **S** ownership remains
correct and independent of this wording.

## Scope not covered

- Controller exact-patch/blob verification, task builds, whole-project builds
  and the concurrent 31-entry mutation run: intentionally not repeated.
- Acceptance/correctness lens, exhaustive source-program equivalence,
  arbitrary partially pinned declarations, and a proof that the shared
  extent helper is correct for every affine form.
- Surface multi-axis/constant syntax, slice-B grouped/boxed admission,
  scan-local semantic repairs, route/JAX support and predicate/bool outputs.
- Four-leg f32 tropical comparisons (explicitly excluded), general IEEE
  arithmetic conformance, and complete independence of shared scalar
  arithmetic/carrier/admission code. Native f32 bit discriminators **were**
  inspected and independently recalculated.
- Independent mutation liveness of new-module B5/group/box/B6 pins and
  newly added pins for the parked exact-case gaps: explicitly not demanded.
- An executed raw-constant scan collision counterexample; the code-level
  accepted/refused boundary and replacement mechanism were inspected.

## Final disposition

**PASS — oracle-independence lens, with one non-blocking documentation
qualification (`ORACLE-AUDIT-01`, fix now).** No high-confidence new
production or fixture-wiring defect was found. The shared `outExtent`
predictor is an intentional, bounded loss of formula independence, not
reuse by the independent declared-shape/value oracle. `fFbig` remains a
live declared/derived contract-discrepancy pin; the tropical and native
binary32 fixtures contain concrete non-tautological discriminators.

**Park** the explicitly owned slice-B/F3/fixture-gap limitations with the
costs recorded above. **Reject** restoring a copied extent formula,
requiring an excluded f32 tropical harness, or demanding out-of-scope
mutation isolation for shadowed new-module pins.

This was one separate-context review, with no nested delegation, builds,
mutation execution or commits. Only this report was created/appended.
No review-budget breach was observed.
