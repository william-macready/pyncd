# F3-b stage 1 review: mishandled / wrongly accepted programs (lens 2)

Base edaf7781, commits 84cbf47c, 13a481cd. All programs below were run through the reference, the checked
f64 plan and the checked f32 plan with `leanncd/scripts/lean-file.sh` on scratch files (deleted afterwards),
helpers copied from ScatterSurfaceTest (`scanIn64`, `compErr`, `refErr`, `planErr64`, `planErr32`).

### R1 [P2] A pinned declaration over a scan state's axis is silently overridden by a constant slot's extent
Where: the scan state shape derivation (reference `evalScan` state extents / checked `scanStateShape`);
`boxedSingleGroups`/`writerGroups` (DSL/Pipeline/Collect.lean) skip scan nodes (`plainAt?` is `none`), so the
declared box (B5c) never applies to a scan statement.
Scenario (OBSERVED, identical in ref, f64, f32):
```
axis j : ℕ = 3
iter l = 3
tensor f32 G(j, l), X(j), W(j, k)
G[=5, 0] := X[j]
G[=5, l +1] := G[j, l] · W[j, k]
```
publishes G with shape [6,3] although `j` is declared 3. With `=1` instead of `=5`: shape [2,3] (j declared 3),
cells [0,0,0, 6,42,294]. The TOP-LEVEL analogue is honoured or refused loudly: `S(j=3)` with `S[=1] := X[j]`
gives shape [3], cells [0,6,0]; `S[=5] := X[j]` is the typed refusal `ShapeError.writerExtentExceedsBox "S" 1 0 3 6`
(reference text "extent 6 exceeds declared box extent 3"). So a constant in a scan escapes a check its top-level twin has.
Sibling (OBSERVED): a strided non-constant scan slot has the same pre-existing behaviour: `G[2*j, 0]`,
`G[2*j, l +1]` with declared `j = 3` publishes [6,3]. So this is a scan-wide gap that stage 1 extends to constants,
not a regression of existing programs. Before stage 1 the constant program was refused at compile, so it is new
acceptance of a program whose published shape contradicts its declaration.
Why tests miss it: every scanConst* fixture leaves `j` undeclared or sized only by an input.
Fix: small. Either refuse at preflight/reference when a scan state's derived dimension differs from a pinned declared
axis extent (typed `inconsistentStateExtent`-style), or park it explicitly as a documented scan-wide limit in the
F3-b record and the Eval/AGENTS.md sentence ("unreached rows stay 0_K" is true, but the declared extent is not enforced).

### R2 [P3] Two base statements with different constants cannot coexist (typed refusal, no residue separation)
Where: `writesCollide` (Eval/Plan/Scan.lean 162) and reference `baseDimsSeparate` (Eval/Scan.lean 167): for two
`.strided` rows of scale 1 the test `offsetA % 1 != offsetB % 1` is never true, so scale-1 rows never separate.
Scenario (OBSERVED):
```
G[=1, 0] := X[j]
G[=2, 0] := Y[j]
G[=2, l +1] := G[j, l] · W[j, k]
```
refused on all three legs with `inconsistentStateExtent "G" "G" 0 2 3` (ref text "dimension 0 is 2 wide in its first
placement but 3 wide in a later one"). Different constants in one dimension have different extents (n+1), so the
extent rule fires and the program could never be accepted anyway; the residue rule's blindness is therefore not
reachable as a wrong rejection or a wrong acceptance. Two identical constants:
`G[=2, 0] := X[j]; G[=2, 0] := Y[j]` is the typed `baseWritesOverlap "G" "G" 0 1` on both plans (ref: "may write the
same cell (no dimension separates them)"), exactly as the free-slot control `G[j,0]` twice. Correct.
Residual: you cannot write two different constant cells as two base statements of one state (a typed limitation of the
n+1 extent model). Note for the F3-b record; no fix needed in stage 1.

### R3 [P3] Predicate scan state with a constant: reference accepts, both plans refuse (typed)
Scenario (OBSERVED):
```
iter l = 3
predicate G(j, l)
tensor f32 X(j), W(j, k)
G[=2, 0] := X[j]
G[=2, l +1] := G[j, l] · W[j, k]
```
`compileToScheduled` accepts; reference gives shape [3,3] = [0,0,0, 0,0,0, 1,1,1]; f64 and f32 plans refuse with
`CapabilityError.predicateScatterDest "G: predicate scatter destination"`. This is the pre-existing capability tier
for any predicate scatter destination (not new geometry), and typed, but it is a new reference-accepts/plan-refuses
pair reachable from surface syntax. Why tests miss it: no predicate fixture among the scanConst* programs.
Fix: tiny, add one pin documenting it (ref accepts, plans refuse with predicateScatterDest).

### R4 [P3] Docs wording: "hand-built raw one is still refused" is reachable only from a hand-built ScheduledProgram
Where: Eval/AGENTS.md line 64, Eval/Plan/AGENTS.md line 56, Semantics/AGENTS.md line 180, DSL/AGENTS.md line 115,
Compile.lean `checkScanScatterLHSSlot` doc.
Observation: a hand-built TLProgram `.scatter` (and `.assign`) with a raw `.affine (.const 3)` in a scan is now LOWERED by
`lowerArith` (StructuralTest pin, and P6 below), so it is accepted. A raw constant survives only in a hand-built
`ScheduledProgram` that skips `lowerArith`. Compile.lean's comment says exactly that; the AGENTS sentences "only a
hand-built raw one is still refused" read as if a hand-built Stmt were enough. Cosmetic, tiny: say "hand-built
ScheduledProgram".
Value-grep of leanncd (no .lake, papers, spikes) found no remaining statement that scan constants are refused or
unsupported; the only matches are the sentences above and each carries the stage-1 qualification.

## Question verdicts
Q1 Checked: P1a/P1b/P1c as in R2. OBSERVED. No wrong acceptance, no wrong rejection reachable.
Q2 Checked and clean (INFERRED plus fixtures): `rg "#const"` finds the name only at Structural.lean 1141 (construction)
and docs; no name-based check, `reservedAxisName` not involved. The decl `.axis u (some 1)` sizes the axis (scanTwoConst,
scanCoupled, Far fixtures run with correct shapes). Display and serialization of a scan-body synthetic axis were NOT
examined (same axis already appears at top level). unsizedAxis for a scan with only constant LHS slots: not isolated.
Q3 Checked and clean by code reading (INFERRED): collection (`writerGroups`, `boxedSingleGroups`, `scanWriterConflict?`)
only looks at `.plain` statements, so scan constants are never grouped or boxed; the cost is R1. A hand-built `.scatter`
in a scan goes through `lowerArith`'s `.scatter` arm (OBSERVED, P6). ScanOracle, ScanGen and DifferentialTest generators
were NOT read (budget); unconfirmed.
Q4 Checked and clean (OBSERVED). A constant in the scan-axis position: `G(l,j)` with `G[=0, j]` base: compile
`missingBaseCase "G"`; `G(j,l)` with `G[j, =0]` base: `missingBaseCase "G"`. A step without an iterNext slot,
`G[=1, j] := G[l, j]·W` or `G[j, =1]`: compile accepts, preflight `noAdvancingAxis "G"`, reference "scan node has no
iteration axis", both plans `capability noAdvancingAxis`. Typed on all legs, not accepted.
Q5 Checked (OBSERVED): predicate, see R3. `relu(G·W)` and `relu(G·W·W)` with a constant slot: compile refuses
`unsupportedNonlinScatter "G"` (typed, at `checkScatterNonlin`, before `lowerArith`, so a nonlinearity plus a constant is
refused exactly like any scatter). A `where` mask needs an axiswise nonlinearity, so it is unreachable (INFERRED, same
refusal); not run.
Q6 Checked and clean (OBSERVED). Hand-built `.affine (.const (-1))` in base and step of scanConstBoth: compile ok;
reference typed error `evalScatter G: write to output coord [-1, 0] ... outside the destination extent`; f64 and f32:
`scanWriteRowNotAdmitted "G" "G" true 0 0 #[1] (-1)`. Only the step carrying -1 (base free): reference
`inconsistentStateExtent` (3 wide vs 0 wide), plans `scanWriteRowNotAdmitted ... false 0 0 #[0,1] (-1)`. No panic output
and no `.ok` with PANIC in any run. The new Structural.lean comment is true.
Q7 Spot-checked three fixtures by reading plus the implementer's m3 result. scanConstFar pins shape [6,3] (extent n+1;
extent n or n+2 changes the shape) and rows 0..4 as 0. scanConstTrop pins -inf for unreached rows and row 2 = 3,9,15.
scanConstBoth pins 0 rows and 6,66,726. All write each cell once, so sum-versus-overwrite is invisible in all of them (the
collision rule is not this slice's, F3-a covers it). Cannot fail under the stage-1 feature: the `G` assertion of
scanCoupled (G is an unmutated free state; the implementer already says so), and the compile-only guards. No fixture has a
declared pinned axis (R1) or a predicate state (R3).
Q8 Docs: claims true against code and runs except the wording in R4. P6/P6b confirm the -1 sentence.

Unconfirmed: ScanOracle/ScanGen/DifferentialTest generators and the PropertyOracle comparators for hand-built scan
scatters with a constant; display/serialization of the synthetic axis in a scan; `where` mask (unreachable by INFERENCE).
Tool-call count: about 46 of 45 allowed (a slight breach, caused by Repr-instance retries for plan errors); context well under 200k.
