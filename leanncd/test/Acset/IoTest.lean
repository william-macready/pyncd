import LeanNCD.Acset.Io
namespace LeanNCD.Acset
-- helper to fetch a file's content:
private def fileOf (pairs : List (String × String)) (nm : String) : String :=
  (pairs.find? (·.1 == nm)).map (·.2) |>.getD "<missing>"

/-- `writeSBr` returns `Except CsvError` since 2026-07-30 (audit finding #17: an unserializable
    compound `SizeExpr` used to become an empty size field silently). Every instance in THIS file is
    serializable by construction, so unwrap — but loudly: on failure the sentinel makes the
    surrounding `#guard` fail rather than quietly yielding `[]`. Do not replace with `.getD []`. -/
private def wr (inst : SBrInstance) : List (String × String) :=
  match writeSBr inst with
  | .ok fs   => fs
  | .error e => [("writeSBr-FAILED", e)]

-- a small instance: Y[i] := X[i] with a norm axis + identity op + a sample with negative offset.
def inst : SBrInstance :=
  { axisSizes := [(⟨.rawAxis, 0⟩, .lit 5), (⟨.normAxis, 1⟩, .var "2")],
    equations := [{ equationIdx := 0, lhsName := some "Y" }],
    arrays    := [{ equationIdx := 0, slot := 0, name := some "Y", isInput := false,
                    operatorTag := some .maskedSoftmax, normAxis := some ⟨.normAxis,1⟩,
                    datatypeTag := .reals, maxValue := none, bias := none,
                    elementwiseFn := none, opPredicate := some "P", wireLabel := none }],
    arrayAxes := [{ equationIdx := 0, arraySlot := 0, axisUid := ⟨.rawAxis,0⟩,
                    isTarget := true, position := 0 }],
    samples   := [{ equationIdx := 0, reindexingSlot := 1, srcUid := ⟨.rawAxis,0⟩,
                    tgtUid := ⟨.rawAxis,0⟩, coeff := 1, offset := -1 }] }

-- five files in order:
#guard (wr inst).map (·.1) ==
  ["axis_sizes.csv","equations.csv","arrays.csv","array_axes.csv","samples.csv"]
-- arrays.csv header is the EXACT Python column line:
#guard ((fileOf (wr inst) "arrays.csv").splitOn "\r\n")[0]! ==
  "equation_idx,slot,name,is_input,operator_tag,norm_axis,datatype_tag,max_value,bias,elementwise_fn,op_predicate,wire_label"
-- the one arrays data row encodes exactly (note empty fields for none):
#guard ((fileOf (wr inst) "arrays.csv").splitOn "\r\n")[1]! ==
  "0,0,Y,false,masked_softmax,NormAxis:1,reals,,,,P,"
-- samples row with negative offset:
#guard ((fileOf (wr inst) "samples.csv").splitOn "\r\n")[1]! == "0,1,RawAxis:0,RawAxis:0,1,-1"
-- axis_sizes with a FreeNumeric (?2):
#guard ((fileOf (wr inst) "axis_sizes.csv").splitOn "\r\n")[2]! == "NormAxis:1,?2"
-- every file ends with \r\n:
#guard ((wr inst).all (fun p => p.2.endsWith "\r\n"))

-- ── #17: an UNSERIALIZABLE size must be an error, not a corrupt empty field ──────────────────
-- Probed 2026-07-30: `writeSBr` used to emit `RawAxis:1,` (an axis with an EMPTY size) and return
-- normally, even though `encodeSize` had already refused the compound expression. `decodeSize ""`
-- then fails on read, so the corruption surfaced far from its cause. Nothing else in this file
-- exercises the failure path — every other instance here is serializable by construction.
def unserializableInst : SBrInstance :=
  { axisSizes := [(⟨.rawAxis, 1⟩, .add (.lit 2) (.lit 3))],   -- compound ⇒ encodeSize errors
    equations := [], arrays := [], arrayAxes := [], samples := [] }

#guard (writeSBr unserializableInst).toOption.isNone
-- ...and the failure path is genuinely taken (the `wr` sentinel appears), so this cannot pass by
-- accident on a success that merely lacked the row:
#guard (wr unserializableInst).any (fun p => p.1 == "writeSBr-FAILED")

-- The same must hold for an unserializable `ArrayRow.maxValue` (the `encSizeOpt` path):
def unserializableMaxVal : SBrInstance :=
  { axisSizes := [], equations := [],
    arrays    := [{ equationIdx := 0, slot := 0, name := none, isInput := false,
                    operatorTag := none, normAxis := none, datatypeTag := .reals,
                    maxValue := some (.mul (.lit 2) (.lit 3)), bias := none,
                    elementwiseFn := none, opPredicate := none, wireLabel := none }],
    arrayAxes := [], samples := [] }

#guard (writeSBr unserializableMaxVal).toOption.isNone

-- ── Task 4: round-trip property  readSBr (wr inst) = .ok inst ──

#guard readSBr (wr inst) == .ok inst

-- empty instance round-trips:
def emptyInst : SBrInstance := { axisSizes := [], equations := [], arrays := [], arrayAxes := [], samples := [] }
#guard readSBr (wr emptyInst) == .ok emptyInst

-- a richer instance: two equations, an input + output array, multiple axes/samples, negatives, ?id sizes
def inst2 : SBrInstance :=
  { axisSizes := [(⟨.rawAxis,0⟩, .lit 8), (⟨.natAxis,2⟩, .var "5")],
    equations := [{ equationIdx := 0, lhsName := some "T" }, { equationIdx := 1, lhsName := some "Y" }],
    arrays := [{ equationIdx := 1, slot := 0, name := some "Y", isInput := false,
                 operatorTag := some .linear, normAxis := none, datatypeTag := .natural,
                 maxValue := some (.lit 3), bias := some true, elementwiseFn := some "relu",
                 opPredicate := none, wireLabel := some "w0" },
               { equationIdx := 1, slot := 1, name := some "X", isInput := true,
                 operatorTag := none, normAxis := none, datatypeTag := .reals,
                 maxValue := none, bias := none, elementwiseFn := none, opPredicate := none, wireLabel := none }],
    arrayAxes := [{ equationIdx := 1, arraySlot := 0, axisUid := ⟨.rawAxis,0⟩, isTarget := true, position := 0 },
                  { equationIdx := 1, arraySlot := 1, axisUid := ⟨.natAxis,2⟩, isTarget := false, position := 1 }],
    samples := [{ equationIdx := 1, reindexingSlot := 1, srcUid := ⟨.rawAxis,0⟩, tgtUid := ⟨.natAxis,2⟩, coeff := 2, offset := -3 }] }
#guard readSBr (wr inst2) == .ok inst2

-- a missing file errors:
#guard (readSBr [("axis_sizes.csv","axis_uid,size\r\n")]).toOption == none
end LeanNCD.Acset
