import LeanNCD.Eval.Tensor
namespace LeanNCD.Eval
open DenseTensor
#guard DenseTensor.sizeOf [2,3] == 6
#guard strides [2,3,4] == [12,4,1]
#guard flatIdx [2,3] [1,2] == 5
#guard (zeros [2,3]).data.size == 6
-- set! then get! round-trips:
#guard ((zeros [2,3]).set! [1,2] 7.0).get! [1,2] == 7.0
-- ofFn agrees with get! and is row-major consistent with flatIdx:
#guard (ofFn [2,2] (fun c => Float.ofNat (flatIdx [2,2] c))).get! [1,1] == 3.0
#guard (ofFn [2,3] (fun c => Float.ofNat (c.headD 0))).get! [1,2] == 1.0
-- approxEq: reflexive true; perturbation false:
#guard approxEq (ofFn [3] (fun _ => 1.0)) (ofFn [3] (fun _ => 1.0))
#guard ! approxEq (ofFn [3] (fun _ => 1.0)) ((ofFn [3] (fun _ => 1.0)).set! [0] 2.0)
-- allCoords enumerates the full space in row-major order:
#guard allCoords [2,2] == [[0,0],[0,1],[1,0],[1,1]]

/-! ## f32 slice Task 3, fixture 15: the `DenseTensor` compatibility shim

`DenseTensor` is now an ALIAS for `DenseTensorOf Float`, and changing a structure into an alias
synthesizes none of the original's generated names. All three are preserved explicitly in
`Eval/Tensor.lean`; these checks are what distinguishes a real compatibility shim from an `abbrev`
that preserves only the type name. A repo-wide grep for the three names gives the complete set of
pre-existing direct users — `KernelDenseTest`, `GraphDenseTest`, `NonlinDenseTest`, and
`Portfolio.ScatterNonlinRejectTest` — all of which are in the default `Tests` target and must
compile unmigrated; each form those four files actually use is exercised below. -/

/-- `DenseTensor.mk` still names the binary64 carrier's constructor, applied to the two original
    field values in order (`Portfolio.ScatterNonlinRejectTest`'s form). -/
def shimSample : DenseTensor := DenseTensor.mk [2] #[1.0, 2.0]

-- `DenseTensor.shape`/`DenseTensor.data` are usable as standalone FUNCTION VALUES — the form
-- `GraphDenseTest`/`NonlinDenseTest`/`KernelDenseTest` use (`.map DenseTensor.data`), and the form
-- a bare abbreviation of the generic projection does not support.
#guard (some shimSample).map DenseTensor.shape == some [2]
#guard (some shimSample).map DenseTensor.data == some #[1.0, 2.0]

-- ... and through ordinary field notation on the alias.
#guard shimSample.shape == [2]
#guard shimSample.data == #[1.0, 2.0]

-- Structure-instance and anonymous-constructor notation still elaborate at the alias, which is how
-- every store literal in the Dense test suites is written.
#guard ({ shape := [2], data := #[1.0, 2.0] } : DenseTensor).data.size == 2
#guard (⟨[2], #[1.0, 2.0]⟩ : DenseTensor).shape == [2]

-- The binary32 carrier is a DIFFERENT instantiation of the same shell, with native `Float32`
-- storage — not `DenseTensor` relabelled.
#guard ({ shape := [2], data := #[Float32.ofBits 0x3f800000, Float32.ofBits 0] } :
          DenseTensor32).data.map Float32.toBits == #[0x3f800000, 0]

end LeanNCD.Eval
