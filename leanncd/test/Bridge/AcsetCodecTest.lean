import LeanNCD.DSL.Compile
import LeanNCD.Bridge.AcsetCodec

/-! # Acset codec round-trip regression (Task F)

Computational witness of the Task C theorem `AcsetCodec.toThreadedComposed_fromThreadedComposed`:
decoding the encoded acset tables recovers the original `ThreadedComposed` on the nose, checked by
`decide` over the §12.1 example programs (fixtures 1-5) plus nonlinear-routing round trips added by
`nonlinearity_split_pair_direct_lowering.md` §3.4's slice (fixtures 6-9). A `#guard` failure means
the encode/decode pair drifted out of sync (fires at `lake build`). -/

namespace LeanNCD
open LeanNCD.AcsetCodec

-- 1. Matmul (single contraction step, two external inputs).
#guard toThreadedComposed (fromThreadedComposed (tl!{ Y[i,j] := W[i,k] · X[k,j] }))
        = tl!{ Y[i,j] := W[i,k] · X[k,j] }

-- 2. Causal masked attention (multi-step: linear pre-activation + softmax).
#guard toThreadedComposed (fromThreadedComposed (tl!{
          tensor A(q, s)
          A[q, s.] := softmax(where s ≤ q)(Q[q, d] · K[s, d]) }))
        = tl!{
          tensor A(q, s)
          A[q, s.] := softmax(where s ≤ q)(Q[q, d] · K[s, d]) }

-- 3. Strided convolution (nontrivial reindexing coefficients — exercises the matrix round trip).
#guard toThreadedComposed (fromThreadedComposed (tl!{ Y[i, j] := W[p, r] · X[i + p, 2 * j + r] }))
        = tl!{ Y[i, j] := W[p, r] · X[i + p, 2 * j + r] }

-- 4. Upsample 2× (affine-LHS scatter).
#guard toThreadedComposed (fromThreadedComposed (tl!{
          tensor Out(i, j)
          Out[2 * i, 2 * j] := X[i, j] }))
        = tl!{
          tensor Out(i, j)
          Out[2 * i, 2 * j] := X[i, j] }

-- 5. Coupled scan (one multi-output scan step, six external inputs).
#guard toThreadedComposed (fromThreadedComposed (tl!{
          iter l = 3
          G[j, 0]    := X[j]
          G[j, l +1] := relu(G[j, l] · W_G[j, k] + H[j, l] · U[j, k])
          H[j, 0]    := Y[j]
          H[j, l +1] := relu(H[j, l] · W_H[j, k] + G[j, l] · V[j, k]) }))
        = tl!{
          iter l = 3
          G[j, 0]    := X[j]
          G[j, l +1] := relu(G[j, l] · W_G[j, k] + H[j, l] · U[j, k])
          H[j, 0]    := Y[j]
          H[j, l +1] := relu(H[j, l] · W_H[j, k] + G[j, l] · V[j, k]) }

-- 6. Pointwise ReLU round trip (T2 Task 3, B1). Clone of fixture 1's shape,
-- `NonlinCompileTest.reluProg`'s source: the nonlinear split now lives at the route boundary, not
-- in the source program, so this exercises the physical producer/consumer pair through the codec.
#guard toThreadedComposed (fromThreadedComposed (tl!{ H[i] := relu(W[i, j] · x[j]) }))
        = tl!{ H[i] := relu(W[i, j] · x[j]) }

-- 7. Axiswise softmax round trip (T2 Task 3, B2). Clone of fixture 1's shape,
-- `NonlinCompileTest.softmaxProg`'s source.
#guard toThreadedComposed (fromThreadedComposed (tl!{ Y[q, s.] := softmax(A[q, s]) }))
        = tl!{ Y[q, s.] := softmax(A[q, s]) }

-- 8. Nonlinear chain round trip (T2 Task 3, B3): TWO nonlinear statements, the second reading the
-- first's output. Clone of fixture 6 (B1 above), with a second tanh-split fragment appended.
#guard toThreadedComposed (fromThreadedComposed (tl!{
          H[i] := relu(W[i, j] · x[j])
          Z[i] := tanh(H[i]) }))
        = tl!{
          H[i] := relu(W[i, j] · x[j])
          Z[i] := tanh(H[i]) }

-- 9. Nonlinear scan round trip (T2 Task 3, B4). Clone of fixture 5 (coupled scan), reduced to a
-- single ReLU recurrence: the scan node is copied opaquely at the route boundary (class 8/9), so
-- the ReLU split lives entirely INSIDE the scan node's own payload -- invisible to, hence outside
-- of, the categorical presentation this round trip exercises.
#guard toThreadedComposed (fromThreadedComposed (tl!{
          iter l = 3
          G[j, 0]    := X[j]
          G[j, l +1] := relu(G[j, l] · W_G[j, k]) }))
        = tl!{
          iter l = 3
          G[j, 0]    := X[j]
          G[j, l +1] := relu(G[j, l] · W_G[j, k]) }

end LeanNCD
