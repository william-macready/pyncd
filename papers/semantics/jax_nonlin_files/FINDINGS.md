# JAX pointwise/axiswise slice: prototype findings

Observations from the prototype branch `worktree-jax-pointwise-plan` (base local `main` `f2616f54`).
Written by the controller from two prototype dispatches, the controller's own completion work and its
independent re-verification. The prototype branch is evidence only: it must NEVER be merged (it carries the
code the patches add); only the package files land on `main`, as with the scatter slice.

## What was built

`affineReference` renders and runs `.pointwise` (`relu`, `sigmoid`, `tanh`, `gelu`, `leakyrelu`) and
`.axiswise` (`softmax`, `normalize`, `l2normalize`, masked or not) plan steps in both precisions, compared to
the Lean dense workers within a MEASURED TOLERANCE (the owner accepted tolerance; exactness is not required).
Render-only: `einsumOnly` and the evidence path (`lowerCheckPlanToCandidate`, `JaxExecutableWellFormed`) keep
refusing these steps, `.scan` stays refused, an inline unary read (`sqrt`, `exp`, `log`, `sin`, `cos`,
reciprocal) is still refused by the assignment gate (`unaryFactor`).

Goal behind it: run a single-layer transformer through BOTH Lean and JAX. The repo's example
(`test/Eval/EvalExamplesTest.lean` example 12) compiles to 14 checked nodes: 10 assignments (JAX already
accepted these), 3 axiswise (causal softmax and two `normalize`), 1 pointwise (relu). Before this slice the 4
nonlinear nodes were refused.

## Commits (prototype branch, in patch order)

| Task | Commit | Subject |
| --- | --- | --- |
| T1 | `e6c9383447a77668a5a934df9aa8baa993597ee9` | `feat(jax): render pointwise and axiswise steps in affineReference` |
| T2 | `465aabbbf5d3923955901d4e89e762d5156dec2f` | `feat(jax): pointwise and axiswise runtime and Lean-vs-JAX differential` |
| T3 | `3efb82ef0848c234d3b5b2ab1e0e8f00b17db72e` | `test(jax): single-layer transformer through Lean and JAX` |
| T4 | `0893a66c` (amended; the T4 patch is authoritative) | `test(jax): Python mutation runner accepts a per-entry verifier` |
| T5 | `5b6933ac` | `test(jax): fixtures that pin softmax row max, relu NaN and the compare path` |
| T6 | `f66bbf1b` (amended once to add the driver-count fix; the T6 patch is authoritative) | `docs(jax): pointwise and axiswise steps render in affineReference (tolerance-compared)` |

Patches (`papers/semantics/jax_nonlin_patches/`, `git format-patch` output) replayed onto a throwaway tree at
`f2616f54` with `patch -p1 --fuzz=0` (git refused a redirect into a second worktree, so `patch` was used):
every patch applied, and 12 of 12 touched files hashed identically to the prototype tip.

## Design decisions taken (and why)

- **D1 render-only.** The existing refusal guards `testPointwiseStepRejectedLocated`,
  `testAxiswiseStepRejectedLocated`, `testMaskedAxiswiseStepRejectedLocated` (EvalPlanCodegen.lean, Slice 5)
  call `lowerCheckPlanToCandidate`, the EVIDENCE door, which still refuses: none of them changed. The two
  `ExecutableTest.lean` hits (`some (.pointwise _) | some (.axiswise _) => false` arms) are exhaustiveness
  arms, unaffected. New guards (section 11 at the end of EvalPlanCodegen.lean) pin the render door and
  re-assert that `einsumOnly` and the evidence door still refuse with `unsupportedStep 0`.
- **D3 mask evaluated in Lean.** A masked axiswise step carries a static row-major `"include"` table of 0/1,
  built by `buildAxiswiseInclude` through the dense worker's own predicate, so the runtime never sees a
  predicate. The worker's `axiswiseIncluded` is private; the only core-file edit is one additive public
  delegating wrapper `axiswiseIncludedPredicate` in `LeanNCD/Eval/Plan/Nonlin.lean` (no existing body
  changed). A mask the worker refuses (unreachable for a checked plan: `maskWidthMismatch`) throws the new
  located `JaxCodegenError.axiswiseIncludeRefused` rather than emit an unmasked table.
- **D4 no support gate.** Unlike scatter there is no `checkJaxPointwiseSupport`: evidence comes from
  `checkPlan`, which already ran `checkPointwise`/`checkAxiswise` (or the F32 variants) under
  `raw.tensorSigs`, selected by the storage kind, and `renderAffineNodesArray` reads exactly that table. No
  standalone renderer takes a caller table, so a re-run could only repeat the check; these steps have no
  compute half to grade. `Executable.lean` is untouched.
- **Records.** `{"kind": "pointwise", "source": s, "dest": d, "shape": [...], "fn": "<name>"}` and
  `{"kind": "axiswise", ..., "axis_pos": n, "fn": "<name>"[, "include": [...]]}`; an unmasked step omits
  `"include"`. Exact observed texts (pinned by guards):
  `{"num_slots": 2, "input_slots": [0], "nodes": [{"kind": "pointwise", "source": 0, "dest": 1, "shape": [3], "fn": "relu"}]}`
  and, for a causal `s <= q` mask over `[3,3]`,
  `{"num_slots": 2, "input_slots": [0], "nodes": [{"kind": "axiswise", "source": 0, "dest": 1, "shape": [3, 3], "axis_pos": 1, "fn": "softmax", "include": [1, 0, 0, 1, 1, 0, 1, 1, 1]}]}`.
- **Runtime semantics** (mirrors `LeanNCD.Eval.Nonlin` operation for operation): relu is
  `where(0 <= x, x, 0)` (Lean `max 0 x`: `relu(NaN) = +0`; never `jnp.maximum`); softmax row maximum and all
  row sums are sequential left folds (`fori_loop`) over the UNMASKED entries; masked entries are 0, an
  all-masked, zero-sum or all-zero row is exactly 0; binary32 gelu/leakyrelu constants are the exact bit
  patterns of Lean's (`0x3F4C422A`, `0x3D372713`, `0x3C23D70A`).

## Observed numbers (all on this machine's XLA CPU backend; observations, not guarantees)

Tolerance constants, chosen BEFORE the full measurement and unchanged since: binary64 `rtol 1e-12`,
`atol 1e-14`; binary32 `rtol 1e-5`, `atol 1e-6`; the check is `|g - w| <= atol + rtol * |w|`.

| function | f64 max rel | f64 max abs | f32 max rel | f32 max abs |
| --- | --- | --- | --- | --- |
| gelu | 4.578e-14 | 4.441e-16 | 2.458e-05 | 8.941e-08 |
| tanh | 1.201e-16 | 1.110e-16 | 6.041e-08 | 5.960e-08 |
| softmax | 4.080e-16 | 1.110e-16 | 0 | 0 |
| sigmoid, leakyrelu, relu, normalize, l2normalize | 0 | 0 | 0 | 0 |

Margins: f64 `atol` about 22 times the worst absolute difference. The f32 gelu relative difference (2.46e-5) is
above `rtol 1e-5` but sits at an output near `3.6e-3`, so the `atol` term covers it (the f32 gelu tolerance is
absolute-driven; `atol` margin about 11 times). Bit-identical counts: sum-based functions (normalize,
l2normalize, sigmoid), leakyrelu and relu are bit-identical to Lean in both precisions except relu/leakyrelu
under jit (below); f32 softmax is bit-identical; f64 softmax differs in 16 of 168 entries; tanh and gelu
differ in some entries. The left-fold sums held: the only differences come from `exp`/`tanh`/`pow`.

Single-layer transformer (T3; hand-chosen non-identity weights; SEQ 3, D 4, H 2, K 2, DFF 4; the causal rows
keep 1, 2 and 3 entries; both precisions; 10 materialized outputs compared, eager and jit):

| output | f64 max rel | f64 max abs | f32 max rel | f32 max abs |
| --- | --- | --- | --- | --- |
| Q, K, V | 0 | 0 | 0 | 0 |
| S | 1.362e-16 | 5.551e-17 | 1.114e-07 | 5.960e-08 |
| AttnOut | 6.940e-16 | 5.551e-17 | 8.617e-08 | 2.980e-08 |
| Attn | 1.325e-16 | 5.551e-17 | 1.080e-07 | 2.980e-08 |
| A | 1.084e-15 | 4.441e-15 | 3.525e-07 | 9.537e-07 |
| F | 9.737e-16 | 3.109e-15 | 2.240e-07 | 7.153e-07 |
| Y | 9.501e-16 | 3.109e-15 | 2.865e-07 | 9.537e-07 |
| H | 3.417e-16 | 2.220e-16 | 1.447e-07 | 1.192e-07 |

Everything passes with the unchanged tolerances; the pure assignments are exact and everything downstream of an
`exp` or a normalize differs by about 1e-16 (f64) or 1e-7 (f32). Pinned plan shape (asserted by the Lean driver):
14 steps = 10 assign / 1 pointwise / 3 axiswise. The transformer's relu input already carries the upstream
libm-vs-XLA difference, so "relu is bit-exact" does not apply to it (the verifier skips that rule and the
per-function statistics for transformer fixtures).

Verifier lines at the final tip (`run-evalplan-nonlin.sh`):
`15 float64 nonlinearity fixtures within rtol 1e-12 / atol 1e-14 of Lean (eager + jit)` and
`15 float32 nonlinearity fixtures within rtol 1e-05 / atol 1e-06 of Lean (eager + jit)`, then, per precision,
`tolerance self-test: 1e-3 relative perturbation and a zeroed output are rejected`,
`require_close canary: a 1e-3 perturbed output is rejected end to end`,
`pins: relu(NaN) = +0, large-negative and huge-masked softmax rows are real distributions`,
`relu signed zero: assign copy turns -0.0 into +0.0 in Lean; relu bit-exact in eager JAX`.

Builds: `Build completed successfully (8844 jobs).` for `LeanNCD Tests JaxExperiment` at the final tip (same as
`main` before the slice; the new driver adds no library module). T1's own build
(`LeanNCD Eval.Plan.ExecutableTest JaxExperiment`) printed `8619 jobs`; `run-evalplan-nonlin.sh` runs its own
`lake build LeanNCD` (`8615 jobs`) and `lake build JaxExperiment` (`8516 jobs`). The FIRST build after the
`Nonlin.lean` edit recompiles thousands of jobs (the whole library downstream of `Plan/Nonlin.lean`), so run it
in the background.

Older verifiers after T2 (dispatch 1, all passed): `run-evalplan-affine.sh` ending
`Lean checked plan -> affine lookup tables -> ordered JAX reference -> Dense agreement passed`,
`run-evalplan-affine32.sh` ending `56 binary32 fixtures, 160 eager/jit output checks: bit-identical to the Lean binary32 reference except the pinned KNOWN_DIVERGENT positions (x64 disabled)`,
`run-evalplan-scatter.sh` printing `10 float64 scatter fixtures bit-identical to Lean (eager + jit)` and
`5 float32 scatter fixtures bit-identical to Lean (eager + jit)`.

## Surprises (each is a planning fact)

1. **Signed zero and relu under jit.** Lean's `relu(-0.0)` fixture gives `+0.0`, because the surface language
   always emits an assignment copy before a pointwise step and that copy starts from `+0` (`+0 + -0 = +0`);
   under `jax.jit` XLA drops that `+0` seed (the pitfall already in `AGENTS.md`). So relu is required
   bit-exact in the EAGER run only; jit compares by value. A signed zero fed DIRECTLY into a pointwise step
   (a raw plan, no assignment copy) is not exercised (parked).
2. **NaN is reachable through the surface.** `0 + NaN = NaN` reaches relu, and Lean's `relu(NaN) = +0` while
   `jnp.maximum` propagates NaN. This is a real behavioural pin, found by mutation JN-P-01 surviving (below).
3. **`T` is a reserved token in `tlprog!`** (tanh outputs are named `Th`). `explicitF64`
   (`test/Eval/ExplicitF64.lean`) is not importable from the JAX driver (`run-evalplan-nonlin.sh` builds only
   `LeanNCD` and `JaxExperiment`): declare every tensor `tensor f64 ...` by hand.
4. **Stale `.pyc` flake in the Python mutation runner.** A same-size mutation restored within the same second
   leaves a bytecode file valid by whole-second mtime and size, so the post-restore baseline ran the mutant
   (`JN-P-12` reported `NOT RESTORED/GREEN` once while `git status` was clean). Fixed in the runner
   (`PYTHONDONTWRITEBYTECODE=1` for the verifier subprocesses); the diagnosis is supported by the flake not
   recurring in three further full runs, not proved by an isolated reproduction.
5. **Existing behaviour that rules out a shorter route to LayerNorm.** A real LayerNorm is expressible in
   Lean (`M[q] := X[q,d] . invd[]`, `C := X + negone[] . M`, variance, `+ eps[]`, `sqrt(...)`, division `/`),
   matches a plain-Float oracle on the reference evaluator and the checked plan (7 nodes, printed to 6
   decimals), but its `sqrt` and division nodes are refused on JAX as `unaryFactor`. This slice does not touch
   that: unary reads on JAX is a separate slice that needs a domain-error decision (Lean fails loud on a
   negative `sqrt`; `jit` cannot raise).

6. **`check-lean-drivers.sh` counted drivers in prose.** Its header and its final line said "five"; the new
   `EvalPlanNonlinSmoke` is the sixth `run_driver`. T6 changes both to "six", so its last line becomes
   `all six drivers ran clean (Lean side only; the Python/JAX verifiers were not run)`. The agents ran the
   script at the T3 state (last line `all five drivers ran clean ...`); after the text edit it was only
   syntax-checked (`bash -n`), not re-run, so the executor's first run of it is the first observation of the
   new line.

## Mutation results

Python (`jax_nonlin_mutations_python.json`, 17 entries `JN-P-01..17`, runner
`mutation_python_manifest.py`, which gained a per-entry `verifier` field and the bytecode fix in T4): the first
observe run killed 13 and left 4 SURVIVORS; after the T5 fixtures the real run is **17/17 PASS**:

| mutant | first run | resolution |
| --- | --- | --- |
| JN-P-01 relu via `jnp.maximum` | survived (only signed zero and NaN differ; no fixture fed a NaN) | T5 fixture `relu_nan`/`relu_nan32`: Lean `relu(NaN) = +0`, JAX NaN is non-finite; killed ("non-finite value") |
| JN-P-02 softmax row max over ALL entries (masked included) | survived (softmax is shift-invariant) | T5 fixture `causal_big`: masked entries 1000/2000/900, so `exp(x - m)` underflows and the row collapses to zeros; killed ("exact-zero pattern differs") |
| JN-P-03 softmax row max from `jnp.maximum` starting at 0 | survived | T5 fixture `aw_neglarge`: rows all below `-999`; killed ("exact-zero pattern differs") |
| JN-P-17 verifier compares the JAX output with itself | survived | T5 canary in `main()`: `require_close` must reject a 1e-3 perturbed output end to end; killed |
| JN-P-08 normalize zero-sum guard dropped | killed, but by a `TypeError` (the mutant was malformed: `inc[..., None]` added a dimension) | mutant rewritten to `jnp.where(inc, xm / s[..., None], zero)`; now killed by "non-finite value" (0/0) |
| JN-P-12 gelu cubic coefficient (same-size edit) | `NOT RESTORED/GREEN` once | the `.pyc` flake (surprise 4); killed and restored in every later run |

Every kept entry's `expect` string is the first failing assertion line the runner observed. Caveat inherited from
the scatter slice: the `expect` strings are generic assertion source lines, so a mutant dying for a different
assertion would not be distinguished by them; the table above records the reason each one died.

Lean (`jax_nonlin_mutations_post.json`, 8 entries `JN-T1-01..08`, `mutation-manifest.sh`): `--check` prints
`manifest OK: 8 entries, 8 selected, every old-string unique`; the real run is `8/8 cycles passed.`, every file
restored byte-identically. Failing-guard lines (valid from T1 on, because no later patch touches
`EvalPlanCodegen.lean`): `JN-T1-01`/`02` lines 2285 and 2297; `03`, `04`, `07` line 2285; `05` line 2280; `06`
line 2278; `08` line 2315 (each `error: experiments/jax_bridge/EvalPlanCodegen.lean:<n>:0: Expression`).

## Process record (Rule 6, Rule 12)

- Dispatch 1 (T1, T2): 105 tool calls against the 60-call cap, about 206,818 subagent tokens, 4,026 s. Its
  report said "roughly 75 tool turns"; the harness count is 105. It also ran one inline heredoc in breach of the
  shell rules (touched only EvalPlanCodegen.lean; the committed contents are what T1 shipped).
- Dispatch 2 (T3, a draft of the Python manifest): 68 tool calls by the harness count (it reported about 72),
  about 130,294 subagent tokens, 387 s. It stopped before running either manifest.
- The controller finished the rest itself (T4 runner commit and its bytecode fix, the T5 survivor fixtures, both
  manifests and their observed `expect` strings, the T6 docs, the patches, the replay) rather than brief a
  third dispatch for mechanical work. Authoring token totals are not measured as one figure.
- Harness quirks: a worktree-isolated session refuses `git -C <other worktree>` and compound commands; scripts
  that need them go through files; replay used `patch -p1 --fuzz=0 -d <dir> -i <patch>`.

## Not verified

- The 3,832-case corpus after this slice (`run-evalplan-affine-corpus.sh`, about 11 minutes): the executor must
  run it. The slice adds node kinds the corpus never emits.
- The three older verifiers were run by dispatch 1 after T2 only; nothing but test fixtures, a runner and docs
  changed afterwards. The executor re-runs all of them.
- Any GPU or non-CPU XLA run: on this CPU the comparison is within tolerance and many functions bit-identical;
  other backends may differ more (the tolerance was measured, not derived).
- (Checked, not a gap:) the scatter slice's Python manifest was re-run with the modified runner at the final
  tip: 16 of 16 `PASS`, so T4 does not regress it. The final-tip full build, the nonlin differential, the
  Python manifest (17/17) and the Lean manifest (`--check`, then 8/8) were all run by the controller.
- Padding or data-driven masks, embedding lookup, RoPE, ALiBi, unary reads (LayerNorm with `eps`), scan: out of
  scope for this slice (see `leanncd/test/Eval/Portfolio/KnownGapTest.lean` for the catalogue).
