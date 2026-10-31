# Scatter-geometry slice A: replay verification

* Base (local main at replay): `6715e1280961b87423b3daa85942ce26113f7507`
* Replay branch `replay-scatter-geometry-a` code head (before the verification commit): `ef48df69ad258640d3caefde5e8808b2f9648ebd`
* Prototype head compared against: `e5bb6b3c`
* Patch application (prototype order T1, T2, T3, T3b-scan-const, T3b-scan-pin, T5-tropical, T4-docs): all `git apply --check` + `git apply` clean, no repair by hand.
* Task 3 committed as TWO commits (3a constant, 3b scan-const with the pin folded in; pin applied before the tropical task). The pin applied cleanly before T5.
* Final six patches in `papers/semantics/additive_scatter_geometry_a_patches/` regenerated with `git diff parent..commit`. Applying all six in order onto base main in a scratch worktree reproduced the replay head tree for leanncd/ and the two papers docs: tree `069ba7cc0663e057351ec811090c538cae75e29d` equal, empty diff.
* Replay vs prototype e5bb6b3c: empty diff over leanncd/ + the two docs.
* Build (replay head): `lake-build.sh ... LeanNCD Tests JaxExperiment` -> Build completed successfully (8843 jobs). Per-task builds not measured.
* Mutation manifest: `--check` unfiltered OK (31 entries, every old-string unique); then runs per task, all restored (git status showed no production file modified after each).
* Manifest edits: task T3b->T3, T5->T4, labels SGA-T5-* -> SGA-T4-* (SGA-T3b-* kept), line numbers removed from expect strings (SGA-T4-01..03 now `error: test/Semantics/SourceSortedDifferentialTest.lean:` + `Docstring on `#guard_msgs` does not match generated message:`). old/new/targets unchanged. The prototype ledger copy is `additive_scatter_geometry_a_files/proto_notes.md` with the T4 section "Files edited (8)" corrected to 7.
* Defects: none. Outcomes equal the ledger (31/31 killed, no survivors).
* Budget: the 45-tool-call budget was exceeded (about 45 calls; most extra calls were wait calls on the 31-cycle mutation run). Surfaced per Rule 6.

## End-of-task commits and tree hashes

| Task | commit | tree |
|---|---|---|
| Task 1 (T1-extent) | `c412cabe47e5494f63348a56b7e6f76538e7011c` | `514b46d3f55fd72917a68b1a0b95def209115385` |
| Task 2 (T2-multi-axis) | `0ed0e599a535d0e4ace26370dafe7075f09eac7b` | `22942e5fc89a913e14ba3df11b91e84ee7dd8122` |
| Task 3a (T3a-constant) | `a9f06488e87e753a8202fdfa7af2f5f3b66cca69` | `392e35f58c2d23b3cd9f3443606f5c505ecdb03b` |
| Task 3b (T3b-scan-const + pin) | `27ad9336854adb584bd66bcdffe2f7939721a185` | `0908724c52d61c24d72a7ecbec224e17d04a1d1f` |
| Task 4 (T4-tropical-fixtures) | `e4a4f8bcc33b98035a5b4671904882df34d0d494` | `b9dc29c509fd9e3730722a8639ab5e50d948afe1` |
| Task 5 (T5-docs) | `ef48df69ad258640d3caefde5e8808b2f9648ebd` | `069ba7cc0663e057351ec811090c538cae75e29d` |

## Blob hashes (replay head == prototype e5bb6b3c for every path)

| path | blob | owning task(s) | equal |
|---|---|---|---|
| `leanncd/LeanNCD/DSL/AGENTS.md` | `077d2170e8a4f38ad9a9c5924102f51e9efbfd01` | T5 | yes |
| `leanncd/LeanNCD/DSL/Ast.lean` | `e804a5b3ed927b93a1f4923f6a28002711364e16` | T1, T3a | yes |
| `leanncd/LeanNCD/DSL/Pipeline/Structural.lean` | `769135b75a17a9a417f31236c8d7acca203e1d27` | T3a, T3b | yes |
| `leanncd/LeanNCD/Eval/AGENTS.md` | `5636792eb0aef0a4a38a01e80a8ef4f3ce9241e4` | T5 | yes |
| `leanncd/LeanNCD/Eval/Plan/AGENTS.md` | `91affebe90de89f1343e3603da0cd2c514246a7d` | T5 | yes |
| `leanncd/LeanNCD/Eval/Plan/Check.lean` | `ad4b61ebef7757f74cc7a7e0ec84374d9454b89b` | T1 | yes |
| `leanncd/LeanNCD/Eval/Plan/Compile.lean` | `fc821872cd2ae77163327f7a98572d2ea64edb02` | T2, T3a | yes |
| `leanncd/LeanNCD/Eval/Plan/Error.lean` | `0701c926a9c7784bbbd092870bc270c0578bac32` | T5 | yes |
| `leanncd/LeanNCD/Exec/Uid.lean` | `637fbafd007c00a6270ebf954ba22349a842d7a7` | T3a, T3b | yes |
| `leanncd/LeanNCD/Semantics/AGENTS.md` | `d9c750e5c85e24e63ca6e0fc772e981fa20761ba` | T5 | yes |
| `leanncd/LeanNCD/Semantics/Source/Differential.lean` | `66a88a8d0831c8d43037ec948b9f07d53f4d97c0` | T1 | yes |
| `leanncd/lakefile.toml` | `235b03c2e9e0016f413cc7598a223af664fd30c3` | T1 | yes |
| `leanncd/test/DSL/Pipeline/StructuralTest.lean` | `1e419a9e34b755cfb836feadef78b76871222b43` | T3a, T3b | yes |
| `leanncd/test/Eval/Plan/CompileTest.lean` | `222b2ce10f58f289bc4f40289439984cd4c9acbd` | T2, T3a | yes |
| `leanncd/test/Eval/Plan/ScatterCheckTest.lean` | `4697dc7211d4cfb74594d193e788c4533c6d8572` | T1 | yes |
| `leanncd/test/Eval/Plan/ScatterGeometryTest.lean` | `920f35a4714e171c0134ee92519664281ccc64c1` | T1, T2, T3a | yes |
| `leanncd/test/Semantics/SourceDifferentialScatterTest.lean` | `42a3c0d9ae5b4ce6bed27f7e1eafb00310148569` | T1, T2, T3a | yes |
| `leanncd/test/Semantics/SourceSortedDifferentialTest.lean` | `1fcc04a76b7f01e927c91f7a9bd89dd828de7f70` | T4 | yes |
| `papers/backend_missing_functionality.md` | `1bfd3c037e98d9baeed7ff25f594cbb6c899da76` | T5 | yes |
| `papers/scatter_affine_lhs_writes.md` | `c6a13747e5136c6572cbdaa270644be3087e10f9` | T5 | yes |

## Mutation results (31 entries; every cycle: broke, restored build green, file byte-identical, expect strings seen)

| label | task | result | killing module | expect |
|---|---|---|---|---|
| SGA-T1-01 | T1 | killed (PASS) | Eval.Plan.ScatterCheckTest | error: test/Eval/Plan/ScatterCheckTest.lean: |
| SGA-T1-02 | T1 | killed (PASS) | Eval.Plan.ScatterCheckTest | error: test/Eval/Plan/ScatterCheckTest.lean: |
| SGA-T1-03 | T1 | killed (PASS) | Eval.Plan.ScatterCheckTest | error: test/Eval/Plan/ScatterCheckTest.lean: |
| SGA-T1-04 | T1 | killed (PASS) | Eval.Plan.ScatterCheckTest | error: test/Eval/Plan/ScatterCheckTest.lean: |
| SGA-T1-05 | T1 | killed (PASS) | Eval.Plan.ScatterCheckTest | error: test/Eval/Plan/ScatterCheckTest.lean: |
| SGA-T1-06 | T1 | killed (PASS) | Eval.Plan.ScatterCheckTest | error: test/Eval/Plan/ScatterCheckTest.lean: |
| SGA-T1-07 | T1 | killed (PASS) | Eval.Plan.ScatterCheckTest | error: test/Eval/Plan/ScatterCheckTest.lean: |
| SGA-T1-08 | T1 | killed (PASS) | Eval.Plan.ScatterCheckTest | error: test/Eval/Plan/ScatterCheckTest.lean: |
| SGA-T1-09 | T1 | killed (PASS) | Semantics.SourceDifferentialScatterTest | error: test/Semantics/SourceDifferentialScatterTest.lean: |
| SGA-T2-01 | T2 | killed (PASS) | Eval.Plan.CompileTest | error: test/Eval/Plan/CompileTest.lean: |
| SGA-T2-02 | T2 | killed (PASS) | Eval.Plan.CompileTest | error: test/Eval/Plan/CompileTest.lean: |
| SGA-T2-03 | T2 | killed (PASS) | Eval.Plan.CompileTest | error: test/Eval/Plan/CompileTest.lean: |
| SGA-T2-04 | T2 | killed (PASS) | Eval.Plan.B5BoundaryTest | error: test/Eval/Plan/B5BoundaryTest.lean: |
| SGA-T2-05 | T2 | killed (PASS) | Eval.Plan.B5cSingleBoxTest | error: test/Eval/Plan/B5cSingleBoxTest.lean: |
| SGA-T2-06 | T2 | killed (PASS) | Eval.Plan.B5NativeTest | error: test/Eval/Plan/B5NativeTest.lean: |
| SGA-T2-07 | T2 | killed (PASS) | Semantics.SourceDifferentialScatterTest | error: test/Semantics/SourceDifferentialScatterTest.lean: |
| SGA-T3-01 | T3 | killed (PASS) | Eval.Plan.ScatterGeometryTest | error: test/Eval/Plan/ScatterGeometryTest.lean: |
| SGA-T3-02 | T3 | killed (PASS) | Eval.Plan.ScatterGeometryTest | error: test/Eval/Plan/ScatterGeometryTest.lean: |
| SGA-T3-03 | T3 | killed (PASS) | Eval.Plan.ScatterGeometryTest | error: test/Eval/Plan/ScatterGeometryTest.lean: |
| SGA-T3-04 | T3 | killed (PASS) | Eval.Plan.ScatterGeometryTest | error: test/Eval/Plan/ScatterGeometryTest.lean: |
| SGA-T3-05 | T3 | killed (PASS) | Eval.Plan.ScatterGeometryTest | error: test/Eval/Plan/ScatterGeometryTest.lean: |
| SGA-T3-06 | T3 | killed (PASS) | Eval.Plan.B5BoundaryTest | error: test/Eval/Plan/B5BoundaryTest.lean: |
| SGA-T3-07 | T3 | killed (PASS) | Eval.Plan.B5BoundaryTest | error: test/Eval/Plan/B5BoundaryTest.lean: |
| SGA-T3-08 | T3 | killed (PASS) | Eval.Plan.ScatterGeometryTest | error: test/Eval/Plan/ScatterGeometryTest.lean: |
| SGA-T3-09 | T3 | killed (PASS) | DSL.Pipeline.StructuralTest | error: test/DSL/Pipeline/StructuralTest.lean: |
| SGA-T3b-01 | T3 | killed (PASS) | DSL.Pipeline.StructuralTest | error: test/DSL/Pipeline/StructuralTest.lean: |
| SGA-T3b-02 | T3 | killed (PASS) | DSL.Pipeline.StructuralTest | error: test/DSL/Pipeline/StructuralTest.lean: |
| SGA-T3b-03 | T3 | killed (PASS) | DSL.Pipeline.StructuralTest | error: test/DSL/Pipeline/StructuralTest.lean: |
| SGA-T4-01 | T4 | killed (PASS) | Semantics.SourceSortedDifferentialTest | error: test/Semantics/SourceSortedDifferentialTest.lean: + Docstring on `#guard_msgs` does not match generated message: |
| SGA-T4-02 | T4 | killed (PASS) | Semantics.SourceSortedDifferentialTest | error: test/Semantics/SourceSortedDifferentialTest.lean: + Docstring on `#guard_msgs` does not match generated message: |
| SGA-T4-03 | T4 | killed (PASS) | Semantics.SourceSortedDifferentialTest | error: test/Semantics/SourceSortedDifferentialTest.lean: + Docstring on `#guard_msgs` does not match generated message: |

Killed/total per task: T1 9/9, T2 7/7, T3 12/12, T4 3/3

