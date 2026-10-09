| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| T1-UID-position-alias (V1) | yes | yes | yes | PASS |
| T1-UID-wrong-inverse-permutation (V3) | yes | yes | yes | PASS |
| V5 requested freshness omits output/free support (intended proof: BinderScope.requested_fresh) | yes | yes | yes | PASS |
| V6 domain check removed (intended contract: resolveUID domain witness) | yes | yes | yes | PASS |
| T2 prefix-domain acceptance (A1) | yes | yes | yes | PASS |
| T2 output slot reorder (A3/A4) | yes | yes | yes | PASS |
| T2 support over-contraction (A5/B4) | yes | yes | yes | PASS |
| T2 duplicate resolved axis declaration shadow (A9; A9/A10 duplicate-declaration family) | yes | yes | yes | PASS |
| T2 A11 (write role guard removed; writable contract protected) | yes | yes | yes | PASS |
| T2 A12 (absent domain inferred from input shape) | yes | yes | yes | PASS |
| T2 inputs: fabricate missing declared input bindings (A13/A14) | yes | yes | yes | PASS |
| T2 inputs: skip shape rejection and repair short payloads (A15/A16) | yes | yes | yes | PASS |
| T3-P1 first-statement single-target role shortcut | yes | yes | yes | PASS |
| T3-P3 attached original tag overwritten by permuted ordinal | yes | yes | yes | PASS |
| T3-P4 (deduplicate original occurrences by output and ordered operand signature) | yes | yes | yes | PASS |
| T3-P5 (omit publications for nonoutput defined tensors) | yes | yes | yes | PASS |
| T3-P6 (omit the entire coordinate domain of tensors without statements) | yes | yes | yes | PASS |
| T3-P9 exact nested read footprint loses all inner reads | yes | yes | yes | PASS |
| T4-B2-BOUNDARY (lose the zero contraction bound) | yes | yes | yes | PASS |
| T4-B3-BOUNDARY (change one repeated destination slot) | yes | yes | yes | PASS |
| T4-B4-bias-reduced-over-another-term-bound | yes | yes | yes | PASS |
| T4-B6-drop-second-target-local-statement-occurrences | yes | yes | yes | PASS |
| T5-F11-F12-final-only-envelope (supplementary payload profile guard) | yes | yes | yes | PASS |
| T5-D6-trace-index-zip-without-occurrence-key-normalization | yes | yes | yes | PASS |
| T5-D7 wrong differing coordinate | yes | yes | yes | PASS |
| T5-D8 prefix shape comparison | yes | yes | yes | PASS |
| T5-D9 original source ordinal dropped | yes | yes | yes | PASS |
| T5 checked compile/preparation/runtime renderer causes collapsed (D11-D13) | yes | yes | yes | PASS |
| T5-D15 successful native observation discards stored warnings | yes | yes | yes | PASS |
| T5-D14 guessed native body causal localization without a hook | yes | yes | yes | PASS |
| T6-F4 diagonal write wrongly refused by repeated-output UID guard | yes | yes | yes | PASS |
| T6-F5 independent oracle zero-domain assignment made singleton | yes | yes | yes | PASS |
| T6-F8 independent oracle packing transposed | yes | yes | yes | PASS |
| T6-F7 source sum-product terms deduplicated before original term indexing | yes | yes | yes | PASS |
| T6-zero-normalization-removed (F11 comparison-only injected signed-zero observation) | yes | yes | yes | PASS |
| T6-policy-f32-source-silently-rewritten-to-f64 (F13) | yes | yes | yes | PASS |
| T6-policy-multiple-definitions-falsely-marked-shared (F14/F15) | yes | yes | yes | PASS |
| T6-F18 independent oracle slots merge actual UID into first assignment | yes | yes | yes | PASS |
| T6-F17-P6 publication scan drops final coordinate of every defined domain | yes | yes | yes | PASS |

39/39 cycles passed.
