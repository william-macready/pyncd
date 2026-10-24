| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| T1-M1 reference Combine.tropical multiplies factors with * (not +) | yes | yes | yes | PASS |
| T1-M2 checked plan f64 tropical factorOp back to .mul | yes | yes | yes | PASS |
| T1-M3 checked plan f32 tropical factorOp back to .mul | yes | yes | yes | PASS |
| T1-M4 maxNaN loses NaN propagation (Max.max) | yes | yes | yes | PASS |
| T1-M5 minNaN32 loses NaN propagation (Min.min) | yes | yes | yes | PASS |
| T1-M6 plan f64 floatOps min arm bypasses minNaN (Min.min) | yes | yes | yes | PASS |
| T1-M7 plan f32 tropical factorId 0x00000000 -> 0x3f800000 | yes | yes | yes | PASS |
| T2-M1 plan bare OOB pad -> ops.zero (real 0) instead of the statement's 0_K | yes | yes | yes | PASS |
| T2-M2 plan unary OOB pad -> pad (0_K) instead of the real zero | yes | yes | yes | PASS |
| T2-M3 plan Iverson false -> ops.zero (real 0) instead of 0_K | yes | yes | yes | PASS |
| T2-M4 plan Iverson true -> decoded real one instead of 1_K | yes | yes | yes | PASS |
| T2-M5 reference gather bare OOB pad -> 0.0 instead of the statement's 0_K | yes | yes | yes | PASS |
| T2-M6 reference Combine.tropical (unit0, unit1) -> (0.0, 1.0): empty sum / empty product | yes | yes | yes | PASS |
| T3-M1 reference scatter fold: combine -> + (max/min collisions summed) | yes | yes | yes | PASS |
| T3-M2 reference scatter init: unit0 -> 0.0 | yes | yes | yes | PASS |
| T3-M3 reference scatter fold: combine -> non-NaN max | yes | yes | yes | PASS |
| T3-M5 checked worker fill: reduceId -> ops.zero | yes | yes | yes | PASS |
| T3-M6 checked worker fold: reduceOp -> overwrite | yes | yes | yes | PASS |
| T3-M7 compile: scatter step algebra ignores agg | yes | yes | yes | PASS |
| T4-M1 (tropicalNonlin removed from checkScheduledDtypes) | yes | yes | yes | PASS |
| T4-M2 (scanStateAlgebraMismatch removed) | yes | yes | yes | PASS |
| T4-M3b (cast table: tropical -> bool accepted) | yes | yes | yes | PASS |
| T4-M3c (cast table: max-plus <-> min-plus accepted) | yes | yes | yes | PASS |
| T4-M3d (cast table: real -> bool also rejected, parked decision 1 broken) | yes | yes | yes | PASS |
| T4-M4b (neutral writer: contracted-axis condition dropped) | yes | yes | yes | PASS |
| T4-M5 (unaryFn exemption removed: unary read cast-checked like a bare read) | yes | yes | yes | PASS |
| T4-M7b (Stmt.algebra ignores the predicate declaration: predicate-ness dropped from the sort) | yes | yes | yes | PASS |
| T5-M1 (cast removed in reference gather: bare read) | yes | yes | yes | PASS |
| T5-M2 (cast removed in plan Dense) | yes | yes | yes | PASS |
| T5-M3 (truth convention flipped, plan Dense) | yes | yes | yes | PASS |
| T5-M4b (cast applied under unary, plan compile) | yes | yes | yes | PASS |
| T5-M5 (cast applied for real statements, plan compile: tropical guard dropped) | yes | yes | yes | PASS |
| T5-M6 (cast applied to the OOB pad, reference) | yes | yes | yes | PASS |
| T5-M7 (cast field not filled: scan base caller) | yes | yes | yes | PASS |
| T5-M9 (cast field not filled: scatter caller) | yes | yes | yes | PASS |
| T5-M11 (checker: castNotAdmitted rejection removed) | yes | yes | yes | PASS |
| T6-M1 (reference state init back to zeros) | yes | yes | yes | PASS |
| T6-M2 (plan f64 state init back to 0.0) | yes | yes | yes | PASS |
| T6-M5 (reference: neutral writers keep their own annotation) | yes | yes | yes | PASS |
| T6-M7 (neutral writers forced real in both backends: pad and cast key lose the state's sort) | yes | yes | yes | PASS |
| T6-M8 (state sort leaks from scratch / other names: sorts not filtered by name) | yes | yes | yes | PASS |
| T6-M9 (compile: max-plus state gets zero init) | yes | yes | yes | PASS |
| T6-M11 (checker: stateInitNotAdmitted rule removed) | yes | yes | yes | PASS |
| T6-M12 (checker: rule rejects tropical init on every state, not only bool) | yes | yes | yes | PASS |
| T7-M1 (oracle: sorted tropical scatter refused again: keeps its max/min agg, so admission refuses nonSum) | yes | yes | yes | PASS |
| T7-M4 (PRODUCTION reference: tropical empty product back to 1.0; caught by the zero-factor rows) | yes | yes | yes | PASS |
| T7-M5 (oracle: empty-fibre total starts at 1_K, i.e. real 0 in a tropical carrier) | yes | yes | yes | PASS |
| T7-M6 (test fixture: declared strided extent back to 7) | yes | yes | yes | PASS |
| T8-M1 (PRODUCTION: min-plus scan state starts at -inf in the checked plan; mirror-asymmetric, caught by the min hand twin RC10m AND by the duality property's grid min case) | yes | yes | yes | PASS |
| T8-M3 (PRODUCTION: predicate read casts false to 0.0 in BOTH tropical sorts; 0.0 is negation-fixed and predicate programs are outside the property, so ONLY the one-sort BoolCastTest hand fixtures catch it, and GN4/GN4m do not discriminate unless the masked row would win) | yes | yes | yes | PASS |
| T8-M4 (ORACLE test-side: the independent unrolling's zero leaf / merge go back to the real sum, i.e. state init back to 0) | yes | yes | yes | PASS |
| T8-M5 (PRODUCTION: a sort-neutral writer votes for the state's sort; flips the PARKED all-neutral pin, and RC10-style neutral-base behaviour where annotations disagree) | yes | yes | yes | PASS |
| T8-M6 (PRODUCTION: binary32 min-plus reduce identity is -inf; asymmetric f32-only bug; caught by the property's plan32 leg AND by Adapter32Test fixture 9 min) | yes | yes | yes | PASS |

53/53 cycles passed.
