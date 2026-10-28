# B5 final mutation results

Controller-run stock manifests on guard-fixed commit
`8a8505d19d7242d3a1c62aa13d0a2fbb86b02307`, integrated as `b5028559`.
The controller verified that both checkouts have identical `leanncd/` source.
Unfiltered applicability checks passed for all 8 pre and 16 post rows.

Every PASS below means: the actual mutated build failed; every manifest `expect`
string was present; the mutated file was restored byte-identically; and the
restored target build passed. No setup failure, survival or uniqueness-only check
is counted as a kill. Both manifest commands exited 0; final fix checkout clean.

| Manifest | Mutation | Intended distinction | Cycle, expected failure, restoration |
|---|---|---|---|
| pre | B5-M03 | Collector uses agreed tropical algebra | PASS |
| pre | B5-M11 | B6 static range rejection retained | PASS |
| pre | B5-M12 | Scatter folds rather than overwrites | PASS |
| pre | B5-M13 | Native f32 source fold order | PASS |
| pre | B5-M14 | Holes use additive identity | PASS |
| pre | B5-M15 | Collector retains every writer | PASS |
| pre | B5-M16-FIX | Reference scratch privacy | PASS |
| pre | B5-C02 | Actual JAX B5 pre-emission scatter gate | PASS |
| post | B5-M01 | Exact writer extent equality, not containment | PASS |
| post | B5-M02 | Neutral scatter adopts agreed algebra | PASS |
| post | B5-M04 | Scatter group publishes tropical sort | PASS |
| post | B5-M05 | All-scatter needs a declaration | PASS |
| post | B5-M06 | Collector basis UIDs are distinct | PASS |
| post | B5-M07 | Explicit bare scatter is not fallback assign | PASS |
| post | B5-M08 | True multi-axis geometry remains refused | PASS |
| post | B5-M09 | Geometry normalizes canceling coefficients | PASS |
| post | B5-M10 | Mismatch names actual dimension | PASS |
| post | B5-M17 | Public route does not silently admit B5 | PASS |
| post | B5-O01 | Independent normalized geometry | PASS |
| post | B5-O02 | Independent stride-aligned extent | PASS |
| post | B5-O03 | Independent tropical scatter entry | PASS |
| post | B5-O04 | Independent exact writer shape | PASS |
| post | B5-C01 | Unsized source is not default extent zero | PASS |
| post | B5-R01 | Undeclared fallback basis rank | PASS |

**Final result: 24/24 distinct manifest rows killed as intended and restored green.**
The early four oracle cycles and original activation's 24-row run also passed;
those repeated observations are not additional distinct mutants.

## Direct review-fix cycle

The final shape review exposed a top-level direct iteration assignment bypassing
B5's ordinary-bare precondition. A separate Direct-path stock cycle,
`B5-assignment-ordinary-slots`, removed only the new predicate. Both new exact
source-error guards failed; legacy and legal free/freeNorm neighbors remained.
Mutation exit 1, restore hashes exit 0, restored native/boundary build exit 0.
No new manifest entry was added. This is one additional isolated guard cycle,
not part of the 24-row manifest count.

Exact commands, original expected failures and final table logs are preserved
in the execution session's `files/` directory. See
[the execution record](additive_b5_record.md) for full-build, review and budget
evidence; the unchanged manifests contain every exact substitution and target.
