| Mutation | Cycle (broke, then restored build green) | File byte-identical | Expected failure seen | Result |
|---|---|---|---|---|
| S5-T7b-F1 missing-X raw binding becomes present including empty tensors | yes | yes | yes | PASS |
| S5-T7b-F2 missing-Z raw binding becomes present including empty tensors | yes | yes | yes | PASS |
| S5-T7b-F3 extra-H raw binding becomes absent including empty tensors | yes | yes | yes | PASS |
| S5-T7b-F4 extended history observation substitutes the shorter bound | yes | yes | yes | PASS |
| S5-T7b-F5 selected mixed-registry operator becomes identity | yes | yes | yes | PASS |
| S5-T7b-P1 unused mixed-registry entry changes binary arity | yes | yes | yes | PASS |

6/6 cycles passed.
