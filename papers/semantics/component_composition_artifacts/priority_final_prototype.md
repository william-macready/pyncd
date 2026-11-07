# Indexed component composition: priority field

The final public field is proved in `IndexedComponentCompositionPriority.lean`:

```lean
theorem priority :
    (schedule A B wire).keys.map
        (keyStep (program A B wire) (contract A B wire) (fragment A B wire)
          (sourceToWriter A B wire)) =
      (graph A B wire).steps
```

For occurrence keys, `keyEquiv` and `occurrenceEquiv` expose the component
occurrence; `writer_upstream` and `writer_downstream` identify its *actual*
indexed `sourceToWriter` entry with `mapWriter`. For publication keys, the
existing exact-list `collectorCapabilities_upstream` and
`collectorCapabilities_downstream` equations transport capabilities; the latter
uses `downstream_defined_address` to identify the dependent-shape address.
`keyOrder` preserves the full upstream-then-downstream append. The component
`matched.priority` fields, their `close_success_canonical` equations, and
`graph_steps` establish the final list equality. The proof does not assume
composite priority, composite match, selection, or execution agreement.

Verification: the wrapper build of `IndexedComponentCompositionPriority`
passed on the final source (2973 jobs). A temporary *exact-signature* example
and `#print axioms IndexedComponentComposition.priority` /
`#audit_axioms IndexedComponentComposition` were compiled in that same module
with the required wrapper, then removed; the audited build passed (8601 jobs).
The public theorem uses only `propext`, `Classical.choice`, and `Quot.sound`;
the audit reports 229 namespace constants using only standard axioms.
The transient standalone `+IndexedComponentCompositionPriorityCheck` target
was not registered, so its attempted wrapper build could not run; its exact
example and audit were instead checked within the registered target. The
final source was rebuilt after removing the temporary checks. The full
experiment build is the parent's responsibility, not claimed here.

`priority_final_prototype.patch` is generated mechanically by Git against
the committed collector-only base `05438de5`, from the final source bytes.
No collector proof was reproved or edited. No `sorry`, new axioms,
`native_decide`, or `unsafe`.

Budget: approximately 39 action turns exceeded the 30-action target but
stayed within the 60-action / 250k-context hard cap. The token-report script
returned `no transcript for session
166c28b7-d291-45be-9935-ac49e19535cb`, so cumulative input tokens could
not be measured. No other agent was launched.
