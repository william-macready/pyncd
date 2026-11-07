# Indexed component composition priority prototype

Status: compiled partial only. Exact-list collector lookup is proved for transported upstream defined addresses and transported downstream defined addresses. The downstream proof assumes B is defined; boundary B inputs do not introduce independent collectors. Both proofs use mapped assembled contract rows, embedding address injectivity, and the structural disjointness of the accepted local defined images. No writer read/capability list is converted to a set.

The full priority field is **not yet proved**: its dependency `IndexedComponentCompositionMatch` is active WIP and fails its downstream address cast proof. Once that module builds, specialize occurrence key steps with its `writer_upstream`/`writer_downstream`; publication keys use these collector lemmas and `downstream_defined_address`. Map over `keyOrder`, apply both local `matched.priority` equations, and rewrite `graph_steps` with the local `close_success_canonical` equations. No composite match, selection agreement, or runner premise is needed.

Required final signature:

```lean
theorem priority :
    (schedule A B wire).keys.map
        (keyStep (program A B wire) (contract A B wire) (fragment A B wire)
          (sourceToWriter A B wire)) =
      (graph A B wire).steps
```

Verification: `bash /Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-composition/leanncd/scripts/lean-file.sh /Users/williammacready/code/python/pyncd.worktrees/follow-directions-component-composition/leanncd experiments/indexed_execution/IndexedComponentCompositionPriority.lean` passed with no diagnostics. Full priority build and snippet check were not run successfully; no full match is claimed. No `sorry`, new axioms, `native_decide`, or `unsafe`.

## Mechanically generated compiled source patch

```diff
diff --git a/leanncd/experiments/indexed_execution/IndexedComponentCompositionPriority.lean b/leanncd/experiments/indexed_execution/IndexedComponentCompositionPriority.lean
new file mode 100644
index 00000000..9e558b2d
--- /dev/null
+++ b/leanncd/experiments/indexed_execution/IndexedComponentCompositionPriority.lean
@@ -0,0 +1,96 @@
+import IndexedComponentCompositionAssemble
+
+namespace IndexedComponentComposition
+
+open LeanNCD.Semantics
+open LeanNCD.Semantics.Program
+open IndexedComponentTransport
+open IndexedOpenComposition
+
+variable {σA σB : Declarations Unit}
+variable [Fintype σA.Tensor] [DecidableEq σA.Tensor]
+variable [Fintype σB.Tensor] [DecidableEq σB.Tensor]
+variable (A : MatchedComponent σA) (B : MatchedComponent σB)
+variable (wire : Boundary A B)
+
+private theorem find_transported_collector_row {α β : Declarations Unit}
+    [DecidableEq (Address α)] [DecidableEq (Address β)]
+    (f : Embedding α β) (rename : Nat → Nat)
+    (rows : List (Address α × List Nat)) (a : Address α) :
+    (rows.map (mapRow f rename)).find?
+        (fun row => decide (row.1 = f.address a)) =
+      (rows.find? (fun row => decide (row.1 = a))).map
+        (mapRow f rename) := by
+  induction rows with
+  | nil => rfl
+  | cons row rows ih =>
+    by_cases h : row.1 = a
+    · simp [List.find?, mapRow, h]
+    · have h' : f.address row.1 ≠ f.address a :=
+        fun eq => h (f.address_injective eq)
+      simp [List.find?, mapRow, h, h', ih]
+
+private theorem find_outside_collector_row {α β : Declarations Unit}
+    [DecidableEq (Address β)] (f : Embedding α β) (rename : Nat → Nat)
+    (rows : List (Address α × List Nat)) (z : Address β)
+    (h : ∀ row ∈ rows, f.address row.1 ≠ z) :
+    (rows.map (mapRow f rename)).find?
+      (fun row => decide (row.1 = z)) = none := by
+  induction rows with
+  | nil => rfl
+  | cons row rows ih =>
+    simp [mapRow, h row (by simp), ih (by
+      intro r hr
+      exact h r (by simp [hr]))]
+
+theorem collectorCapabilities_upstream
+    (a : Address σA) (ha : A.contract.input a.1 = false) :
+    collectorCapabilities (contract A B wire) ((upstream A B).address a) =
+      (collectorCapabilities A.contract a).map upstreamId := by
+  letI := Program.Executor.addressEq (σ := σA)
+  letI := Program.Executor.addressEq (σ := declarations A B)
+  have hbFacts := ClosureFacts.of_close B.matched.close_ok
+  have hnone :
+      (B.contract.collectors.map
+        (mapRow (downstream A B wire) downstreamId)).find?
+        (fun row => decide (row.1 = (upstream A B).address a)) = none := by
+    apply find_outside_collector_row (downstream A B wire) downstreamId
+    intro row hr heq
+    exact (closureScope A B wire).defined_disjoint a row.1 ha
+      (hbFacts.collectors_defined row hr) heq.symm
+  change (((A.contract.collectors.map (mapRow (upstream A B) upstreamId) ++
+      B.contract.collectors.map (mapRow (downstream A B wire) downstreamId)).find?
+      (fun row => decide (row.1 = (upstream A B).address a))).map Prod.snd).getD [] =
+    (collectorCapabilities A.contract a).map upstreamId
+  rw [List.find?_append, hnone, Option.or_none,
+    find_transported_collector_row]
+  unfold collectorCapabilities
+  cases A.contract.collectors.find? (fun row => decide (row.1 = a)) <;>
+    simp [mapRow]
+
+theorem collectorCapabilities_downstream
+    (b : Address σB) (hb : B.contract.input b.1 = false) :
+    collectorCapabilities (contract A B wire)
+        ((downstream A B wire).address b) =
+      (collectorCapabilities B.contract b).map downstreamId := by
+  letI := Program.Executor.addressEq (σ := σB)
+  letI := Program.Executor.addressEq (σ := declarations A B)
+  have haFacts := ClosureFacts.of_close A.matched.close_ok
+  have hnone :
+      (A.contract.collectors.map (mapRow (upstream A B) upstreamId)).find?
+        (fun row => decide (row.1 = (downstream A B wire).address b)) = none := by
+    apply find_outside_collector_row (upstream A B) upstreamId
+    intro row hr heq
+    exact (closureScope A B wire).defined_disjoint row.1 b
+      (haFacts.collectors_defined row hr) hb heq
+  change (((A.contract.collectors.map (mapRow (upstream A B) upstreamId) ++
+      B.contract.collectors.map (mapRow (downstream A B wire) downstreamId)).find?
+      (fun row => decide (row.1 = (downstream A B wire).address b))).map Prod.snd).getD [] =
+    (collectorCapabilities B.contract b).map downstreamId
+  rw [List.find?_append, hnone, Option.none_or,
+    find_transported_collector_row]
+  unfold collectorCapabilities
+  cases B.contract.collectors.find? (fun row => decide (row.1 = b)) <;>
+    simp [mapRow]
+
+end IndexedComponentComposition
```
