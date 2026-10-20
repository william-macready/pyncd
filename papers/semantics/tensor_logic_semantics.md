# Tensor Logic: Operational and Denotational Semantics

[Previous: Semantics introduction](README.md) | [Contents](README.md) | [Next: Part I: Background notation](tensor_logic_semantics_part_i.md)

This specification is divided into five part files and a notation reference.
For both document series and the recommended reading order, see the
[semantics introduction](README.md).

## Status and purpose

This specification defines tensor-logic syntax, denotational meaning,
reference execution, and compilation contracts. Its purpose is to provide
a coherent mathematical foundation for a Lean formalization and verified
implementation.

The intended language uses **additive contribution semantics**: separate source
statements can contribute to the same tensor coordinate. A source statement's
`=` is not, by itself, an assertion that the final tensor entry equals that
statement's contribution.

The specification separates three questions: what equations a program
defines, how those equations can be evaluated, and when a compiled execution
faithfully realizes that evaluation. A mutation order or storage convention
does not determine the source language's meaning.

### Roadmap and reading guide

The document has five parts, followed by a notation reference and bibliography:

| Part | Central question | Contents and result |
| --- | --- | --- |
| [I: Background notation](tensor_logic_semantics_part_i.md#part-i-background-notation), Sections [1](tensor_logic_semantics_part_i.md#1-numbers-finite-sets-and-functions)-[12](tensor_logic_semantics_part_i.md#12-notation-for-operational-and-proof-rules) | What mathematical objects and notation are used? | Finite domains, scalar algebras, tensor signatures, environments, stores, indices, operators, and contribution occurrences, illustrated by running examples. |
| [II: Core language and surface elaboration](tensor_logic_semantics_part_ii.md#part-ii-core-language-and-surface-elaboration), Sections [13](tensor_logic_semantics_part_ii.md#13-core-syntax-and-binding)-[17](tensor_logic_semantics_part_ii.md#17-pure-einsum-semantics-and-transformation-foundations) | What does a well-formed statement say explicitly? | Scoped core syntax, structural checks, surface-to-core translation, and the canonical pure-einsum meaning and rewrite conditions. |
| [III: Denotational semantics](tensor_logic_semantics_part_iii.md#part-iii-denotational-semantics), Sections [18](tensor_logic_semantics_part_iii.md#18-expression-interpretation-and-definedness)-[22](tensor_logic_semantics_part_iii.md#22-denotational-scope-and-execution-requirements) | What equations and values does a program define? | Strict expression interpretation, additive collection, complete program models, and a partial input-output function on inputs with a unique model. |
| [IV: Operational semantics](tensor_logic_semantics_part_iv.md#part-iv-operational-semantics), Sections [23](tensor_logic_semantics_part_iv.md#23-read-footprints-and-executable-dependencies)-[28](tensor_logic_semantics_part_iv.md#28-reference-machine-boundaries-and-proof-targets) | How can the contributions be computed safely? | Read footprints, dependency ranks, accumulation and publication rules, explicit failures, and correspondence with unique models for the ranked fragment. |
| [V: Compilation and refinement](tensor_logic_semantics_part_v.md#part-v-compilation-and-refinement), Sections [29](tensor_logic_semantics_part_v.md#29-execution-plans-and-logical-action-contracts)-[34](tensor_logic_semantics_part_v.md#34-refinement-boundaries-and-formalization-targets) | When does a compiled plan implement that meaning? | Plan contracts, buffer representations, simulation and progress obligations, batching, scan-buffer reuse, and a conditional compiler-correctness theorem. |

Read Parts [I](tensor_logic_semantics_part_i.md#part-i-background-notation) and [II](tensor_logic_semantics_part_ii.md#part-ii-core-language-and-surface-elaboration) before the formal semantics: they establish the notation
and binding conventions used throughout. [Part III](tensor_logic_semantics_part_iii.md#part-iii-denotational-semantics) applies even to cyclic
equation systems; the progress guarantees in Parts [IV](tensor_logic_semantics_part_iv.md#part-iv-operational-semantics) and [V](tensor_logic_semantics_part_v.md#part-v-compilation-and-refinement) concern the
coordinate-ranked fragment, not every structurally valid program.
The distinction between having a unique model and having a supported
execution strategy is therefore essential.

The boundary, colliding-write, activation, and finite-history examples are
revisited across the parts to connect notation, elaboration, equations,
execution, and storage. [Section 35](tensor_logic_semantics_reference.md#35-compact-notation-reference) collects the notation; the references
identify the mathematical sources and related design documents.

For the implementation path, see
[From Tensor Logic semantics to a Lean executable reference](lean_executable_semantics_path.md).
It maps this document's notation and mathematical clauses to the landed Lean
definitions and proofs, explains their category-theoretic organization, and
separates the verified admitted exact-rational reference executor and the
bounded source-correspondence layer from the remaining general-source and
backend-refinement work.

For a fully worked example of the notation, see
[Tensor Logic semantics: worked examples](tensor_logic_semantics_examples.md).
It starts with the DSL for an L-layer, ten-class classifier, makes its core
translation and dependencies explicit, and shows every contribution and
publication step of a numerical instance. Three additional worked programs
demonstrate residual contribution collection, guarded partial operations and
explicit failure, and affine scatter with collisions and empty fibers. A
Lean-focused compilation walkthrough then contrasts current full-history
lowering with an illustrative Part V two-buffer plan, including physical
layouts, retirement, certificates and simulation obligations.

### Semantics at a glance

The development rests on five ideas. [Part I](tensor_logic_semantics_part_i.md#part-i-background-notation) fixes the notation, and each
item names the section that makes it precise. The colors are explained in the
next subsection.

1. **Occurrences ([§9](tensor_logic_semantics_part_i.md#9-programs-and-contribution-occurrences), [§13](tensor_logic_semantics_part_ii.md#13-core-syntax-and-binding)).** A statement $\textcolor{#9D75C4}{s}$ generates one
   occurrence $(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})$ for each
   admissible valuation $\textcolor{#5688C7}{\nu}\in\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$.
   It is addressed to $\textcolor{#9D75C4}{\mathop{\mathrm{dst}}\nolimits}(\textcolor{#9D75C4}{o})=(T_{\textcolor{#9D75C4}{s}},\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(\textcolor{#5688C7}{\nu}))$
   and carries a body value $\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}$,
   which can be undefined ($\textcolor{#398B83}{\bot}$).
2. **Collection ([§19](tensor_logic_semantics_part_iii.md#19-contribution-collection)).** All occurrences addressed to a coordinate are
   combined, none deduplicated, and an empty fiber gives $0_K$:
   $$
   \textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)[p]
   =\bigoplus_{(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})\in\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(T,p)}
   \textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\rrbracket_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}.
   $$
3. **Meaning ([§20](tensor_logic_semantics_part_iii.md#20-program-models-and-functional-denotation)).** A model on inputs $\textcolor{#398B83}{\eta}$ is a complete
   environment that extends $\textcolor{#398B83}{\eta}$, has every actual body defined, and satisfies
   $\textcolor{#398B83}{\rho}(T)=\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)$ for every defined tensor $T$.
   The denotation $\textcolor{#398B83}{\llbracket} \textcolor{#9D75C4}{P}\textcolor{#398B83}{\rrbracket}(\textcolor{#398B83}{\eta})$ is the output part of the model when
   $\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$ has exactly one element.
4. **Execution ([§24](tensor_logic_semantics_part_iv.md#24-machine-configurations-and-initialization)–[§25](tensor_logic_semantics_part_iv.md#25-execution-rules-and-terminal-outcomes)).** A configuration $(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$ holds published values,
   accumulators, and pending occurrences. Three rules fire in any order their
   premises allow:
   $\textcolor{#A87C28}{\mathrm{CONTRIBUTE}}$ adds a pending occurrence's value to its destination's
   accumulator once every address in its read footprint is published;
   $\textcolor{#A87C28}{\mathrm{PUBLISH}}$ makes a coordinate readable once no pending occurrence
   targets it; $\textcolor{#A87C28}{\mathrm{UNDEFINED}}$ ends the run in an explicit failure when a
   ready body is undefined.
5. **Correspondence ([§26](tensor_logic_semantics_part_iv.md#26-conservation-termination-and-correspondence), [§31](tensor_logic_semantics_part_v.md#31-simulation-and-compiler-correctness)).** For programs with a coordinate rank
   certificate, every maximal run succeeds exactly when $\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$ is a
   singleton and then returns that model; otherwise it fails explicitly.
   A valid compiled plan refines this machine.

In the boundary example of [Section 11.1](tensor_logic_semantics_part_i.md#111-boundary-contributions), `T[0,c] = C[c]` and `T[r,0] = R[r]`
give the corner two occurrences, so $T[0,0]=C[0]+R[0]$. Interior coordinates
have empty fibers and receive $0$, and the corner is not readable until both
occurrences have been consumed.

### Notation color key

Color is a visual guide to a symbol's semantic role, not an additional
mathematical assumption. The same roles are used throughout the document:

| Color | Role | Representative notation | Reading cue |
| --- | --- | --- | --- |
| $\textcolor{#5688C7}{\text{Blue}}$ | Domains, signatures, and index binding | $\textcolor{#5688C7}{\Gamma},\textcolor{#5688C7}{\nu},\textcolor{#5688C7}{\Sigma},\textcolor{#5688C7}{I},\textcolor{#5688C7}{\phi}$ | Which coordinates and index assignment? |
| $\textcolor{#9D75C4}{\text{Purple}}$ | Program syntax and source identities | $\textcolor{#9D75C4}{P},\textcolor{#9D75C4}{s},\textcolor{#9D75C4}{E},\textcolor{#9D75C4}{\mathcal{O}},\textcolor{#9D75C4}{\mathrel{+}=}$ | What does the source program say? |
| $\textcolor{#398B83}{\text{Teal}}$ | Denotational values and equations | $\textcolor{#398B83}{\rho},\textcolor{#398B83}{\eta},\textcolor{#398B83}{V},\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits},\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}$ | What values and equations does it mean? |
| $\textcolor{#A87C28}{\text{Amber}}$ | Reference execution and readiness | $\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U},\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits},\textcolor{#A87C28}{\longrightarrow}$ | What is available or executable now? |
| $\textcolor{#C16C86}{\text{Rose}}$ | Compiled execution and physical representation | $\textcolor{#C16C86}{\Pi},\textcolor{#C16C86}{\mathsf{C}},\textcolor{#C16C86}{M},\textcolor{#C16C86}{\xi},\textcolor{#C16C86}{\lambda}$ | How is it scheduled and stored? |

In particular, an index valuation $\textcolor{#5688C7}{\nu}$, a complete
tensor environment $\textcolor{#398B83}{\rho}$, a published-value store
$\textcolor{#A87C28}{\sigma}$, and physical memory $\textcolor{#C16C86}{M}$
are different kinds of object. Color reinforces that distinction.
Published stores and incomplete accumulators share the execution color;
their names and definitions still distinguish them.

Mixed formulas keep each component's role rather than taking one color
as a whole. Tensor names, individual coordinates, ordinary arithmetic,
scalar algebra, and generic mathematical punctuation generally remain
neutral. Locally reused letters are colored by their stated meaning:
for example, a matrix identifier $\textcolor{#9D75C4}{M}$ is source notation, whereas physical
memory $\textcolor{#C16C86}{M}$ is a storage object. Source contribution
notation is purple even when it resembles an update; mathematical equality
remains neutral. Neither color nor source-list position specifies an
execution order.

Read this document in
VS Code's Markdown preview with the built-in `markdown.math.enabled`
setting enabled (the default), or in a browser Markdown preview supporting
KaTeX or MathJax. Plain Markdown without a math renderer displays the
source notation rather than typesetting it. GitHub also imposes a per-page
math-rendering complexity limit; this long document can exceed it even with
supported macros. Use the local preview to render the complete specification.

### Semantic scope

The specification assumes:

- Finite, explicitly determined index domains, including finite scan histories.
- A fixed scalar algebra, or a fixed family of scalar sorts ([Section 2.4](tensor_logic_semantics_part_i.md#24-scalar-sorts)), for a
  given development.
- Exact mathematical values, distinguished from machine floating-point values.
- Explicitly specified domains for primitive operators.
- Tensor names whose roles as inputs or defined tensors are distinguished.

Several distinctions apply throughout:

- A statement generates contributions; their collected totals define equations.
- A supplied input is not an implicit contribution, and an unwritten defined
  coordinate receives the empty sum on its declared domain.
- An unavailable value is not an available zero; a ready but undefined
  expression is a different case again.
- Primitive applications and constructed arrays use the strict interpretation
  in [Part III](tensor_logic_semantics_part_iii.md#part-iii-denotational-semantics). A zero multiplier is not a guard.
- Logical coordinates and published versions remain distinct even when
  physical storage is reused.

Cyclic dependencies remain permitted in the denotational language, but the
direct executor does not select solutions for cyclic equations. Out-of-range
access is outside the core: it is neither a read nor a write of an in-bounds
coordinate. A surface profile may give a read outside the shape a defined
meaning, for example the zero-extension read of the
[boundary-policy note](tensor_logic_boundary_policies.md#843-boundary-aware-gather-constructs-another-naperian-family), which
returns $0_K$ of the sort being read. Likewise implicit conversion between sorts
is defined only as an elaboration into registered primitives
([Section 2.4](tensor_logic_semantics_part_i.md#24-scalar-sorts)). Floating-point reduction order and
machine-number representations are outside the specified fragment. [Part V](tensor_logic_semantics_part_v.md#part-v-compilation-and-refinement) treats
physical storage reuse within an exact-value memory model; it does not
silently replace the scalar carrier by floating-point values.

Every lemma and theorem here carries a mathematical argument. Which of them
are also kernel-checked in Lean is recorded in
[Proof status and numbered results](#proof-status-and-numbered-results). The
[Part V](tensor_logic_semantics_part_v.md#part-v-compilation-and-refinement) compilation results Lemma 31.2, Theorem 31.3 and Lemma 32.1 are
proved for the slice-1 to slice-4 profile (singleton/fused commands by expansion,
retirement of defined published addresses, typed static same-sort buffer reuse
with boundary-local layout injectivity; see the table). Slice 4, its review fixes,
and the retirement/reuse fixture-probe closure are merged and pushed through
`e9ae73f1` (2026-10-12). That baseline has 367 fixtures
(186 evaluated rows and 181 proof items), 64 production mutation controls with
exact failure-site expectations, and 17 supplemental probes (16 computed
components and one independent `R.dead` consumer). The latter use source copies
with proved control parity: they do not admit proofs, modify production, or
establish whole mutated executor runs. The full build and standard-axiom audit
are green, and the review findings are closed. See the
[slice-4 record](plan_layer_slice4_record.md) and the
[retirement probe close-out](plan_layer_slice3_record.md#o3-reconciled-and-closed-independent-component-mutation-probes).
Slice 5 additionally proves the bounded full-history instance of
[Section 33.1](tensor_logic_semantics_part_v.md#331-a-separate-buffer-history-plan): exact schedule validity,
all-command physical preservation of published slices, unconditional completion,
and full typed history decoding for arbitrary natural bounds, including zero.
The Plan inventory is now 516 fixtures (239 evaluated rows and 277 proof items);
scan controls, review and integration evidence are separate in the
[slice-5 record](plan_layer_slice5_record.md). Automatic scan recognition,
two-buffer last-reader liveness and in-place reuse are not proved. Compiler correctness is
conditional on the stated certificates and kernel contracts; it is not a claim
that an existing compiler satisfies them.
Structural well-formedness alone establishes neither existence of a model
nor an executable dependency order.

The pure-einsum material draws on
[*The Syntax and Semantics of einsum*](https://arxiv.org/html/2509.20020).
[Section 17](tensor_logic_semantics_part_ii.md#17-pure-einsum-semantics-and-transformation-foundations) adapts it to zero-based finite domains, explicit signatures, and
tagged contributions. The paper uses one-based intervals with positive
extents; this specification permits zero extents. Correspondence arguments
must preserve that difference rather than exclude empty domains implicitly.

### Proof status and numbered results

The lemmas, propositions, theorems, and corollaries below are labeled where
they are stated. Other sections cite them by label. Labels are numbered
sequentially within each top-level section and are not subsection numbers:
"Theorem 26.5" is in [Section 26.4](tensor_logic_semantics_part_iv.md#264-finite-execution-and-progress-for-ranked-programs), and "[Section 26.3](tensor_logic_semantics_part_iv.md#263-successful-execution-gives-the-unique-model)" names a section.

| Result | Statement | Lean status (`LeanNCD.Semantics`) |
| --- | --- | --- |
| Proposition 19.1 | Pure-einsum elaboration correspondence | Proved for the bounded source fragment (read-only sums of products over bare slots, over any semiring): `Term.collectedBody_correspondence`, `AdmittedSource.collect_correspondence`, `AdmittedSource.models_iff_global` (`Source.Correspondence`, `Source.ProgramCorrespondence`). Independence from the order of nested reductions is `interpret_contract_reindex` (`Source.Lowering`): any equivalence of the bound coordinates leaves the interpreted contraction unchanged, for the generic `contract` builder over any semiring. Admission still builds reductions in declaration order, and no theorem permutes factors or terms. Actual successful raw admission now certifies original declarations and indexed occurrences through `admitRawSource_fields` and `admitRawSource_certified` (`Source.RawCorrespondence`, `Source.RawSemanticConnection`), with applicability to existing body/fiber/collection/model results. Reached rational results require an actual complete outcome, are relative to `result.input`, and expose denotation only on outputs. This is not an independent raw denotation, parser correctness, global identity-mint injectivity or input-buffer certification; affine slots, guards, marked slices and nonlinear bodies remain outside the fragment. |
| Proposition 19.2 | Source-order invariance | Proved for the bounded source fragment: the occurrence-relabeling form generically (`models_relabel`) and for source programs under any statement permutation (`StatementPermutation.models`, `.collect`, `.admEnv`, `.identities` in `Source.Permutation`). `StatementPermutation.successful_results` proves equal whole stores for two completed rational executions with equal inputs; it does not assert completion or trace equality. Open beyond the fragment and for re-admitted permuted source text. |
| Lemma 23.1 | Read stability | Proved: `evalWith_stable`, `interpret_stable` (`Readiness`). |
| Lemma 26.1 | Conservation invariants | Proved: `reachable_invariant` (`Invariants`) yields `Invariant.published` (item 4), `Invariant.consumed` (item 5), `Invariant.conservation` (accumulator formula), and `Invariant.inputs` (inputs unchanged, part of item 3), with `initial_invariant`, `consume_invariant`, `publish_invariant`. Items 1 and 2 follow from the step premises and typing (item 1 via the pending premise and `Finset.erase`). Monotone publication has only the one-step lemma `publish_extends`; the invariant does not need more. |
| Lemma 26.2 | Preservation of every candidate model | Partial. Parts (b) and (c) are `candidate_preserved` (`Soundness`), which also makes failed states incompatible with a model. For part (a), the finished-fiber case is `finished_accumulator`; the partial-fiber sum follows from `Invariant.conservation` and `Invariant.consumed` and is not stated separately in Lean. |
| Theorem 26.3 | A successful run gives the unique model; a failed run excludes every model | Proved: `successful_model`, `successful_unique`, `successful_admInput`, `successful_denotation`, `failed_no_model` (`Soundness`). Executor level: `result_model`, `result_unique`, `result_denotation`, `result_failure` (`ReferenceExecutor`). |
| Lemma 26.4 | Finite execution | Proved: `step_wellFounded`, `no_infinite_chain`, `running_trace_bound`, `failed_trace_bound` (`Measure`). Executor level: `initialBudget_agrees`, `run_not_exhausted` (`ExecutableState`, `ReferenceExecutor`). |
| Theorem 26.5 | Ranked progress | Proved: `ranked_progress`, `ranked_not_blocked` (`Progress`). Executor level: `result_not_blocked`. |
| Theorem 26.6 | Ranked correspondence | Proved: `maximal_dichotomy`, `model_maximal_success`, `no_model_maximal_failure`, `initialization_iff_singleton`, `successful_schedules_agree` (`Progress`). Executor level: `run_ranked_dichotomy`. |
| Corollary 26.7 | Ranked uniqueness | Follows from `model_maximal_success`, `maximal_extension` and `successful_unique`; no separately named theorem. |
| Lemma 31.2 | Terminal adequacy of a valid plan | Proved (slice-1 to slice-4 profile): `terminal_adequacy`, `complete_of_refState` (`Plan.Correctness`). Fused plans: `terminal_adequacy_F` (`Plan.FusionCorrectness`). Outputs remain live by `live_output_of_valid`; `Decode` follows allocation, not ghost history. |
| Theorem 31.3 | Compiled correctness | Proved (slice-1 to slice-4 profile): `done_correct`, `failed_correct`, `done_or_failed`, `done_of_model`, `done_iff_model` (`Plan.Correctness`); `runPlan_not_stuck` (`Plan.Run`). Fused plans: `done_correct_F`, `failed_correct_F`, `done_or_failed_F`, `done_of_model_F`, `done_iff_model_F`, `runPlan_not_stuck_F` (`Plan.FusionCorrectness`); per-command failure matching `step_failed_command` (`Plan.Fusion`). `Valid.layout` supplies all-boundary alias safety; exact `checkPlan_iff` and `checkPlanF_iff` remain. |
| Lemma 32.1 | Batched accumulation refines individual steps | Proved: `batch_execution`, `batch_execution_perm`, `accumulateBatch_accumulators`, `accumulateBatch_pending`, `accumulateBatch_published` (`Plan.Batch`); failure half for the transactional singleton kernel only (`step_failed`, `Plan.Simulation`). |
| Section 33.1 instance | Bounded full-history scan with retained slice buffers | Proved (slice 5, `Plan.ScanHistory`): `plan_valid`, `plan_checkPlan`, independent collected-equation model existence/uniqueness, `prefix_done_R`, `history_retained`, `history_retained_later`, unconditional `scan_done`, full typed `scan_decode_history`, and `scan_denotation_history`. Arbitrary `d,N`, `AddCommMonoid V`, registered total unary same-sort array F and every validated input; no retirement/reuse or compiler-recognition claim. |

The Lean results for Sections 23-26 concern the reference machine as a transition
relation over abstract finite carriers and primitives. Its computable refinement now
selects those same legal transitions, validates tensor-level input presence,
and retains typed event paths and exact endpoints. The verified runtime profile
uses exact rationals with reciprocal and square; successful initialized runs
give the unique whole-store model, and reached ready failures exclude models.
For the generic executor the rank certificate and complete ordered schedule
are supplied as data. The bounded source layer builds its schedule
automatically but synthesizes and checks no rank, and its admission accepts only
a bounded fragment rather than general source. No production/backend
refinement is claimed. Arbitrary debug blocking or exhaustion is not a
no-model result.

The bounded source layer admits finite read-only sums of products over bare
slots with identity-keyed valuations, and proves Propositions 19.1 and 19.2
for that fragment. Its
differential comparison of four evaluation legs (an independent exact oracle,
the rational executor, legacy evaluation, and the checked dense backend) is
executed evidence, not theorems. The original slice is validated by 79 named
fixtures and 39 mutation controls (18 proof-protected and 21 executable). The
raw-admission follow-up adds ten fixture families and 17 controls (15
proof-protected rejections and 2 fixture contrasts), recorded separately.
Its numerical profile claims exact bit agreement only for programs with
f64-declared integral values of magnitude at most $2^{20}$ and one definition
per left-hand side; it is not a floating-point semantics. Proof target 2 is
covered only at the level of identity-keyed valuations, binder freshening, and
reindexing of reduction binders; there is no substitution on expressions. See
[the Lean path document](lean_executable_semantics_path_part_4.md#47-bounded-source-correspondence-and-differential-debugging).
Items 1 and 2 of the proof targets in [Section 28](tensor_logic_semantics_part_iv.md#28-reference-machine-boundaries-and-proof-targets) (well-definedness of typed
interpretation, and renaming and substitution) are not numbered statements;
the companion document records what covers them. The table reflects
[the Lean path document](lean_executable_semantics_path.md) as of its
2026-10-10 snapshot, which is authoritative for what has landed. Update both
together.

## Table of contents

- [Status and purpose](#status-and-purpose)
  - [Roadmap and reading guide](#roadmap-and-reading-guide)
  - [Semantics at a glance](#semantics-at-a-glance)
  - [Notation color key](#notation-color-key)
  - [Semantic scope](#semantic-scope)
  - [Proof status and numbered results](#proof-status-and-numbered-results)
- [Part I: Background notation](tensor_logic_semantics_part_i.md#part-i-background-notation)
  - [1. Numbers, finite sets, and functions](tensor_logic_semantics_part_i.md#1-numbers-finite-sets-and-functions)
  - [2. Scalar algebras and finite combination](tensor_logic_semantics_part_i.md#2-scalar-algebras-and-finite-combination)
  - [3. Axes, index variables, and valuations](tensor_logic_semantics_part_i.md#3-axes-index-variables-and-valuations)
  - [4. Tensor signatures, coordinates, and values](tensor_logic_semantics_part_i.md#4-tensor-signatures-coordinates-and-values)
  - [5. Environments and stores](tensor_logic_semantics_part_i.md#5-environments-and-stores)
  - [6. Index expressions and coordinate maps](tensor_logic_semantics_part_i.md#6-index-expressions-and-coordinate-maps)
  - [7. Free indices, contraction, and broadcasting](tensor_logic_semantics_part_i.md#7-free-indices-contraction-and-broadcasting)
  - [8. Operators, predicates, and definedness](tensor_logic_semantics_part_i.md#8-operators-predicates-and-definedness)
  - [9. Programs and contribution occurrences](tensor_logic_semantics_part_i.md#9-programs-and-contribution-occurrences)
  - [10. Equality, source notation, and interpretation brackets](tensor_logic_semantics_part_i.md#10-equality-source-notation-and-interpretation-brackets)
  - [11. Running examples fixing the notation](tensor_logic_semantics_part_i.md#11-running-examples-fixing-the-notation)
  - [12. Notation for operational and proof rules](tensor_logic_semantics_part_i.md#12-notation-for-operational-and-proof-rules)
- [Part II: Core language and surface elaboration](tensor_logic_semantics_part_ii.md#part-ii-core-language-and-surface-elaboration)
  - [13. Core syntax and binding](tensor_logic_semantics_part_ii.md#13-core-syntax-and-binding)
  - [14. Structural well-formedness](tensor_logic_semantics_part_ii.md#14-structural-well-formedness)
  - [15. Surface-to-core elaboration](tensor_logic_semantics_part_ii.md#15-surface-to-core-elaboration)
  - [16. Worked core elaborations](tensor_logic_semantics_part_ii.md#16-worked-core-elaborations)
  - [17. Pure einsum semantics and transformation foundations](tensor_logic_semantics_part_ii.md#17-pure-einsum-semantics-and-transformation-foundations)
    - [17.1 Index strings and global valuations](tensor_logic_semantics_part_ii.md#171-index-strings-and-global-valuations)
    - [17.2 Canonical fiber semantics](tensor_logic_semantics_part_ii.md#172-canonical-fiber-semantics)
    - [17.3 Connection to the contribution core](tensor_logic_semantics_part_ii.md#173-connection-to-the-contribution-core)
    - [17.4 Delta tensors and diagonal identities](tensor_logic_semantics_part_ii.md#174-delta-tensors-and-diagonal-identities)
    - [17.5 Conditions for semantic transformations](tensor_logic_semantics_part_ii.md#175-conditions-for-semantic-transformations)
    - [17.6 Neutral operands and domain preservation](tensor_logic_semantics_part_ii.md#176-neutral-operands-and-domain-preservation)
- [Part III: Denotational semantics](tensor_logic_semantics_part_iii.md#part-iii-denotational-semantics)
  - [18. Expression interpretation and definedness](tensor_logic_semantics_part_iii.md#18-expression-interpretation-and-definedness)
  - [19. Contribution collection](tensor_logic_semantics_part_iii.md#19-contribution-collection)
  - [20. Program models and functional denotation](tensor_logic_semantics_part_iii.md#20-program-models-and-functional-denotation)
  - [21. Worked denotational examples](tensor_logic_semantics_part_iii.md#21-worked-denotational-examples)
  - [22. Denotational scope and execution requirements](tensor_logic_semantics_part_iii.md#22-denotational-scope-and-execution-requirements)
- [Part IV: Operational semantics](tensor_logic_semantics_part_iv.md#part-iv-operational-semantics)
  - [23. Read footprints and executable dependencies](tensor_logic_semantics_part_iv.md#23-read-footprints-and-executable-dependencies)
  - [24. Machine configurations and initialization](tensor_logic_semantics_part_iv.md#24-machine-configurations-and-initialization)
  - [25. Execution rules and terminal outcomes](tensor_logic_semantics_part_iv.md#25-execution-rules-and-terminal-outcomes)
  - [26. Conservation, termination, and correspondence](tensor_logic_semantics_part_iv.md#26-conservation-termination-and-correspondence)
  - [27. Worked operational examples](tensor_logic_semantics_part_iv.md#27-worked-operational-examples)
  - [28. Reference-machine boundaries and proof targets](tensor_logic_semantics_part_iv.md#28-reference-machine-boundaries-and-proof-targets)
- [Part V: Compilation and refinement](tensor_logic_semantics_part_v.md#part-v-compilation-and-refinement)
  - [29. Execution plans and logical action contracts](tensor_logic_semantics_part_v.md#29-execution-plans-and-logical-action-contracts)
  - [30. Concrete states and logical representation](tensor_logic_semantics_part_v.md#30-concrete-states-and-logical-representation)
  - [31. Simulation and compiler correctness](tensor_logic_semantics_part_v.md#31-simulation-and-compiler-correctness)
  - [32. Batched collection and array kernels](tensor_logic_semantics_part_v.md#32-batched-collection-and-array-kernels)
  - [33. Scan compilation and buffer reuse](tensor_logic_semantics_part_v.md#33-scan-compilation-and-buffer-reuse)
  - [34. Refinement boundaries and formalization targets](tensor_logic_semantics_part_v.md#34-refinement-boundaries-and-formalization-targets)
- [35. Compact notation reference](tensor_logic_semantics_reference.md#35-compact-notation-reference)
- [References and related documents](tensor_logic_semantics_reference.md#references-and-related-documents)

---

[Previous: Semantics introduction](README.md) | [Contents](README.md) | [Next: Part I: Background notation](tensor_logic_semantics_part_i.md)
