# Lean executable reference - 4. What is implemented and proved

[Previous: 3. The category-theoretic organization](lean_executable_semantics_path_part_3.md) | [Contents](README.md) | [Next: 5. Remaining work, in dependency order](lean_executable_semantics_path_part_5.md)

## In this part

- [4. What is implemented and proved](#4-what-is-implemented-and-proved)
  - [4.1 Strict expressions and stable ready evaluation](#41-strict-expressions-and-stable-ready-evaluation)
  - [4.2 Occurrences, collection, and models](#42-occurrences-collection-and-models)
  - [4.3 Reference transitions and conservation](#43-reference-transitions-and-conservation)
  - [4.4 What reached-run soundness establishes](#44-what-reached-run-soundness-establishes)
  - [4.5 Coordinate ranks, finite termination, and correspondence](#45-coordinate-ranks-finite-termination-and-correspondence)
  - [4.6 The computable reference executor](#46-the-computable-reference-executor)
  - [4.7 Bounded source correspondence and differential debugging](#47-bounded-source-correspondence-and-differential-debugging)
  - [4.8 Existing validation and its limits](#48-existing-validation-and-its-limits)
  - [4.9 Part V slice 1: the singleton-command plan layer](#49-part-v-slice-1-the-singleton-command-plan-layer)

## 4. What is implemented and proved

### 4.1 Strict expressions and stable ready evaluation

The constructors map directly to
[Sections 18.2-18.4](tensor_logic_semantics_part_iii.md#182-scalar-constructors):

| Core expression | Lean constructor and interpretation |
| --- | --- |
| $c_K$, $T[\textcolor{#9D75C4}{e}_1,\ldots,\textcolor{#9D75C4}{e}_k]$, $\mathbf 1_{\textcolor{#9D75C4}{Q}}$ | `Expr.lit`, `.read`, `.iverson` |
| $\textcolor{#9D75C4}{E}_1\oplus \textcolor{#9D75C4}{E}_2$, $\textcolor{#9D75C4}{E}_1\otimes \textcolor{#9D75C4}{E}_2$ | `.binary .add`, `.binary .mul`; both results must succeed |
| $\bigoplus_{j\in[n]}\textcolor{#9D75C4}{E}$ | `.reduce n body`; ordered `foldValues` over `List.finRange n` |
| $\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits}_{\textcolor{#5688C7}{J}}(\textcolor{#9D75C4}{E})$ | `.tab sh layout body`; `sequence` assembles a complete function array |
| $\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}(\textcolor{#9D75C4}{E},p)$ | `.at e index`; first obtain the complete array value |
| $f(\textcolor{#9D75C4}{E}_1,\ldots,\textcolor{#9D75C4}{E}_q)$ | `.prim f args`; assemble all arguments, then `Registry.apply` checks the domain |

The correspondence is more than constructor naming.
[`Completeness.lean`](../../leanncd/LeanNCD/Semantics/Completeness.lean)
proves `sequence_some_iff`, `tab_complete`, `reduce_defined_iff`,
`reduce_empty`, `at_some_iff`, and `prim_some_iff`: these state the successful
result conditions of the mathematical clauses.

Algebraic hypotheses are deliberately local. `ScalarOps` contains operations
as data and imposes no semiring laws. `interpret_reduce_sum` identifies the
ordered reduction with $\bigoplus$ when the selected carrier has
`AddCommMonoid` and the supplied `zero` and `add` equal its identity and
addition. It does not assume those equalities for every carrier.

For [Section 23.3](tensor_logic_semantics_part_iv.md#233-stable-evaluation-from-a-partial-store),
[`Readiness.lean`](../../leanncd/LeanNCD/Semantics/Readiness.lean) proves:

```math
\textcolor{#398B83}{\rho}|_{\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})}
=\textcolor{#398B83}{\rho}'|_{\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})}
\Longrightarrow
\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}
=\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho}',\textcolor{#5688C7}{\nu}}
\qquad\texttt{interpret\_stable}.
```

`evalWith_stable` is the analogous partial-store theorem.
`checkReads_iff` validates the Boolean readiness check, and `ready_consistent`
equates ready evaluation with interpretation in an agreeing complete
environment. Its stronger whole-store use is `evaluated_consistent` in
[`Invariants.lean`](../../leanncd/LeanNCD/Semantics/Invariants.lean).

Use the three cases of `evalReady`:

```text
.notReady                 footprint unavailable: wait
.evaluated (some v)       ready, defined value v
.evaluated none           ready, undefined result bot
```

The low-level `evalWith` returns only `Option`; its `none` alone cannot
classify waiting versus undefinedness. A mathematical complete-extension
witness in `ready_complete_extension` is not a zero-fill runtime fallback.
Whole-array footprints and both strict operands remain required even when
one entry is selected or another operand is zero.

### 4.2 Occurrences, collection, and models

[`Program.lean`](../../leanncd/LeanNCD/Semantics/Program.lean) presents
[Sections 9 and 19](tensor_logic_semantics_part_i.md#9-programs-and-contribution-occurrences)
using local statement tags for each defined tensor. For a fixed target $T$
and $\textcolor{#398B83}{\rho}\in\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})$, define:

```math
\textcolor{#9D75C4}{O}_T=\coprod_{\substack{\textcolor{#9D75C4}{s}\in \textcolor{#9D75C4}{P}\\T_{\textcolor{#9D75C4}{s}}=T}}\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}},
\qquad
\textcolor{#5688C7}{d}_T(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})=\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}(\textcolor{#5688C7}{\nu}),
\qquad
\textcolor{#398B83}{v}^{\textcolor{#398B83}{\rho}}_T(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})=\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}.
```

`P.Occurrence t` is the dependent pair of a statement `Fin` tag and a
guard-admitted valuation subtype. The mathematical global $\textcolor{#9D75C4}{\mathcal O}_{\textcolor{#9D75C4}{P}}$
is correspondingly the disjoint union of these families over defined
tensors. Guards exclude valuations before body demand.

| Mathematics | Lean |
| --- | --- |
| $\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$ | `{v : Fin (P.valuations t s) // P.guard t s v = true}` |
| $\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}$, $\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}$ | `P.destination t s`, `P.body t s` |
| $\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}$ | `P.outcome ops ρ t o` |
| $\textcolor{#398B83}{\rho}\in\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})$ | `P.AdmEnv ops ρ` |
| Successful value $\textcolor{#398B83}{v}^{\textcolor{#398B83}{\rho}}_T(\textcolor{#9D75C4}{o})$ | `P.contribution ops ρ h t o`, extracted using admission proof `h` |
| $\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)=\textcolor{#5688C7}{d}_{T!}(\textcolor{#398B83}{v}^{\textcolor{#398B83}{\rho}}_T)$ | `P.collect ops ρ h t`, directly defined using `pushforward` |

This last equality is the actual organizing implementation, not a categorical
analogy attached to an imperative collector. `collect_grouped` and
`collect_relabel` transfer the generic laws to program collection.

[`Models.lean`](../../leanncd/LeanNCD/Semantics/Models.lean) expresses
[Section 20](tensor_logic_semantics_part_iii.md#20-program-models-and-functional-denotation):

```math
\textcolor{#398B83}{\rho}\in\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})
\iff
\textcolor{#398B83}{\rho}\in\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})
\ \land\ \textcolor{#398B83}{\rho}|_{\textcolor{#5688C7}{\mathrm{In}}}=\textcolor{#398B83}{\eta}
\ \land\
\forall T\in\textcolor{#5688C7}{\mathrm{Def}},p,\
\textcolor{#398B83}{\rho}(T)[p]=\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})(T)[p].
```

The Lean predicate is `P.Models ops η ρ`.
`ValidInput` requires tensor-level presence exactly for input tensors,
including empty inputs. `InputAgreement` supplies the middle conjunct;
the final conjunct quantifies over all defined tensors, including nonoutputs.
No prior candidate value is a collection seed.

`models_fixedpoint` identifies these equations with a fixed point of
`equationOperator` on its admitted domain. This operator neither specifies
iteration nor guarantees its result remains admitted.
`models_relabel` and `models_grouped` preserve the model relation.

`AdmInput` is $\exists!\textcolor{#398B83}{\rho},\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$.
`denotation` is the unique model's `outputProjection`, using
`Classical.choose`; `denotation_of_model` proves agreement with any supplied
model under the uniqueness premise. A unique output projection alone is
not enough.

### 4.3 Reference transitions and conservation

[`Machine.lean`](../../leanncd/LeanNCD/Semantics/Machine.lean) is the direct
presentation of
[Sections 24-25](tensor_logic_semantics_part_iv.md#24-machine-configurations-and-initialization):

| Specification | Lean |
| --- | --- |
| $(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$ | `Running.published`, `.accumulators`, `.pending` |
| $\textcolor{#A87C28}{\mathop{\mathrm{Init}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$ | `P.initial η`: supplied inputs, zero accumulators, all admitted tags pending |
| $\textcolor{#A87C28}{U}\cap\textcolor{#9D75C4}{\mathcal C}_{\textcolor{#9D75C4}{P}}(T,p)=\varnothing$ | `P.FiberEmpty c t p` |
| $\textcolor{#A87C28}{\mathrm{CONTRIBUTE}}$ | `Step.contribute`: selected tag pending, `.evaluated (some v)`; add at its destination and erase that tag |
| $\textcolor{#A87C28}{\mathrm{PUBLISH}}$ | `Step.publication`: unpublished defined coordinate, empty pending fiber; publish its retained accumulator |
| $\textcolor{#A87C28}{\mathrm{UNDEFINED}}$ | `Step.undefined`: selected tag pending, `.evaluated none`; enter `.failed t o c` with the unchanged snapshot |
| $\textcolor{#A87C28}{\longrightarrow}^*$ | `P.Reaches ops` |
| Complete / successful / blocked | `P.Complete`, `P.Successful ops η`, `P.Blocked ops` |
| Complete $\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}$ | `P.finalStore c complete` |

`pending` is a family of finite sets, one per defined tensor, equivalent to
the global tagged pending set. Zero-valued contributions still erase their
tag. Empty fibers publish available zero explicitly. Accumulators are not
readable before publication; published coordinates cannot be overwritten.
Completion requires every declared address and every occurrence, not only
the designated outputs. `failed_terminal` proves failure has no outgoing step.

For [Section 26.1](tensor_logic_semantics_part_iv.md#261-basic-conservation-invariants),
`Invariant` in
[`Invariants.lean`](../../leanncd/LeanNCD/Semantics/Invariants.lean) retains
proof-only consumed values $\textcolor{#398B83}{v}_{\textcolor{#9D75C4}{o}}$ and states

```math
\textcolor{#A87C28}{\alpha}(T,p)=
\bigoplus_{\textcolor{#9D75C4}{o}\in\textcolor{#9D75C4}{\mathcal C}_{\textcolor{#9D75C4}{P}}(T,p)\setminus \textcolor{#A87C28}{U}}\textcolor{#398B83}{v}_{\textcolor{#9D75C4}{o}}.
```

This is `conservation` via `spent`. `inputs` preserves supplied inputs;
`published` states that each published defined fiber is exhausted and its
value equals its accumulator. `consumed` says every consumed body still
interprets to its recorded value in every complete environment agreeing
with published cells.

`StateInvariant` existentially hides the history; it is not an extra runtime
field or an obligation for a caller to supply a model witness.
`reachable_invariant` proves it for every reached running or failed state.

### 4.4 What reached-run soundness establishes

[`Soundness.lean`](../../leanncd/LeanNCD/Semantics/Soundness.lean) proves the
central implications in
[Sections 26.2-26.3](tensor_logic_semantics_part_iv.md#262-preservation-of-every-candidate-model):

| Theorem | Mathematical conclusion |
| --- | --- |
| `candidate_preserved` | Every candidate model agrees with every reached published store; a reached failed state is incompatible with that model |
| `successful_model` | Reached completion constructs $\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}\in\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$ |
| `successful_unique` | Every model equals that complete $\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}$ |
| `successful_admInput` | Reached success proves $\textcolor{#398B83}{\eta}\in\textcolor{#398B83}{\mathop{\mathrm{AdmInput}}\nolimits}(\textcolor{#9D75C4}{P})$ |
| `successful_denotation` | $\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{P}\textcolor{#398B83}{\mathclose{]\!]}}(\textcolor{#398B83}{\eta})=\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}\vert_{\textcolor{#5688C7}{\mathrm{Out}}}$ |
| `failed_no_model` | Reached ready-undefined failure implies $\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\varnothing$ |

No rank certificate, pre-existing model, or semiring multiplication law is
required for these results. Collection and conservation need
`AddCommMonoid` only on participating defined carriers; body operations
remain explicit data.

The converse for coordinate-ranked programs is now proved in
[Section 4.5](#45-coordinate-ranks-finite-termination-and-correspondence).
Blocking is still not undefinedness and does not exclude a model.
In particular, unique-model existence for an unranked cyclic program does
not establish executability by this machine.

### 4.5 Coordinate ranks, finite termination, and correspondence

The [coordinate-ranks/finite-measure plan](coordinate_ranks_finite_measure_plan.md)
is complete and merged, as recorded in its
[execution record](coordinate_ranks_finite_measure_execution_record.md).
The landed definitions and proofs cover
[Section 23.4](tensor_logic_semantics_part_iv.md#234-coordinate-dependencies-and-the-ranked-fragment)
and [Section 26.4](tensor_logic_semantics_part_iv.md#264-finite-execution-and-progress-for-ranked-programs).

[`Ranks.lean`](../../leanncd/LeanNCD/Semantics/Ranks.lean) derives dependencies
from the existing footprints:

```math
\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a)=
\bigcup_{\textcolor{#9D75C4}{o}\in\textcolor{#9D75C4}{\mathcal C}_{\textcolor{#9D75C4}{P}}(a)}\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{o}),
\qquad
b\in\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a)\Longrightarrow r(b)<r(a).
```

`P.dependencies a` uses guard-admitted occurrences in the exact destination
fiber; `input_dependencies_empty` excludes dependencies at input addresses.
`P.RankCertificate` supplies `rank : Address σ -> Nat` and its strict
`decreases` proof. Dependencies are on **coordinates**, not tensor names:
different history cells of the same tensor can have increasing ranks.
All strict operand, binder, and whole-array reads remain in the footprint.
Rank is independent of input values and certifies readiness, not membership
in primitive domains. This is a supplied certificate, not rank synthesis,
a source rank checker, or a proved equivalence with graph acyclicity.

[`Measure.lean`](../../leanncd/LeanNCD/Semantics/Measure.lean) defines
`pendingCount`, `unpublishedCount`, and their sum `measure`:

```math
\textcolor{#A87C28}{\mu}(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})
=|\textcolor{#A87C28}{U}|+
|\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}\setminus\mathop{\mathrm{dom}}\nolimits(\textcolor{#A87C28}{\sigma})|.
```

`DefinedAddress` includes every defined coordinate, including nonoutputs.
`initial_measure` proves that initially
$\textcolor{#A87C28}{\mu}=|\textcolor{#9D75C4}{\mathcal O}_{\textcolor{#9D75C4}{P}}|+|\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}|$.
`consume_measure`, `publish_measure`, and `running_step_measure` prove
exact decreases by one, including zero-valued consumption and empty-fiber
publication. `stateMeasure` is $\mu+1$ for running states and zero for failed
states, so `step_decreases` also covers the terminal undefined step.

| Finite-execution theorem in [Measure](../../leanncd/LeanNCD/Semantics/Measure.lean) | Conclusion |
| --- | --- |
| `step_wellFounded`, `no_infinite_chain` | No infinite chain of legal transitions; no rank or model premise |
| `running_trace_bound` | A trace ending in a running state has at most its starting $\mu$ transitions |
| `failed_trace_bound` | A trace ending in failure has at most its starting $\mu+1$ transitions |

`Trace` is a length-indexed proposition, not an executable trace container.
Failure retains the last running snapshot; it is terminal, not another
running-state measure decrease.

[`Progress.lean`](../../leanncd/LeanNCD/Semantics/Progress.lean) uses the
reachable invariant and a minimum-rank unpublished defined coordinate.
A pending tag in its fiber is ready, enabling contribution or undefinedness;
an exhausted fiber enables publication. No pre-existing model is required.
`Terminal` means no outgoing step; `Maximal` means reached from initialization
and terminal, not an arbitrary finite prefix stopped by a scheduler.

| Correspondence theorem in [Progress](../../leanncd/LeanNCD/Semantics/Progress.lean) | Conclusion |
| --- | --- |
| `ranked_progress`, `ranked_not_blocked` | Every reached noncomplete ranked running state has a step and cannot block |
| `terminal_extension`, `maximal_extension` | Every state has a terminal extension; every reached prefix extends to a maximal endpoint, without rank |
| `maximal_dichotomy` | Every maximal ranked run succeeds or explicitly fails; failure excludes all models |
| `model_maximal_success` | If a model exists, every maximal ranked run succeeds with that unique complete model |
| `no_model_maximal_failure` | If no model exists, every maximal ranked run fails |
| `initialization_iff_singleton` | Initialization reaches a successful complete store exactly when `Models` is its singleton |
| `successful_schedules_agree` | Successful runs yield the same complete environment, even without rank |

Together with existing soundness, the landed correspondence is

```math
\textcolor{#A87C28}{\mathop{\mathrm{Init}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})\textcolor{#A87C28}{\Downarrow}\textcolor{#398B83}{\rho}
\quad\Longleftrightarrow\quad
\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\{\textcolor{#398B83}{\rho}\}
\qquad\text{for the coordinate-ranked fragment}.
```

Here $\Downarrow$ asserts existence of a reached successful state with complete
store $\rho$, not evaluation by a Lean driver. Denotation agreement reuses
`successful_denotation`; it is not a new equation solver. Failing schedules
may still identify different first undefined occurrences.

### 4.6 The computable reference executor

The executor refines the transition relation of [Section 4.3](#43-reference-transitions-and-conservation)
without redefining it. It lives in
[`ExecutableState`](../../leanncd/LeanNCD/Semantics/ExecutableState.lean),
[`ExecutableSelection`](../../leanncd/LeanNCD/Semantics/ExecutableSelection.lean),
[`ReferenceExecutor`](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean), and the
closed exact-rational profile
[`RationalReference`](../../leanncd/LeanNCD/Semantics/RationalReference.lean).
The first part below describes its definitions and supplied inputs. The
tables then map the specification's
[Part IV](tensor_logic_semantics_part_iv.md#part-iv-operational-semantics) clauses and
results to them, and the last two parts cover the runtime fixtures and the
limits of the claim.

#### Definitions and supplied inputs

The executor implements the existing relation rather than redefining it:

1. [ExecutableState](../../leanncd/LeanNCD/Semantics/ExecutableState.lean)
   supplies computational equality, canonical finite presentations, updates
   proved equal to `Program.consume` and `Program.publish`, and a budget proved
   equal to the initial `stateMeasure`. Stores remain functions on dependent
   coordinates. Only defined carriers need `AddCommMonoid`.
2. [ExecutableSelection](../../leanncd/LeanNCD/Semantics/ExecutableSelection.lean)
   checks pending membership, strict `evalReady`, and the exact publication
   barrier. `select_none_iff` proves that no selection means no existing legal
   `Step`, not merely that selected steps are sound. Selection restarts at the
   first supplied key after each event; there is no global contribution-first
   policy.
3. [ReferenceExecutor](../../leanncd/LeanNCD/Semantics/ReferenceExecutor.lean)
   validates tensor-level input presence before initialization, including empty
   tensors, and returns the first offending tensor in the supplied order.
   `run` uses the proved sufficient budget. `runFuel` is a debug API that
   classifies failed, complete, and blocked endpoints before testing fuel for an
   eligible move. Exhaustion is neither success nor a no-model result.
4. Typed events retain statement/valuation identities, destinations, and
   contribution/publication payloads. Failed outcomes retain the exact
   pre-failure snapshot. `Result.execution` certifies the event path.
   Blocked outcomes carry unavailable
   read observations with actual missing addresses; `observations` also exposes
   ready `Option` values. The trace is not a log of every scan/readiness check.

`Schedule` is supplied data with kernel-checked duplicate-freedom and complete
coverage of tensors, occurrences, and all defined publication coordinates.
Computational tensor equality and the program's finite tensor presentation are
also supplied. Coordinate ranks remain proof data, not a synthesized or runtime
checked certificate. Reachable ranked blocking is excluded without a model
premise. Unranked blocking is not undefinedness and does not exclude models.

[RationalReference](../../leanncd/LeanNCD/Semantics/RationalReference.lean)
offers the closed `Unit`-sort exact-rational profile: zero, one, addition,
multiplication, reciprocal with nonzero domain, and square. There is no
unsupported-operation translation or native-registry fallback. Exact-real
transcendentals and native floating-point execution remain separate work.

#### Correspondence to the specification

| Specification clause | Lean | What it fixes |
| --- | --- | --- |
| [Section 24.2](tensor_logic_semantics_part_iv.md#242-initial-configuration): validate inputs before initialization | `validate`, `validate_accepts`, `validate_preserves`, `validate_error`, `runValidated`, `runValidated_error` | Every tensor's presence must match its role: an absent input, or a supplied defined tensor, is rejected rather than zero-filled, and an empty input must still be present. The first offender in the supplied tensor order is returned. Coordinate shapes are enforced by dependent types, not checked at runtime. |
| [Sections 25.1-25.3](tensor_logic_semantics_part_iv.md#25-execution-rules-and-terminal-outcomes): CONTRIBUTE, PUBLISH, UNDEFINED | `Event`, `Event.Legal`, `Event.effect`, `Event.legal_step` | The three constructors are the three rules. `Event.Legal` restates their premises (pending tag and ready value; unpublished address and empty pending fiber; ready undefined body). An `undefined` event reaches `failed t o c`, which keeps the exact pre-failure snapshot `c`. |
| Updates in Sections 25.1-25.2 | `consume`, `publish`, `consume_agrees`, `publish_agrees` | The computational updates equal the noncomputable `Program.consume` and `Program.publish`. |
| [Section 23.3](tensor_logic_semantics_part_iv.md#233-stable-evaluation-from-a-partial-store): waiting is not a ready $\bot$; rules fire in any order | `attempt`, `scan`, `select`, `Schedule` | An attempt is empty when the occurrence is not pending, is not ready, or its publication barrier is unmet. A ready undefined body is an `undefined` event, never a skip. The schedule is a priority order only; selection restarts at its first key after every event, so reversing it changes priority, not the set of eligible edges. |
| [Section 25.4](tensor_logic_semantics_part_iv.md#254-completion-and-dependency-blocking): complete and blocked | `completeDecidable`, `fiberDecidable`, `select_none_iff`, `Outcome` | Selection returns nothing exactly when no legal `Step` exists. A noncomplete state with no selection is `blocked`; it is neither success nor an undefined-operation failure. |
| Section 23.3: available and missing addresses | `observations`, `Observation` | For each pending occurrence, either the actual missing footprint addresses or its ready `Option` value. This inspects the current state; it is not a log of every scan. |
| [Lemma 26.4](tensor_logic_semantics_part_iv.md#264-finite-execution-and-progress-for-ranked-programs): the finite measure | `initialBudget`, `initialBudget_agrees`, `runFuel_not_exhausted`, `run_not_exhausted` | The default budget equals the initial `stateMeasure`, which is $\mu+1$ on running states. Any fuel at least the current measure suffices, so the default run is never exhausted. |

#### Theorems

The executor's theorems are the following. Each reuses the soundness and
progress results of Sections 4.4 and 4.5; none is a new equation solver.

| Theorem | Mathematical conclusion | Spec result |
| --- | --- | --- |
| `Event.legal_step` | Every selected event is a legal `Step` | Sections 25.1-25.3 |
| `select_none_iff` | Selection is empty exactly when there is no legal `Step`: completeness as well as soundness of the selector | Section 25.4 |
| `Execution.reaches` | The typed event path forgets to the existing `Reaches` relation | Section 25 |
| `run_not_exhausted` | The default run never ends in debug exhaustion | Lemma 26.4 |
| `result_success`, `result_model`, `result_unique`, `result_denotation` | A complete outcome of a run from initialization is `Successful`; its whole-store environment is the unique model and the denotation agrees | Theorem 26.3 |
| `result_failure` | A failed outcome of a run from initialization implies $\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\varnothing$ | Theorem 26.3 |
| `result_not_blocked` | Given a `RankCertificate`, a run from initialization does not end blocked | Theorem 26.5 |
| `run_ranked_dichotomy` | Given a `RankCertificate`, the default run is complete, or failed with no model | Theorem 26.6 |

#### Fixtures and controls

The 22 actual executor assertions cover admitted examples from
[Sections 21](tensor_logic_semantics_part_iii.md#21-worked-denotational-examples)
and [27](tensor_logic_semantics_part_iv.md#27-worked-operational-examples) within this
profile, not every example or source construct. Two statements times two
valuations retain all four tags and collect `2 + 2 + 5 + 5 = 14` at one
destination. Literal full-store equations and reversed schedules agree on
`[0,14,0]`. Reciprocal before collection gives `3/4`, whereas reciprocal after
addition gives `1/6`; square at `3` gives `9`. Neither independent candidate is
supplied to the executor to justify progress or success.

The default budget for the tagged fixture is `8`; supplied fuel `6` exhausts,
`7`, `8`, and `9` complete, and `0` exhausts only when an eligible move remains.
Already complete or failed endpoints retain their terminal class at zero fuel.
Other assertions separate missing addresses from destinations, unavailable
reads from ready undefinedness, input presence from coordinate presence, and
internal nonoutput failure from output completion.

The 19 mutation controls, their classification, and their limits are summarized
in [Section 4.8](#48-existing-validation-and-its-limits); the receipts are in
the [execution record](computable_reference_executor_record.md#8-implementation-execution-2026-10-08).
Existing generic soundness supplies uniqueness and denotation agreement;
checking a literal candidate or computing collection alone is not an equation
solver.

#### What this does not claim

- **No general synthesis or rank checking.** The generic `Schedule` carries
  kernel-checked duplicate-freedom and coverage supplied by its caller. The
  bounded source layer computes that schedule, but does not synthesize or
  runtime-check address ranks.
- **No no-model claim outside initialization.** `runFuel` on an arbitrary state,
  blocked endpoints, and exhausted endpoints say nothing about whether a model
  exists. Blocking is not undefinedness.
- **No schedule independence beyond whole stores.** Successful schedules agree
  on the complete environment; failure selection, diagnostics, and event traces
  may differ.
- **No dense/backend representation claims.** Stores remain function-valued.
  The separate bounded source layer adds correspondence and scalar diagnostic
  rendering, not physical-storage simulation. The Part V slice-1 to slice-4 plan layer
  ([Section 4.9](#49-part-v-slice-1-the-singleton-command-plan-layer)) adds allocation-indexed
  simulation for singleton/fused commands, retirement and static same-sort reuse;
  general backend refinement remains open.
- **A parked runtime gap.** The generic executor retains heterogeneous carriers,
  but the runtime fixtures do not cover heterogeneous non-additive inputs.

### 4.7 Bounded source correspondence and differential debugging

The `LeanNCD.Semantics.Source` layer ([Source.lean](../../leanncd/LeanNCD/Semantics/Source.lean)
and the modules under [`Source/`](../../leanncd/LeanNCD/Semantics/Source/)) connects named, identity-keyed
source statements to the core of Sections 4.1-4.6, and compares executions of
the same program. It is the first slice of the source work in
[Section 5](lean_executable_semantics_path_part_5.md#5-remaining-work-in-dependency-order), not the general source
language.

**Fragment.** A statement is `Y[bare slots] = Σ_terms Π_factors A[bare slots]`:
finite, read-only, scalar, with sum aggregation and no nonlinearity. Every
output and read slot is a bare variable over a declared axis with a pinned size.
Repeated slots are allowed. Tensor roles and input buffers are supplied
explicitly, and every input, including unused and empty ones, needs a buffer.
Admission refuses everything else, and refuses the whole program if any
statement is refused: affine and constant indices, guards (there is no syntax),
Iverson and unary factors, scatter, scans, marked output slots, non-sum
aggregation, predicates, complex types, and writes to input tensors. The
generic theorems hold over any `Semiring`, not necessarily commutative. Results
about runs hold over ℚ through the rational profile of Section 4.6.
This paragraph describes the default entry `admitSource`. A second entry,
`admitSourceAffine` (S2a, landed, merge 7a551faa), also admits integer-affine and constant LEFT-hand slots and sum-only scatter; affine READ
slots, guards and the other refusals above stay refused, and the raw-parse chain
(`RawCorrespondence`, `RawSemanticConnection`) is not extended to affine statements.
A third entry, `admitSourceSorted` (S2b, merge pending), runs the affine entry with a `sorted` flag that admits
`max`/`min` statements as their sort-free structure, selects one carrier for the whole program (a mix is refused
as `sortSelection`) and still refuses tropical scatter; `admitSource` and `admitSourceAffine` with their default
flag still refuse `max`/`min` (`nonSum`).

#### Binding and admission

| Specification clause | Lean | What it fixes |
| --- | --- | --- |
| [Sections 3.2-3.3](tensor_logic_semantics_part_i.md#32-index-variables-and-contexts): variables are identities, order is irrelevant | [`Context`](../../leanncd/LeanNCD/Semantics/Source/Context.lean), `UIDVal`, `uidCoordEquiv`, `Ref.sameUID_lookup`, `UIDTransport`, `reenumerateTransport` | A valuation is a dependent function keyed by axis identity, equivalent to ordered coordinates. Two refs with the same identity read the same value, which gives diagonals. A domain-preserving bijection of identities, or any reordering of the axis list, transports valuations and lookups. |
| [Section 13.4](tensor_logic_semantics_part_ii.md#134-scope-freshness-and-substitution): freshness and renaming | `BinderScope`, `renameBinders_noCapture`, `requestedBinders_*`, `indexPullback_id`, `indexPullback_comp`, `indexPullback_repeated` | Generated identities land outside the support; everything else is fixed. Pullback along an index map is contravariant, and a non-injective map yields equal coordinates. A requested renaming applies only when injective and fresh; otherwise every generated identity falls back to the default freshening. There is no substitution $E[i:=e]$, and admission never renames. |
| [Section 15.1](tensor_logic_semantics_part_ii.md#151-explicit-inputs-to-elaboration): resolution | `resolveRef` ([Context](../../leanncd/LeanNCD/Semantics/Source/Context.lean)), `resolveSourceSlots` ([Admission](../../leanncd/LeanNCD/Semantics/Source/Admission.lean)), `adaptSource`, `UnsupportedSource` ([Adapter](../../leanncd/LeanNCD/Semantics/Source/Adapter.lean)) | Slots resolve by identity and must match the declared extent exactly. Refusals are typed (unbound, domain, rank, and the unsupported forms above). Roles come from explicit specs, not names. |
| Raw source to admitted occurrences | `admitRawSource_fields` ([RawCorrespondence](../../leanncd/LeanNCD/Semantics/Source/RawCorrespondence.lean)), `admitRawSource_certified` ([RawSemanticConnection](../../leanncd/LeanNCD/Semantics/Source/RawSemanticConnection.lean)) | Actual admission success certifies name-keyed resolver memo coverage, ordered pinned domains, original declaration indices and specs, and pointwise raw statement/term/factor/slot links. Names, metadata, order, repeated occurrences and empty sums/products are retained; raw coordinate witnesses use the actual memo lookup at the same slot position. |
| [Section 15.2](tensor_logic_semantics_part_ii.md#152-statement-variables-and-term-local-contraction): term-local contraction | `SupportPartition`, `admitTerm`, `interpret_product`, `interpret_contract` ([Admission](../../leanncd/LeanNCD/Semantics/Source/Admission.lean), [Lowering](../../leanncd/LeanNCD/Semantics/Source/Lowering.lean)) | The contracted variables of a term are its read identities not in the output, in declaration order, with a coverage and disjointness proof. A body is a nested sum of products. |
| [Section 14.3](tensor_logic_semantics_part_ii.md#143-statement-and-program-rules): statement conditions | `admitStatement`, `admitOutput` | Conditions 1 and 3 are checked (writable target, arity). Conditions 4 and 5 hold by construction because extents match exactly. Condition 2 holds by construction for output indices, which are scoped by the output identities; its guard part is vacuous since guards have no syntax. |
| [Sections 13.6 and 15.5](tensor_logic_semantics_part_ii.md#136-core-programs): programs keep every occurrence | `AdmittedSource.program`, `program_*`, `IdentifiedSource`, `originalLocalEquiv`, `occurrenceIdentity` ([Program](../../leanncd/LeanNCD/Semantics/Source/Program.lean), [Provenance](../../leanncd/LeanNCD/Semantics/Source/Provenance.lean)) | A defined tensor collects every statement that targets it, in source order, with no merging. Original statement identities are retained and are in bijection with the program's occurrence tags. |

Several choices sharpen the specification:

- **Slot compatibility is by extent.** The variable's identity is never compared
  with the identity of the axis a tensor slot was declared over, which is
  consistent with the statement in Section 14.2 that the core judgments see
  only coordinate ranges.
- **Admission is stricter than the core read rule.** Prefix reads, which
  Section 14.2 allows, are refused; "in bounds" means exact extent equality.
- **The fragment exceeds the standard pure-einsum profile.** Broadcast terms
  (an output variable no read uses), empty products, empty term lists, and
  sums of several terms are admitted. Section 15.1 excludes these from the
  standard profile, which is a single product.
- **Open choices are fixed.** The statement context follows the order in which
  output identities first occur, contraction follows declaration order, and
  freshening offsets by a base outside the support.
- **Bodies are right-nested with trailing units**, for example
  `t₁ ⊕ (t₂ ⊕ 0)` and `r₁ ⊗ (r₂ ⊗ 1)`. This equals the specification's body in a
  semiring but is not bitwise identical in IEEE arithmetic.

#### Pure-einsum correspondence and collection

| Specification clause | Lean | What it fixes |
| --- | --- | --- |
| [Section 17.1](tensor_logic_semantics_part_ii.md#171-index-strings-and-global-valuations): $\Gamma_{\mathrm{all}}$ | `Term.globalContext`, `Term.pure_globalContext` ([Fiber](../../leanncd/LeanNCD/Semantics/Source/Fiber.lean)) | A term's global context is its read identities plus its output identities; for a pure term it is exactly its read identities. |
| [Section 17.2](tensor_logic_semantics_part_ii.md#172-canonical-fiber-semantics): canonical fiber | `globalProduct`, `globalFiber`, `globalFiber_reenumerate` | The ordered product of the original reads, summed over global valuations whose output projection is the coordinate. Factor order and repeated factors are kept; re-enumerating the global axes does not change the sum. |
| [Section 17.3 and Proposition 19.1](tensor_logic_semantics_part_iii.md#193-correspondence-with-pure-einsum): body and fiber | `Term.body_correspondence`, `Term.collectedBody_correspondence`, `pure_correspondence`, `Term.empty_fiber` ([Correspondence](../../leanncd/LeanNCD/Semantics/Source/Correspondence.lean)) | For every admitted output, term, total store, and destination coordinate, the pushed-forward lowered body equals the term's global fiber. Empty fibers are $0$. `pure_correspondence` adds the context identity for pure terms; the work is in `collectedBody_correspondence`, which holds for every term. |
| [Section 19](tensor_logic_semantics_part_iii.md#19-contribution-collection): collection | `collect_statement`, `AdmittedSource.collect_correspondence`, `IdentifiedSource.collect_correspondence`, `total_admEnv` ([ProgramCorrespondence](../../leanncd/LeanNCD/Semantics/Source/ProgramCorrespondence.lean)) | `Program.collect` equals the sum over statements targeting the tensor of the sum over their terms of the global fibers. Duplicate statements stay separate, and a tensor with no statements collects $0$. Every store is admissible, since the semiring operations never fail. |
| [Section 20](tensor_logic_semantics_part_iii.md#20-program-models-and-functional-denotation): models | `models_iff_global`, `sourceResult_globalModel`, `sourceResult_globalUnique`, `sourceResult_globalDenotation` | `Models` holds exactly when the inputs agree and every defined coordinate equals its global fiber. Over ℚ, a complete validated run is the unique global model and its output is the denotation. |

Proposition 19.1 is thereby proved for this fragment, including repeated slots,
empty contractions, zero extents, factor order, multiplicity, broadcast and
zero-factor terms, and sums of several terms. For actual successful
`admitRawSource`, `admitRawSource_fields` and `admitRawSource_certified` now prove
the structural link from the original raw AST's declarations and indexed
occurrences to admitted reads and outputs. `CertifiedRawTerm.semantics`,
`CertifiedRawStatement.semantics`, and `CertifiedRawSource.collect` / `.models`
connect these witnesses to the existing body, footprint, fiber and Program results,
not to a second independently specified raw denotation.
`admitRawSource_reached` requires an `ActualValidatedResult` and its actual
complete-outcome equality; its all-defined-coordinate equations, input agreement
and uniqueness are relative to `result.input`, not automatically the admitted
source's stored input buffers. `admitRawSource_reached_denotation` uses the
existing output-restricted denotation API. The parsed and asymmetric donors run
with `sourceInput`, but their kernel theorems still explicitly require completion.
`interpret_contract_reindex` ([Lowering](../../leanncd/LeanNCD/Semantics/Source/Lowering.lean))
also proves equality of actual nested reduction interpretations under a
coordinate equivalence, with the read environment transported along it.
This includes changing binder order while keeping the ordered read product;
the adapter still constructs reductions in declaration order. The fixtures
reverse unequal bounds (2 and 3) over Nat and Rat and cover empty bounds and
zero extents. This is an exact-semiring result, not a floating-point
reordering guarantee, and nothing outside the fragment is covered.

#### Source order

| Specification clause | Lean | What it fixes |
| --- | --- | --- |
| [Proposition 19.2](tensor_logic_semantics_part_iii.md#194-source-order-and-nonlinear-boundaries): source-order invariance | `StatementPermutation`, `occurrenceEquiv`, and under it `outcome`, `footprints`, `destinations`, `guards`, `originals`, `identities`, `bodies`, `admEnv`, `contribution`, `collect`, `models` ([Permutation](../../leanncd/LeanNCD/Semantics/Source/Permutation.lean)) | For any list in bijection with the admitted statements, the occurrence relabeling preserves outcomes, footprints, destinations, original identities, admissibility, contributions, collected values, and the model relation. |

No completion guarantee is added for a reordered source without a rank
certificate. Conditional successful
result agreement is proved by `StatementPermutation.successful_results`: two
initialized rational executions, with equal inputs and complete outcomes,
have equal whole stores. It combines model preservation with successful-run
uniqueness and does not equate traces or assert that either run completes.
The fixtures specialize it to statement reversal and execute an identity
permutation of an empty program. Still unproved: the connection to re-admitting
a permuted source text, which renumbers original identities, and permutation
of terms or factors.

#### Automatic schedules

`sourceSchedule` ([Schedule](../../leanncd/LeanNCD/Semantics/Source/Schedule.lean)) constructs the executor's
complete ordered schedule from the admitted source. It lists all tensors, an
occurrence key for every defined tensor, targeting statement, and output
valuation, and a publication key for every full-signature coordinate. It is
kernel-checked duplicate-free and complete (`sourceOccurrenceKeysAt_*`,
`sourcePublicationKeysAt_*`, `sourceTensors_*`; the schedule is generic in the carrier and
`sourceSchedule` is its rational instance), and duplicate statements receive
distinct keys. `runSource_not_exhausted` shows the default run is never
exhausted, and `sourceResult_model`, `sourceResult_unique`, and
`sourceResult_denotation` restate the executor's success results for source
programs. No rank certificate is synthesized or checked, so a run can end
blocked.

#### Differential debugging

[`compareSource`](../../leanncd/LeanNCD/Semantics/Source/Differential.lean) has no theorems. Its evidence is
executed fixtures and mutation controls, and every claim below is of that kind.

- **Legs.** The reference leg is the validated rational executor. An
  independent exact oracle ([Oracle](../../leanncd/LeanNCD/Semantics/Source/Oracle.lean)) evaluates the same
  admitted source over ℚ given a supplied dependency order, additively across
  statements. Two native legs run the unmodified resolved source: legacy
  evaluation and the checked dense backend ([NativeLegs](../../leanncd/LeanNCD/Semantics/Source/NativeLegs.lean)).
  The oracle mirrors `globalFiber` but is not proved equal to it, and it shares
  admission with the reference leg, so an admission bug is common to both.
- **Comparison.** The reference is compared with the oracle on published values,
  accumulators, and per-occurrence contributions ([Diagnostics](../../leanncd/LeanNCD/Semantics/Source/Diagnostics.lean)).
  Native legs are compared on output tensors only, against bits derived from the
  oracle. Classification runs in a fixed order and distinguishes reference
  incompleteness, oracle unavailability, comparison refusals, discrepancies,
  known contract differences, unsupported profiles, native unavailability or failure, and
  four-leg parity. A refusal is never counted as parity.
- **Localization.** Reference-versus-oracle differences are localized to body,
  collection, or publication. Readiness and backend arithmetic are never
  localized: readiness is not compared and native internals
  are `noBackendInternalHook`, and term values are explicitly unobserved
  ([Observation](../../leanncd/LeanNCD/Semantics/Source/Observation.lean)); causal evidence is never invented.
  Admission errors abort the comparison rather than classify.
- **Numerical profile.** [`checkProfile`](../../leanncd/LeanNCD/Semantics/Source/NumericalProfile.lean) requires
  explicit `f64` declarations (several statements may define one left-hand
  side: they are collected and value-compared), and exact
  values that are integers of magnitude at most $2^{20}$, bounding inputs,
  products, partial sums, and events. Comparison
  is exact bit equality, with $\pm 0$ equal but original bits kept. The argument
  that binary64 arithmetic is exact on this range is informal, not formalized,
  and the profile is not a floating-point semantics.
- **Known contract differences.** Every backend sums multiple definitions of one
  left-hand side (the specification, the reference leg, the oracle, and
  production, which collects them additively); fixtures F14 and F15 are
  value-compared on all four legs at `[7,13]` and `[12,22]`. The remaining
  known contract difference is an untyped tensor, which defaults to f32 and is
  classified through `StructuralCondition.usedDType`. Production resolves axes by name, so
  `NativeLegs.checkIdentity` refuses a program whose names and identities are not
  in bijection (the same name for distinct identities, or the reverse); that case
  is native-unavailable, not an unsupported profile.
  **Additive collection (decided 2026-10-14, slice 1 landed).** Production collects multiple
  definitions of a sum-algebra bare-slot tensor additively (`collectDefinitions` /
  `desugarMultiWriters`); the overwrite behavior was removed rather than kept as an option, so
  multi-definition programs are value-compared. Scatter, max/min and scan multi-writer sets are
  rejected (`CompileError.multiWriterScatter`, `multiWriterAlgebra`, `multiWriterScan`) and are not
  yet collected. See [the decision note](additive_production_decision_note.md).
  **Affine writes and scatter (S2a, landed, merge 7a551faa).** Through `admitSourceAffine` the oracle evaluates integer-affine left-hand slots
  (`AdmittedOutput.forms`, an integer-affine form per destination axis) and sum-only scatter, so a
  colliding write is summed. Production does not agree, and the differential classifies the difference as
  a `StructuralCondition` (`scatterCollisionRejected`, `multiWriterScatter`,
  `scatterExtentOverridesDeclared`) only when both native legs show the predicted outcome, with limited
  precision: confirmation is origin-bound only for the legacy collision, the checked affine-slot refusal and
  the extent condition; the checked runtime collision and multi-writer `scanAxisNotIter` are cause-only; only
  the head condition is confirmed; the collision-sum scatters `fD`/`fD'` and a bare-slot `rejectCollisions`
  over a contracted axis (F11) end as `nativeFailure` with no condition (S2a plan §2);
  S3a converts these to agreement. While `scatterExtentOverridesDeclared` is confirmed no value of that
  program is compared (documented limitation, see the S2a plan §2). The raw-parse theorem for affine
  statements is a documented gap. See [the S2a record](additive_s2a_record.md).
  **Tropical carriers (S2b, merge pending).** The oracle is generic in a scalar carrier `K` (`Oracle.Carrier`:
  `admits`, `ofRat`, `observe`; `0`, `1`, `+`, `*` come from `[Semiring K]`, the instance the Core leg lowers
  through). `standardCarriers` is a first-match table keyed on (aggregation, destination element type): `sum`
  is real, `max` is max-plus (`Tropical (WithBot ℚ)ᵒᵈ`), `min` is min-plus (`Tropical (WithTop ℚ)`); a further
  semiring is one carrier record plus one table entry, with no edit to oracle evaluation (a toy Boolean carrier
  in `SourceOracleCarrierTest` shows the mechanism; the real limit is the DSL, since `AggOp` is closed). Programs
  are single-sort and a mix is refused (`sortSelection`); cells are observed as `ExtVal` (`fin q`, `negInf`,
  `posInf`). The Core leg runs at the same carrier (`runSourceAt`, `Registry.none`); the real names are its
  rational instance, so the proofs are unchanged. A sibling harness, `compareSortedSource`
  ([SortedDifferential](../../leanncd/LeanNCD/Semantics/Source/SortedDifferential.lean)), compares Core, oracle
  and both production legs under a tropical numerical profile (finite reads are integers within ±2^20, the
  per-occurrence sum of magnitudes stays within 2^20, `±inf` is its own class; an empty reduction axis yields `±inf`
  that production accepts and matches bit for bit); the real harness
  (`compareSource`) is untouched and still refuses `max`/`min`. Production multiplies where the tropical `⊗`
  adds, so a multi-factor `max`/`min` term and a tropical affine write (production refuses a `max` scatter that
  fills with a finite value) are the structural conditions `tropicalMultiFactor` and `tropicalScatterFill`; each is
  confirmed only when both native legs show the predicted outcome at the condition's own tensor (for multi-factor:
  the same first mismatch on both legs and every tensor without that condition agreeing), otherwise the run
  stays a `nativeDiscrepancy` / `nativeFailure`. A scatter-fill refusal compares no other tensor at all. Tropical scatter is refused at admission.
  Because the oracle and the Core leg share the semiring instance and `ofRat`/`observe`, their agreement checks
  scheduling and where embedding and observation happen, not those functions or the algebra; the algebra is pinned by hand-valued oracle fixtures and by production
  agreement on single-factor rows. This is executed evidence, not a theorem. Production tropical sorts, casts
  and constants (S3b) and scatter collision ⊕ and range errors (S3a) remain planned. Parked: merging the two
  harnesses, a tropical oracle-receipt re-check and Program theorems, f32 tropical production comparison.
  See [the S2b record](additive_s2b_record.md).
- **Evidence.** 79 named fixtures (one of them, F16, evaluates a generated corpus
  of exactly 18 programs) and 39 implementation mutations: 18 proof-protected kills and 21
  executable-fixture kills, not 39 runtime differential samples. Six historical
  input contrasts were replayed on the pinned seed. The controller full build
  passed with 8,763 jobs, and both whole-branch reviews were clean
  ([record](source_correspondence_record.md#final-controller-close-out-2026-10-09)).

#### What the source layer does not claim

- **No substitution or renaming by admission.** Proof target 2 is only partially
  addressed, for identity-keyed valuations and binder freshening; no theorem says
  interpretation or footprints are invariant under renaming.
- **No general elaboration.** Everything outside the fragment is refused, and
  the Adapter drops the linear bias flag, element types as semantics, and names.
- **No independent raw denotation or parser correctness.** The raw AST certificate
  proves successful-admission correspondence and existing-semantic applicability,
  not string parsing, global UID mint injectivity, input-buffer certification or
  unconditional successful execution.
- **No proof for the oracle or the comparison.** There is no theorem about
  `compareSource`, the numerical profile, or the native legs, and no backend
  refinement result. The formalized Part V results are the slices 1-4 plan layer
  ([Section 4.9](#49-part-v-slice-1-the-singleton-command-plan-layer)) and slice 5's
  bounded full-history scan ([Section 5.2](lean_executable_semantics_path_part_5.md#52-later-compiled-and-numerical-refinement));
  neither certifies the source layer or the differential oracle.
- **No floating-point correctness.** f32 and f64 are metadata in the exact
  semantics; the bit comparison holds only on the bounded-integer, f64-declared,
  single-definition profile.
- **No injected-fault claims.** The signed-zero, warning, and two protocol cases
  were injected, not observed from a real backend, and native nonoutputs are
  not compared.
- **No rank synthesis or trace/status independence.** Conditional whole-store
  agreement under statement permutation is proved for completed runs over ℚ.

### 4.8 Existing validation and its limits

The execution records distinguish observed computation, proof checking,
mutation controls, and unsupported claims:

| Layer (status) | Tests | Validation record |
| --- | --- | --- |
| Strict expressions/readiness | [ExpressionTest](../../leanncd/test/Semantics/ExpressionTest.lean), [NativeTest](../../leanncd/test/Semantics/NativeTest.lean), [ContractTest](../../leanncd/test/Semantics/ContractTest.lean) | [Expression/readiness execution](expression_readiness_execution_record.md) |
| Collection/models | [CollectionModelTest](../../leanncd/test/Semantics/CollectionModelTest.lean) | [Collection/model execution](collection_model_execution_record.md) |
| Reference transitions/soundness | [ReferenceMachineTest](../../leanncd/test/Semantics/ReferenceMachineTest.lean) | [Reference-machine execution](reference_machine_execution_record.md) |
| Coordinate ranks/termination/correspondence | [RankedMachineTest](../../leanncd/test/Semantics/RankedMachineTest.lean) | [Coordinate-ranks/finite-measure execution](coordinate_ranks_finite_measure_execution_record.md) |
| Computable validated reference | [ExecutableReferenceTest](../../leanncd/test/Semantics/ExecutableReferenceTest.lean) | [Executor implementation execution](computable_reference_executor_record.md#8-implementation-execution-2026-10-08) |
| Bounded source correspondence and differential debugging | [SourceAdmissionTest](../../leanncd/test/Semantics/SourceAdmissionTest.lean), [SourceBindingTest](../../leanncd/test/Semantics/SourceBindingTest.lean), [SourceCorrespondenceTest](../../leanncd/test/Semantics/SourceCorrespondenceTest.lean), [SourceProgramTest](../../leanncd/test/Semantics/SourceProgramTest.lean), [SourceOracleTest](../../leanncd/test/Semantics/SourceOracleTest.lean), [SourceDiagnosticTest](../../leanncd/test/Semantics/SourceDiagnosticTest.lean), [SourceDifferentialTest](../../leanncd/test/Semantics/SourceDifferentialTest.lean), [SourceRawCorrespondenceTest](../../leanncd/test/Semantics/SourceRawCorrespondenceTest.lean), [SourceCorrespondenceTransportTest](../../leanncd/test/Semantics/SourceCorrespondenceTransportTest.lean), [SourceProgramIdentityTest](../../leanncd/test/Semantics/SourceProgramIdentityTest.lean) | [Source correspondence record](source_correspondence_record.md), [raw-source/admission record](raw_source_admission_record.md) |
| Part V slice-1/2 plan layer | [PlanFusionTest](../../leanncd/test/Semantics/PlanFusionTest.lean), [PlanFusionCorrectnessTest](../../leanncd/test/Semantics/PlanFusionCorrectnessTest.lean), [PlanFusionCheckerTest](../../leanncd/test/Semantics/PlanFusionCheckerTest.lean), [PlanBatchTest](../../leanncd/test/Semantics/PlanBatchTest.lean), [PlanMemoryTest](../../leanncd/test/Semantics/PlanMemoryTest.lean), [PlanStepTest](../../leanncd/test/Semantics/PlanStepTest.lean), [PlanSimulationTest](../../leanncd/test/Semantics/PlanSimulationTest.lean), [PlanValidityTest](../../leanncd/test/Semantics/PlanValidityTest.lean), [PlanRunTest](../../leanncd/test/Semantics/PlanRunTest.lean), [PlanCorrectnessTest](../../leanncd/test/Semantics/PlanCorrectnessTest.lean), [PlanMultiSortTest](../../leanncd/test/Semantics/PlanMultiSortTest.lean), shared [PlanFixtures](../../leanncd/test/Semantics/PlanFixtures.lean) | [Plan-layer mutation results](plan_layer_mutation_results.md), [slice-2 mutation results](plan_layer_slice2_mutation_results.md) |
| Part V retirement, reuse and fault wrappers (landed) | [PlanRetireTest](../../leanncd/test/Semantics/PlanRetireTest.lean), [PlanFaultsTest](../../leanncd/test/Semantics/PlanFaultsTest.lean), [PlanReuseTest](../../leanncd/test/Semantics/PlanReuseTest.lean), [PlanReuseStorageTest](../../leanncd/test/Semantics/PlanReuseStorageTest.lean), [PlanReuseWrapperTest](../../leanncd/test/Semantics/PlanReuseWrapperTest.lean) | [Slice-3 record](plan_layer_slice3_record.md), [slice-4 record](plan_layer_slice4_record.md) |

All are discovered by the default `Tests` target. Existing fixtures cover
strict zero multiplication, empty binders, whole-array selection obligations,
heterogeneous primitives, duplicate contributions, colliding destinations,
empty input presence, nonoutput equations, publication barriers, and failure
versus unavailable reads. The earlier logical machine fixtures include a proved successful
run and failure exclusion, but are not runtime executions by a scheduler.
The cyclic blocked fixture is not separately proved reachable.

[`Semantics.AxiomAudit`](../../leanncd/test/Semantics/AxiomAudit.lean) fails the
build if any theorem or definition under `LeanNCD.Semantics` reaches an axiom
other than `propext`, `Classical.choice`, and `Quot.sound`. A `sorry`, a
`native_decide`, or a new `axiom` therefore cannot land silently, and the
"proved" rows in the status tables stay enforceable. It covers the whole
namespace (5,142 constants when added), so no list needs to be kept in sync, and
a self-test checks that a deliberately non-standard axiom is rejected. Only
modules imported through `LeanNCD/Semantics.lean` are audited.

The ranked fixtures add 16 acceptance families: same-tensor coordinate history,
strict masked self-dependency versus guard exclusion, whole-array and binder
demand, input-dependency exclusion, duplicate/zero consumption counts,
empty-fiber and nonoutput publication, rank-zero scalar and zero-extent cases,
ready failure, an unranked model with blocking, stopped-prefix nonmaximality,
successful schedule agreement, distinct first failures, and singleton
correspondence. The second successful schedule is supplied by an existential
proof, not an executable chooser.
All six selected mutations passed their intended generic kernel-proof rejection
and byte-identical restoration gates; this is not an independent runtime or
fixture-only mutation kill for each acceptance family.
The full default build and integrated-main build passed. The follow-up removed
three new unused-simp warnings; 14 inherited warnings remain, so validation is
green, not warning-free.

The executable fixtures run the exact-rational driver and assert 22 named rows,
described under [Fixtures and controls](#fixtures-and-controls) in Section 4.6.
All 19 controls passed with expected failures, byte-identical source restoration,
and restored green builds: 4 proof/type rejections, 2 production runtime oracle
kills, and 13 fixture contrasts. The post-mutation full default build passed
(8,704 jobs); unusedSectionVars and unnecessarySeqFocus warnings remain.
These controls do not claim 19 production-runtime kills or general source
correspondence. Heterogeneous non-additive-input runtime coverage remains parked.

The nested-reduction and successful-permutation follow-ups (`705280cd`,
`ca642b3d`) have no separate record; their validation is in their commit
messages: one hand mutation each (the reordered Nat result changed from 19310 to
19311; a required input-equality witness replaced by `rfl` was rejected), and a
full build of 8,763 jobs for `ca642b3d`.

Native expression fixtures use checked binary32/binary64 primitive APIs and
observe rounding differences. They do not give machine floats exact additive
laws or connect a floating-point backend to the complete-model theorem.
Generic collection allows an appropriate Boolean OR additive structure, but
these collection/model fixtures do not establish a Boolean OR instance or
its execution profile.
The earlier [semantic-core spike](tensor_logic_semantic_core_spike_record.md)
and `ContractTest` supply a narrow signed-coordinate `StMat` seam, not a full
categorical interpretation or general source correspondence.

### 4.9 Part V slice 1: the singleton-command plan layer

Slice 2 extends the layer to fused commands, slice 3 to retirement, and the
landed slice-4 implementation to typed static same-sort buffer reuse.

`LeanNCD.Semantics.Plan` (imported by `LeanNCD.Semantics`) is the first Lean model of
[Part V](tensor_logic_semantics_part_v.md#part-v-compilation-and-refinement): a reference plan
`Program.Plan` of annotated commands over allocation-indexed exact memory, a computable checker for
Definition 31.1 in its slice-1 form, and proofs of Lemma 31.2, Theorem 31.3 and Lemma 32.1 for
that profile. It is not the checked evaluation backend `Eval/Plan` (`CheckedEvalPlan`); no theorem
connects the two.

#### Plan modules

The modules are in [`LeanNCD/Semantics/Plan/`](../../leanncd/LeanNCD/Semantics/Plan/), in import order:

- `Plan/Syntax`: `Allocation` (finite buffers, sorts, capacities, typed `locate`), canonical default,
  allocation-preserving expansion, annotations (`initZero`, `acc`, `pub`, `retire`), commands, the prefix `prefixAnn`, the retired and
  readable sets `Ret`/`Live` and the schedule views `accFlat`/`pubFlat`.
- `Plan/Batch`: `accumulateBatch` and `publishBlock` at the logical level; Lemma 32.1 without any
  memory model.
- `Plan/Memory`: separate `InputSlot` and reusable `BufferSlot`, allocation-indexed memory,
  `Start`, `place`, `readSlot`, the layout view `SlotView` and its domain injectivity `LayoutOK`,
  with canonical compatibility `layoutOK_of_canonical`,
  the read view `readPub`, `Decode`, the reference post-state
  `refState`, and the relation `R` (fields `dead`, `retPub`) with `R_start`.
- `Plan/Step`: the step kernels, `StepResult`, `PlanOutcome`, validated `Start`, and the run
  `runPlan`/`runFrom`.
- `Plan/Simulation`: per-annotation side conditions (`InitOK`, `AccOK`, `PubOK`, `RetOK`, `AnnOK`) and
  one-step simulation `step_R`, `step_failed`, `step_retire`.
- `Plan/Validity`: `Valid` (Definition 31.1, singleton form; fields `retOK`, all-boundary `layout`),
  `resourceList`, `checkLayoutAt`, `checkLayouts` and their exactness, the computable `checkPlan` (with `checkRet`),
  `checkPlan_sound`, `checkPlan_complete` (so `checkPlan_iff`),
  `checkPlan_of_canonical` and `checkAccMat_of_rest`.
- `Plan/Run`: progress `step_not_stuck` and the multi-step run lemma `run_R`/`runPlan_R`.
- `Plan/Correctness`: terminal adequacy and compiled correctness.
- `Plan/Fusion`: fold lemmas for a fused command (`execAnns_R`, `step_R_command`, `step_failed_command`,
  `stepCommand_not_stuck`) and the run bridge `runFrom_agree`/`runPlan_agree` between a fused plan and
  its expansion. (`expand` and `offset` live in `Plan/Syntax`, `execAnns` in `Plan/Step`.)
- `Plan/FusionCorrectness`: `FValid`, `checkPlanF`/`checkPlanF_sound`/`checkPlanF_complete`, `runFrom_R_F`, `runPlan_R_F`, `terminal_adequacy_F`
  and the compiled-correctness theorems `done_correct_F` ... `done_iff_model_F`.
- `Plan/Faults`: implementation errors as a wrapper over an abstract fault oracle (`FOutcome`, `runFromE`,
  `runPlanE`), with Theorem 31.3 (a)(b)(c) restated under faults.

#### Plan-layer theorems

| Theorem | Mathematical conclusion | Spec result |
| --- | --- | --- |
| `batch_execution`, `batch_execution_perm`, `accumulateBatch_accumulators`, `accumulateBatch_pending`, `accumulateBatch_published` | A duplicate-free, pending, ready, successful group is a reference execution ending at accumulator $\alpha\oplus\Delta_G$ and remaining set $U\setminus G$, in any enumeration order | Lemma 32.1 |
| `R_start` | The initial memory is R-related to the initial reference state | Section 31.2 (initialization) |
| `step_R` | From R, `Conf = refState pc`, `AnnOK` and pre/post `LayoutOK`, a successful singleton step re-establishes R at `pc + 1` | Section 31.2 (step simulation) |
| `step_failed` | A failed step is matched by one `undefined` event for the same occurrence from the related state | Section 31.3 (failure matching) |
| `checkPlan_sound` | An accepted plan satisfies `Valid` | Definition 31.1 |
| `checkPlan_complete`, `checkPlan_iff` | A `Valid` plan is accepted, so `checkPlan` decides `Valid` exactly | Definition 31.1 |
| `layoutOK_of_canonical`, `checkPlan_of_canonical` | Canonical allocation is layout-safe at every boundary; if the other checker clauses pass, the added layout clause does not reject the plan | Slice-4 compatibility with the canonical profile |
| `accFlat_nodup_of_accOK`, `pubFlat_nodup_of_pubOK`, `Valid.coverage_nodup_of_steps` | On a singleton plan, `AccOK` (resp. `PubOK`) at every `acc` (resp. `pub`) command makes the accumulation (publication) image duplicate-free: the Nodup halves of coverage 1 and 2 are consequences of the step conditions (checker-level form: `checkPlan_nodup_redundant`) | Section 29.3 conditions 1-2 (Nodup halves) |
| `checkAccMat_of_rest` | Given `checkSingleton`, `checkCov2Complete`, `checkInit` at every `initZero` and `checkPubMat` at every `pub`, `checkAccMat` holds at every `acc`: the clause is shadowed | Definition 31.1 (checker redundancy; no spec result) |
| `step_not_stuck`, `runPlan_not_stuck` | A valid plan's run never reports `stuck` | Section 31.3 (progress) |
| `run_R`, `runPlan_R` | The whole run ends `done m` with R and a reference execution, or fails with a matched failure | Sections 31.2-31.3 |
| `terminal_adequacy`, `complete_of_refState` | At `done m M'` the reference state is complete and `Decode` gives its outputs | Lemma 31.2 |
| `done_correct`, `failed_correct`, `done_or_failed`, `done_of_model`, `done_iff_model` | `done` gives the unique model and the denotation; `failed` gives no model; the run is `done` iff a model exists | Theorem 31.3 |
| `step_R_command` | From R and `Conf = refState pc`, with `AnnOK` at each expanded position and every expanded-boundary `LayoutOK`, a successful fused command re-establishes R at `pc + 1` | Section 31.2 (fused) |
| `step_failed_command` | From R and `Conf = refState pc`, a failing fused command is matched by some reference execution from `Conf` to `Failed` on the same occurrence (the execution may include the earlier annotations of the command) | Section 31.3 (fused failure) |
| `stepCommand_not_stuck` | From R and `refState pc = some c`, a command of an `FValid` plan is never stuck | Section 31.3 (progress, fused) |
| `runPlan_agree` | A fused plan and its expansion run to the same final memory, or fail at the same occurrence | run bridge (no spec result) |
| `checkPlanF_sound`, `checkPlanF_complete`, `checkPlanF_iff` | A fused plan is accepted iff it satisfies `FValid` (Definition 31.1 of the expansion) | Definition 31.1 |
| `terminal_adequacy_F`, `done_correct_F`, `failed_correct_F`, `done_or_failed_F`, `done_of_model_F`, `done_iff_model_F` | Lemma 31.2 and Theorem 31.3 for `FValid` fused plans | Lemma 31.2, Theorem 31.3 |
| `step_retire` | From R, `Conf = refState pc`, `RetOK` and pre-layout safety, the reference state is unchanged, each block member's slot is cleared and R is re-established | Section 30.3 (retirement) |
| `checkLayoutAt_iff`, `checkLayouts_iff`, `Valid.layout_boundary` | Exact resource-pair separation at one/all boundaries, including the final one; validity supplies step pre/post layouts | Sections 30.2, 31.1-31.2 |
| `checkRet_sound`, `checkRet_complete` | `checkRet` accepts exactly `RetOK`, so `checkPlan_iff` still holds with the retire clause | Definition 31.1 |
| `live_output_of_valid` | A valid plan has every output coordinate live at the end, so no retire of an output exists | Lemma 31.2 |

#### Fused commands (slice 2)

Slice 2 extends the layer to fused commands: a command is a finite, possibly empty, list of annotations
run in order. The design is expansion: `π.expand` is the plan whose commands are the singletons of
`π.ann`, a fused plan is valid when its expansion is (`FValid`, `checkPlanF`), and the run bridge
`runPlan_agree` reuses the slice-1 proofs on the expansion. A failing annotation rolls back the whole
command (the failure memory is the memory before the command), `R` is claimed at command boundaries only,
and `done m` counts commands, not expanded annotations (so `Agree` compares final memory or failing
occurrence, never the pc). The singleton `checkSteps` is vacuous on a fused command,
and `checkSingleton` rejects non-singletons. Use `checkPlanF` for fused validity;
outer-boundary layouts alone are insufficient. The run does not detect a mis-fused plan:
`misfused-run-undetected` runs to `done`, and `t4-a5-reinitMid` silently ends with a wrong value;
`checkPlanF` rejects both. The case-by-class table (a1-a10, b-e: legal and forbidden intra-command
dependencies; every cell but e (a theorem) and c (argued, not probed) is pinned by a fixture) is section 2 of `plan_layer_slice2_plan.md`. Slice 2 changed two slice-1 statements
(`step_failed`, `step_failed_no_model`, now stated for `commands[pc]? = some [a]`) and three slice-1
fixtures that had asserted "fused or empty is stuck".

#### Buffer retirement (slice 3)

Slice 3 adds the annotation `retire B` for defined addresses (`Ann.retire`; inputs are never retired and are
always live, `live_input`). `Pub` stays the logical published set and `Live = Pub \ Ret` is the readable set:
`readPub`, `SlotView .pub`, `ReadyOK` and `R`'s `pubSlot` range over `Live`. `execRet` clears each member's slot to
`none`; the reference state does not change, so a retired address stays in the logical `σ` as ghost history.
Reading a retired slot in a later `acc` is a plan defect: `ReadyOK` over `Live` is the reader-side rule that rejects
it, and a run that does it is `stuck`, never an implementation error; decoding a retired output yields `none` and
the run still ends `done` (only the checker rejects that).

`RetOK` has three roles: that every member is published is safety (a retire of an unpublished address would
clear a live accumulator); that no member is already retired is diagnostic; that no member is an output is
terminal (`live_output_of_valid`). `R` gains two fields, `dead` (a retired slot is `none`) and `retPub` (a
retired address is published; Lean only, needed because `R` does not remember earlier steps), and `readPub_eq`
is restated pointwise on `Live`. `Valid` gains the field `retOK`, and `checkPlan_iff` still holds.

The case-by-class table is the "Review Focus" section of `plan_layer_slice3_plan.md`; the two deviations from the
design spec (`retPub` and the pointwise `readPub_eq`) are recorded in its section 3.4.
The address-indexed `dead` description and diagnostic second-retire classification
above describe slice 3 historically; slice 4 changes them as follows.

#### Buffer reuse and aliasing (slice 4, landed)

`Allocation` has explicit complete finite independent buffer identities,
computable equality, per-buffer sort/capacity and bounded sort-certified placement.
The canonical default preserves one buffer per tensor and the existing constructors.
Inputs have separate storage. `Memory`, kernels, reads, decoding and outcomes
carry allocation; `expand` preserves it. Prefix transport (`execAnn_prefix`,
`R_transport`, `decode_prefix_congr`) requires allocation equality and memory casts.

`SlotView` maps `Live` published resources and materialized unpublished
accumulators. `LayoutOK` requires domain injectivity only at the current boundary;
`Valid.layout` and `checkLayouts` cover 0 through `commands.length`, including
pub/pub, pub/acc and acc/acc pairs. Fused checking uses all expanded boundaries.
Initialization needs the successor layout; accumulation/retirement need the
current layout; `step_R` carries both. Publication/failure add none.

`R.dead` now means every unmapped physical slot is `none`, including unused
capacity. A retired address's old slot may hold a new resource; `readPub` still
returns `none` for that logical address. Retirement must act on a live resource:
the no-second-retire condition is now safety, since a repeated retire could clear
a new occupant. Outputs remain live and cannot be retired or overwritten while
represented. Unchecked invalid aliases can finish `done` with corrupted values.

`PlanReuseTest` pins actual point-2-to-retired-point-0 overwrite (`done 7`,
raw row `[4,3,4]`, ghost 0 vs retired read `none`), nearest live-alias rejection,
all three resource-pair classes and final-boundary checking.
`PlanReuseStorageTest` pins distinct internal/output tensors sharing one buffer
index, decode 2 matching canonical, typed ℤ/ℚ decode `(11,7/8)`, empty outputs
and custom zero/unused capacity. A later internal initializer claiming a live
output's slot is rejected only by layout, while its canonical twin passes; the
unchecked shared run corrupts and then clears the output. Re-retiring point 0
after point 2 takes its slot clears point 2 and makes its later publication
`stuck`, unlike canonical storage. Empty decoding is only a control, not a
layout discriminator. `PlanReuseWrapperTest` pins retire-then-init fusion,
an internal-only collision (all outer layouts true, expanded index 4 false),
fault-after-write error-state R at pc 5 and no-fault parity.

#### Slices 1-4 profile, fixtures and mutations

The profile is: singleton or fused commands (fusion by expansion), retirement of defined published addresses
(`Pub` logical, `Live` readable), typed static same-sort reuse with boundary-local
layout injectivity, and error-free kernels (faults remain an abstract wrapper). Soundness rests on `checkPlan`
(singleton plans) or `checkPlanF` (fused plans): the run does not detect an invalid plan. The spec's
restatements are the paragraphs headed "As formalized (slice-1 to slice-4 profile ...)" (in 30.3 and 33.2: "(slice-3 to slice-4 profile ...)") in Sections
29.3, 30.2, 30.3, 30.4, 31.1-31.4, 32.1 and 33.2 of the
[specification](tensor_logic_semantics.md). The slices 1-4 fixture baseline contains 367
fixtures (186 `#eval check` rows and 181 top-level `example`/`theorem` items);
slice 5 adds 149, giving 516 (239 + 277) in the current `Plan*Test.lean` glob.
All 281 baseline assertions (149 + 132) are preserved, with four additional
retirement component rows; 82 reuse fixtures are split 31 core, 26 storage and
25 wrapper. Default `Tests` retains all 13 original
`Plan*Test` modules and adds these three, giving 16 test modules. `PlanFixtures`
is one additional shared module: 14 original Plan test/shared modules, 17 through
slice 4. The two scan modules bring the current totals to 18 test modules and
19 including `PlanFixtures`.
Of the baseline, 68 are slice 3's
`PlanRetireTest` (27 rows, 24 `example`s, 17 theorems); the earlier figure of 180 was off by one (181 by this method
at the commit that wrote it: 110 rows + 71 items), and `PlanFaultsTest` added 19 after it (12 rows + 7 items),
which gives the 200 before slice 3. The four appended component rows bring
`PlanRetireTest` to 72 (31 rows + 41 proof items) today.
Historically the mutation manifests ran 54 cycles (20 in slice 1, 15 in
slice 2, 9 in the D7 manifest, 10 in slice 3), of which 4 are labelled equivalent among the 35 of slices 1-2
(3 in slice 1; S2-M4 at fixture level) and none among the 10 of slice 3 (every one was killed at a library proof).
Those are historical observations, not slice-4 rerun results. The current implementation
has 64 manifest controls: 54 inherited + 10 reuse controls (6 library-proof,
1 test-level invariant consumer, 3 computed fixtures).
All 64 controls have been rerun successfully with 167 exact failure-site
expectations, including D7; multi-site expectations remain separate.
The probe-closure pass additionally reran the two affected buffer manifests,
10/10 each, without changing mutation entries or moving existing fixture anchors.
Results are in [plan_layer_slice4_mutation_results/](plan_layer_slice4_mutation_results/).
Inherited equivalent controls are
proof-shape checks, not semantic counterexamples; `--check` uniqueness alone
is not kill evidence. Review and probe closures are merged and pushed through
`e9ae73f1`, with evidence in the slice records.

The old slice-3 O3 fixture-probe gap is closed by
[buffer-fixture-probes.py](../../leanncd/scripts/buffer-fixture-probes.py): all ten exact retirement substitutions
kill independently evaluated components, including the seven previously
unmeasured variants. Clean source copies prove parity with production and use
the committed fixture expressions. The unused-capacity `R.dead` consumer is also
checked independently of the retirement test's earlier proof barrier. Six
additional reuse computational controls are measured as well: layout omission,
final-boundary omission, each missing resource kind, accumulator role exclusion,
and preservation of a co-live neighbour during retirement. These seventeen
supplemental probes do not admit proofs, mutate production, or claim
whole-executor mutation coverage. Together with the three existing reuse
fixture controls, every buffer manifest entry has evidence beyond a library-proof kill.

#### What slices 1-4 do not do

- Cross-sort reads and primitives (the one multi-sort fixture, `PlanMultiSortTest`, has an empty registry), numeric kernels other than the exact reference, floating point.
- Retiring inputs, copy/relocate, dynamic allocation, cross-sort reuse,
  in-place kernels/snapshots and two-buffer scan last-reader liveness. Static
  same-sort reuse after retirement is done; the Section 33.2 scan example is not
  formalized. Slice 5 separately certifies the Section 33.1 full-history plan.
- Concrete implementation-error sources: `Plan/Faults.lean` models errors as an abstract fault oracle (`FOutcome`, error-free profile, (a)(b)(c) under faults, `R` at the error state; fixtures in `PlanFaultsTest`), so allocation failure and kernel errors are oracle outputs, not events of the model.
- Comparing the failure occurrence or failure snapshot between the plan and the reference executor.
- Dropping the redundant condition-1 covering clause of `Valid`. It follows from the condition-2
  covering clause and condition 4 (`accFlat_complete`), but `complete_of_refState` consumes it
  directly, so dropping it means rerouting that proof.

---

[Previous: 3. The category-theoretic organization](lean_executable_semantics_path_part_3.md) | [Contents](README.md) | [Next: 5. Remaining work, in dependency order](lean_executable_semantics_path_part_5.md)
