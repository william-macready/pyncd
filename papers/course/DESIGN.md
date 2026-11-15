# Design note: course notes on categorical semantics of Tensor Logic

Instructor-facing. Records what the notes are for, the decisions taken, the
alternatives rejected, and the authoring plan. Students do not need this file.

## Intent

A short course for students who know categories, functors and natural
transformations but have not used adjunctions, Kan extensions, monads,
coalgebras or spans in anger. The course has one thesis:

> Category theory is the right organizing principle for a *semantics that
> an agentic coder has to turn into code*. It tells the agent which
> structures are distinct, which laws must hold, and where a tempting
> shortcut is a semantic error.

The running example is Tensor Logic (TL): its denotational semantics
(models of contribution equations), its operational semantics (the
reference machine), and the Lean realization of both. Each categorical tool
is introduced only where it buys something in that example.

## Sources and their authority

- `papers/semantics/tensor_logic_semantics*.md` is the semantic authority.
  Nothing in the notes may contradict it.
- `papers/semantics/categorical_tensor_logic_semantics.md` is a proposal.
  The notes adjust it (see Decisions) where that simplifies exposition or
  proofs. Adjustments are stated in `07-outlook.md`.
- `leanncd/LeanNCD/Semantics/*.lean` is the landed Lean reference. The
  notes cite it by definition and theorem name, verified against the files.

## Goals, non-goals, anti-goals

Goals: (1) a reader can state, for TL, what the index category, the value
functor, the partial-map category, the model equalizer, the witness span and
the machine coalgebra are, and why they are different; (2) a reader can
compute the model and a machine run of the running example by hand;
(3) a reader can map each categorical notion to a Lean definition and run
the mini development; (4) the notes are testable: question sets with answer
keys, and recorded results of agent "students" who saw only the notes.

Non-goals: the St/Br graded-PROP syntax, Naperian typing in general,
Turi-Plotkin bialgebraic semantics (mentioned only in the outlook), Part V
compilation (outlook only), floating point.

Anti-goals: overclaiming. No pullback/pushforward adjunction on K-families
is claimed as a theorem; no least fixed point; ⊥ is never a zero; batching
of partial maps is lax-natural, not natural.

## Decisions (and the alternatives rejected)

1. **Index layer = FinSet with the adjoint triple Σ_f ⊣ f^* ⊣ Π_f on
   Set-valued families, read as Kan extensions along maps of discrete
   categories, then decategorified to K-valued families.** Rejected:
   presenting pullback/pushforward only as two unrelated functors (the
   categorical proposal's cautious stance). That stance is correct but
   hides the one place students can meet Kan extensions concretely. We keep
   the caution by stating the *transpose identity* ⟨f_! u, w⟩ = ⟨u, f^* w⟩
   as the decategorified shadow of the adjunction, proved directly.
2. **Pure einsum = composition in Span(FinSet), linearized.** Rejected:
   string-diagram / compact-closed presentations (not justified for the
   partial fragment, per the proposal).
3. **Partial bodies = Kleisli(Option) = Pfn, with strict pairing as a
   monoidal (not cartesian) product and `sequence` as a distributive law.**
   Rejected: domain-theoretic ⊥ with an order. The spec attaches no order to
   ⊥.
4. **Models = equalizer of the equation operator and the inclusion; the
   denotation of a program = a span of sets Env(In) ← Models → Env(Out)
   up to span isomorphism; partial functions are the monic-left-leg case.**
   Rejected: the proposal's metadata-bearing whole-interface objects. The
   plain-set span carries the same content for teaching; the Lean
   experimental modules prove the laws for the richer objects, and the notes
   say so.
5. **Machine = finitely branching coalgebra over configurations, with the
   store-extension preorder as a thin category, invariants as
   subcoalgebras, the measure as a well-foundedness witness, and the rank
   certificate as a lax morphism into (ℕ, <).** Rejected: building a
   Turi-Plotkin distributive law (the proposal itself lists it as an
   unexecuted pilot).
6. **One fixed running example with numbers**, used in every chapter, plus
   the spec's finite-history (scan) example for ranks.
7. **A self-contained mini Lean development** (`lean/MiniTensorLogic.lean`,
   compiled with `lake env lean` from `leanncd/`), separate from the
   production `LeanNCD.Semantics` modules, which are cited not copied.

## Authoring plan (agents as graduate students)

| Wave | Chapter | Author tier | Why that tier |
| --- | --- | --- | --- |
| 1 | 00 prerequisites | Sonnet | standard material, must be accurate but not deep |
| 1 | 01 tensor logic and the running example | Sonnet | careful summary of spec Parts I–II |
| 1 | 02 categories of indices | Opus, from the instructor's skeleton | the foundational chapter |
| 1 | 03 partiality | Opus | subtle (lax naturality) |
| 2 | 04 denotational semantics | Opus | equalizer + span semantics |
| 2 | 05 operational semantics | Opus | coalgebra + correspondence proof |
| 2 | lean/MiniTensorLogic.lean | Opus | must compile; proofs |
| 3 | 06 from categories to Lean | Sonnet | dictionary + walkthrough |
| 3 | 07 outlook | Haiku, Sonnet-reviewed | summary of existing records |
| 4 | reviews, one per chapter | Sonnet | spec conformance |
| 5 | assessment: students see only the notes | Sonnet and Haiku | efficacy test |
| 5 | grading and revision | instructor | |

Every author receives `CONVENTIONS.md` (notation, running example,
non-negotiable facts) and the exact source files to read. Authors never
invent theorem names: Lean names are copied from the files.

## Verification

- Every Lean name cited in the notes exists in `leanncd` (grep).
- `lean/MiniTensorLogic.lean` compiles with no `sorry`.
- Every internal link resolves.
- Each chapter passes a spec-conformance review against the listed spec
  parts.
- Assessment results are recorded in `assessment/results.md`, including
  failures and the revisions they triggered.
