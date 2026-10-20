# From Tensor Logic semantics to a Lean executable reference

[Previous: Semantics introduction](README.md) | [Contents](README.md) | [Next: 1. Purpose, authority, and current position](lean_executable_semantics_path_part_1.md)

This guide connects the Tensor Logic specification to its Lean executable
reference. It is divided into six files following the original top-level
sections, so each can be read separately on GitHub. Section numbering and
mathematical notation are unchanged.

For both document series and the recommended reading order, see the
[semantics introduction](README.md).

## Table of contents

- [1. Purpose, authority, and current position](lean_executable_semantics_path_part_1.md#1-purpose-authority-and-current-position)
- [2. One notation, two presentations](lean_executable_semantics_path_part_2.md#2-one-notation-two-presentations)
  - [Core admission and source elaboration](lean_executable_semantics_path_part_2.md#core-admission-and-source-elaboration)
- [3. The category-theoretic organization](lean_executable_semantics_path_part_3.md#3-the-category-theoretic-organization)
  - [3.1 Finite coordinate families: representation and contravariance](lean_executable_semantics_path_part_3.md#31-finite-coordinate-families-representation-and-contravariance)
  - [3.2 Finite additive pushforward: covariance and multiplicity](lean_executable_semantics_path_part_3.md#32-finite-additive-pushforward-covariance-and-multiplicity)
  - [3.3 Partial maps organize expression definedness](lean_executable_semantics_path_part_3.md#33-partial-maps-organize-expression-definedness)
  - [3.4 State extension organizes operational refinement](lean_executable_semantics_path_part_3.md#34-state-extension-organizes-operational-refinement)
- [4. What is implemented and proved](lean_executable_semantics_path_part_4.md#4-what-is-implemented-and-proved)
  - [4.1 Strict expressions and stable ready evaluation](lean_executable_semantics_path_part_4.md#41-strict-expressions-and-stable-ready-evaluation)
  - [4.2 Occurrences, collection, and models](lean_executable_semantics_path_part_4.md#42-occurrences-collection-and-models)
  - [4.3 Reference transitions and conservation](lean_executable_semantics_path_part_4.md#43-reference-transitions-and-conservation)
  - [4.4 What reached-run soundness establishes](lean_executable_semantics_path_part_4.md#44-what-reached-run-soundness-establishes)
  - [4.5 Coordinate ranks, finite termination, and correspondence](lean_executable_semantics_path_part_4.md#45-coordinate-ranks-finite-termination-and-correspondence)
  - [4.6 The computable reference executor](lean_executable_semantics_path_part_4.md#46-the-computable-reference-executor)
    - [Definitions and supplied inputs](lean_executable_semantics_path_part_4.md#definitions-and-supplied-inputs)
    - [Correspondence to the specification](lean_executable_semantics_path_part_4.md#correspondence-to-the-specification)
    - [Theorems](lean_executable_semantics_path_part_4.md#theorems)
    - [Fixtures and controls](lean_executable_semantics_path_part_4.md#fixtures-and-controls)
    - [What this does not claim](lean_executable_semantics_path_part_4.md#what-this-does-not-claim)
  - [4.7 Bounded source correspondence and differential debugging](lean_executable_semantics_path_part_4.md#47-bounded-source-correspondence-and-differential-debugging)
    - [Binding and admission](lean_executable_semantics_path_part_4.md#binding-and-admission)
    - [Pure-einsum correspondence and collection](lean_executable_semantics_path_part_4.md#pure-einsum-correspondence-and-collection)
    - [Source order](lean_executable_semantics_path_part_4.md#source-order)
    - [Automatic schedules](lean_executable_semantics_path_part_4.md#automatic-schedules)
    - [Differential debugging](lean_executable_semantics_path_part_4.md#differential-debugging)
    - [What the source layer does not claim](lean_executable_semantics_path_part_4.md#what-the-source-layer-does-not-claim)
  - [4.8 Existing validation and its limits](lean_executable_semantics_path_part_4.md#48-existing-validation-and-its-limits)
  - [4.9 Part V slice 1: the singleton-command plan layer](lean_executable_semantics_path_part_4.md#49-part-v-slice-1-the-singleton-command-plan-layer)
    - [Plan modules](lean_executable_semantics_path_part_4.md#plan-modules)
    - [Plan-layer theorems](lean_executable_semantics_path_part_4.md#plan-layer-theorems)
    - [Fused commands (slice 2)](lean_executable_semantics_path_part_4.md#fused-commands-slice-2)
    - [Buffer retirement (slice 3)](lean_executable_semantics_path_part_4.md#buffer-retirement-slice-3)
    - [Buffer reuse and aliasing (slice 4, landed)](lean_executable_semantics_path_part_4.md#buffer-reuse-and-aliasing-slice-4-landed)
    - [Slices 1-4 profile, fixtures and mutations](lean_executable_semantics_path_part_4.md#slices-1-4-profile-fixtures-and-mutations)
    - [What slices 1-4 do not do](lean_executable_semantics_path_part_4.md#what-slices-1-4-do-not-do)
- [5. Remaining work, in dependency order](lean_executable_semantics_path_part_5.md#5-remaining-work-in-dependency-order)
  - [5.1 Beyond the bounded source fragment](lean_executable_semantics_path_part_5.md#51-beyond-the-bounded-source-fragment)
  - [5.2 Later: compiled and numerical refinement](lean_executable_semantics_path_part_5.md#52-later-compiled-and-numerical-refinement)
- [6. The landed admitted-core milestone](lean_executable_semantics_path_part_6.md#6-the-landed-admitted-core-milestone)

---

[Previous: Semantics introduction](README.md) | [Contents](README.md) | [Next: 1. Purpose, authority, and current position](lean_executable_semantics_path_part_1.md)
