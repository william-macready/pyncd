# Lean executable reference - 6. The landed admitted-core milestone

[Previous: 5. Remaining work, in dependency order](lean_executable_semantics_path_part_5.md) | [Contents](README.md) | [Next: Contents](lean_executable_semantics_path.md)

## In this part

- [6. The landed admitted-core milestone](#6-the-landed-admitted-core-milestone)

## 6. The landed admitted-core milestone

For the admitted exact-rational profile, a validated input, computational tensor
equality, complete ordered schedule, and supplied coordinate-rank certificate
now produce an inspectable finite execution with proved legal transitions, and:

```math
\begin{aligned}
\textcolor{#A87C28}{\mathsf{Success}}(\textcolor{#398B83}{\rho})
&\Longrightarrow
\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\{\textcolor{#398B83}{\rho}\}
\ \land\
\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{P}\textcolor{#398B83}{\mathclose{]\!]}}(\textcolor{#398B83}{\eta})=\textcolor{#398B83}{\rho}|_{\textcolor{#5688C7}{\mathrm{Out}}},\\
\textcolor{#A87C28}{\mathsf{Failed}}(\textcolor{#9D75C4}{o},\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})
&\Longrightarrow
\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})=\varnothing.
\end{aligned}
```

`run_ranked_dichotomy` proves that the actual default driver reaches one of
these outcomes. `result_model`, `result_unique`, and `result_denotation` refine
successful whole-store soundness; `result_failure` requires an event path
reached from validated initialization. It makes no no-model claim for arbitrary
debug states, blocking, or exhaustion. Invalid input is rejected before
initialization. Unsupported operations are outside the closed registry;
rank synthesis is not provided, and source admission and schedule construction exist only for the bounded fragment of Section 4.7.
The generic executor retains heterogeneous carriers; validation does not
establish the parked non-additive-input runtime fixture.

For the bounded source fragment, `sourceResult_model`, `sourceResult_unique`, and
`sourceResult_denotation` give the same success implications for programs
admitted from source, and `runSource_not_exhausted` shows that the
automatically scheduled default run is never exhausted.
`StatementPermutation.successful_results` adds that two complete rational
runs of a permuted source with equal inputs reach the same final store.

The endpoint is an executable realization of the specified equations, not
zero-seeded fixed-point iteration, a floating-point solver presented as exact
mathematics, or a proof that the existing production compiler already refines
the semantics.

---

[Previous: 5. Remaining work, in dependency order](lean_executable_semantics_path_part_5.md) | [Contents](README.md) | [Next: Contents](lean_executable_semantics_path.md)
