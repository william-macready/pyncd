# Lean executable reference - 2. One notation, two presentations

[Previous: 1. Purpose, authority, and current position](lean_executable_semantics_path_part_1.md) | [Contents](README.md) | [Next: 3. The category-theoretic organization](lean_executable_semantics_path_part_3.md)

## In this part

- [2. One notation, two presentations](#2-one-notation-two-presentations)
  - [Core admission and source elaboration](#core-admission-and-source-elaboration)

## 2. One notation, two presentations

Use the specification's notation throughout:
$\textcolor{#5688C7}{\Sigma}$ for declarations, $\textcolor{#5688C7}{\Gamma}$ for a variable context, $\textcolor{#5688C7}{\nu}$ for a
valuation, $\textcolor{#398B83}{\rho}$ for a complete environment, $\textcolor{#398B83}{\eta}$ for supplied inputs,
and $\textcolor{#A87C28}{\sigma}$ for a partial published store. A machine configuration is
$(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$. $\textcolor{#9D75C4}{s}$ is a statement identifier and $\textcolor{#9D75C4}{o}=(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})$ an occurrence.

The mathematics uses the same
[notation color key](tensor_logic_semantics.md#notation-color-key) as the
specification, throughout the equations and correspondence tables:

| Color | Semantic role |
| --- | --- |
| $\textcolor{#5688C7}{\text{Blue}}$ | Domains, signatures, index binding, and coordinate maps |
| $\textcolor{#9D75C4}{\text{Purple}}$ | Program syntax and source identities, including tagged occurrences |
| $\textcolor{#398B83}{\text{Teal}}$ | Denotational values, expression results, and model equations |
| $\textcolor{#A87C28}{\text{Amber}}$ | Reference execution, published stores, accumulators, and readiness |
| $\textcolor{#C16C86}{\text{Rose}}$ | Compiled execution and physical representation, reserved for later refinement |

Color follows meaning, not spelling. Local coordinate maps are blue, while
an expression such as $\textcolor{#9D75C4}{e}$ is purple. Scalar algebra,
generic category notation, and ordinary mathematical punctuation remain
neutral. Lean identifiers and code examples retain their literal spelling
and are not recolored; in particular, the Lean declaration parameter `σ`
must not be confused with the mathematical published store
$\textcolor{#A87C28}{\sigma}$. The labels also make the guide usable in
monochrome. Math colors require no custom macros or CSS; named operators use
`\mathop{\mathrm{Name}}\nolimits` rather than GitHub's blocked `\operatorname`.
Use VS Code's
built-in Markdown math preview, or a browser Markdown preview with KaTeX
or MathJax support, as described in the linked color key.

The specification fixes a scalar carrier $K$. Lean generalizes this to a
family `K : S -> Type`, allowing typed scalar sorts and heterogeneous primitive
signatures. To recover the specification's single-carrier fragment, specialize
to one sort. In formulas below, $K$ means that specialization, or the carrier
of the particular defined tensor being collected.

Recovering the full exact-semiring interpretation also requires choosing the
specified semiring operations as `ScalarOps` and supplying their laws where
needed. The general Lean interface does not enforce this identification.
The collection and soundness results use weaker additive hypotheses.

Two naming collisions must not obscure the correspondence: Lean's declaration
parameter `σ` represents mathematical **$\textcolor{#5688C7}{\Sigma}$**, not the published store
$\textcolor{#A87C28}{\sigma}$; Lean's registry parameter `r` is not the dependency rank
$r:\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}\to\mathbb N$.

| Mathematics | Lean representation | Specification |
| --- | --- | --- |
| Axis identity and extent | `Axis.uid`, `Axis.extent`; ordered `Shape := List Axis` | [3.1](tensor_logic_semantics_part_i.md#31-axes-and-identities), [4.1](tensor_logic_semantics_part_i.md#41-signatures-and-coordinate-domains) |
| $\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)$ | `Coord (σ.signature t).axes`, a product of bounded `Fin` coordinates; `Coord [] = Unit` | [4.1](tensor_logic_semantics_part_i.md#41-signatures-and-coordinate-domains) |
| Tensor value $\textcolor{#5688C7}{I}\to K$ | `Value K (.array s sh) = Coord sh.axes -> K s`; tensor signatures may also have rank zero | [4.2](tensor_logic_semantics_part_i.md#42-tensor-values), [13.2](tensor_logic_semantics_part_ii.md#132-value-types-and-primitive-signatures) |
| Address $(T,p)$ | Dependent pair `Address σ := (t : σ.Tensor) × Coord (σ.signature t).axes` | [5.2](tensor_logic_semantics_part_i.md#52-partial-stores-and-available-values) |
| Complete $\textcolor{#398B83}{\rho}$; partial $\textcolor{#A87C28}{\sigma}$ | `Store K σ`; `PartialStore K σ`, with `Option` at each typed cell | [5](tensor_logic_semantics_part_i.md#5-environments-and-stores) |
| $\textcolor{#5688C7}{\Sigma};\textcolor{#5688C7}{\Gamma};\textcolor{#5688C7}{D}\vdash \textcolor{#9D75C4}{E}:\textcolor{#5688C7}{\tau}$ | `Expr K σ r Γ τ` on an already admitted valuation type | [13](tensor_logic_semantics_part_ii.md#13-core-syntax-and-binding), [14](tensor_logic_semantics_part_ii.md#14-structural-well-formedness) |
| $\textcolor{#398B83}{\mathop{\mathrm{Result}}\nolimits}(\textcolor{#5688C7}{\tau})=\textcolor{#5688C7}{\tau}\sqcup\{\textcolor{#398B83}{\bot}\}$ | `Option (Value K τ)`; `some v` is success, `none` is $\textcolor{#398B83}{\bot}$ | [18.1](tensor_logic_semantics_part_iii.md#181-successful-and-undefined-results) |
| $\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}$ | `interpret ops ρ e γ` | [18](tensor_logic_semantics_part_iii.md#18-expression-interpretation-and-definedness) |
| $\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})$ | Membership in the list `footprint e γ`; repeated list entries do not change readiness | [23.2](tensor_logic_semantics_part_iv.md#232-read-footprints-of-expressions) |
| $\textcolor{#A87C28}{\mathop{\mathrm{Eval}}\nolimits}_{\textcolor{#A87C28}{\sigma}}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})$ when ready | `evalReady ops p e γ = .evaluated ...`; `.notReady` means wait | [23.3](tensor_logic_semantics_part_iv.md#233-stable-evaluation-from-a-partial-store) |

The representations and expression constructors are in
[`Types.lean`](../../leanncd/LeanNCD/Semantics/Types.lean) and
[`Expr.lean`](../../leanncd/LeanNCD/Semantics/Expr.lean).
`Declarations.uid` is injective: tensor identity is not string matching.
`Layout.enumerate : Fin count ≃ Coord sh` certifies a complete coordinate
enumeration, including zero-extent shapes.

### Core admission and source elaboration

In the core, Lean's `Γ` is a **type of valuations**, rather than a list of named
variables. Reduction extends it to `Γ × Fin n`; tabulation extends it to
`Γ × Coord sh.axes`. This realizes the lifted body domains. The `Source` layer
([Section 4.7](lean_executable_semantics_path_part_4.md#47-bounded-source-correspondence-and-differential-debugging))
adds identity-keyed valuations and admission for a bounded fragment, but there
is still no capture-avoiding substitution on expressions, and admission never
renames binders.

Likewise, `AdmittedRead` supplies a resolved bounded coordinate or a constant,
with a proof that its read policy agrees with that resolution. The
specification's bounded-read fragment uses the coordinate case. Constant and
remapped boundary reads are explicit extensions explored by
[the boundary-policy note](tensor_logic_boundary_policies.md), not silently
adopted clauses of the core specification. A rejecting read cannot inhabit
the admitted interface at that valuation.

Destinations are already bounded coordinates. These types establish admission
of the constructed objects. The `Source` layer checks malformed parsed source programs
(`TLProgram` ASTs) for its bounded fragment only; there is no runtime checker for arbitrary raw write
indices.

---

[Previous: 1. Purpose, authority, and current position](lean_executable_semantics_path_part_1.md) | [Contents](README.md) | [Next: 3. The category-theoretic organization](lean_executable_semantics_path_part_3.md)
