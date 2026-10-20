# Tensor Logic semantics - Notation reference and bibliography

[Previous: Part V: Compilation and refinement](tensor_logic_semantics_part_v.md) | [Contents](README.md) | [Next: Contents](tensor_logic_semantics.md)

## In this part

- [35. Compact notation reference](#35-compact-notation-reference)
  - [Domains, signatures, and index binding](#domains-signatures-and-index-binding)
  - [Program syntax and source identities](#program-syntax-and-source-identities)
  - [Scalar foundations, denotational values, and equations](#scalar-foundations-denotational-values-and-equations)
  - [Reference execution and readiness](#reference-execution-and-readiness)
  - [Compiled execution and physical representation](#compiled-execution-and-physical-representation)
- [References and related documents](#references-and-related-documents)

## 35. Compact notation reference

The groups follow the reading-guide color key. Scalar algebra and generic
mathematical notation remain neutral; mixed expressions retain the colors
of their individual components.

### Domains, signatures, and index binding

| Symbol | Meaning |
| --- | --- |
| $[n]$ | Finite ordinal $\{0,\ldots,n-1\}$ |
| $()$ | Empty tuple; the sole rank-zero coordinate |
| $a,\textcolor{#5688C7}{I}_a,n_a$ | Axis, its coordinate range, and extent |
| $\textcolor{#5688C7}{\Gamma},\textcolor{#5688C7}{\nu}$ | Index context and valuation |
| $\textcolor{#5688C7}{\mathop{\mathrm{Val}}\nolimits}(\textcolor{#5688C7}{\Gamma})$ | All valuations for that context |
| $\textcolor{#5688C7}{\Gamma}_{\mathrm{all}}$ | All distinct variables of a pure einsum with resolved domains |
| $\textcolor{#5688C7}{L},\textcolor{#5688C7}{L}_r$ | Output and operand index strings |
| $J_{\textcolor{#5688C7}{L}},\textcolor{#5688C7}{\pi}_{\textcolor{#5688C7}{L}}$ | A string's coordinate domain and projection from a global valuation |
| $\textcolor{#5688C7}{\mathop{\mathrm{vars}}\nolimits}(\textcolor{#5688C7}{\Gamma})$ | Variable-identity set of an index context |
| $\textcolor{#5688C7}{D}^{+j}$ | A valuation domain lifted over a fresh binder |
| $\textcolor{#5688C7}{D}_{\textcolor{#9D75C4}{s}}$ | Admissible free-variable valuations for statement $\textcolor{#9D75C4}{s}$ |
| $\textcolor{#5688C7}{\Sigma}$ | Tensor signature |
| $\textcolor{#5688C7}{\mathrm{In}},\textcolor{#5688C7}{\mathrm{Def}},\textcolor{#5688C7}{\mathrm{Out}}$ | Input, defined, and designated output identifiers |
| $\textcolor{#5688C7}{\mathop{\mathrm{Coord}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}(T)$ | Coordinate domain of tensor $T$ |
| $(T,p)$ | Tensor address |
| $\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{In}}},\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Def}}}$ | Input and defined address partitions |
| $\textcolor{#5688C7}{\mathop{\mathrm{Addr}}\nolimits}_{\textcolor{#5688C7}{\mathrm{Out}}}$ | All declared output coordinates |
| $\textcolor{#5688C7}{\tau},\textcolor{#9D75C4}{\mathcal{F}}$ | Expression value type and primitive registry |
| $\textcolor{#5688C7}{\Sigma};\textcolor{#5688C7}{\Gamma};\textcolor{#5688C7}{D}\vdash \textcolor{#9D75C4}{E}:\textcolor{#5688C7}{\tau}$ | Structural expression judgment under a signature, index context, and admissible valuation domain |

### Program syntax and source identities

| Symbol | Meaning |
| --- | --- |
| $\textcolor{#9D75C4}{\mathop{\mathrm{FV}}\nolimits}(\textcolor{#9D75C4}{E})$ | Free variables of an expression |
| $\textcolor{#9D75C4}{E}[i:=\textcolor{#9D75C4}{e}]$ | Capture-avoiding index substitution |
| $\textcolor{#9D75C4}{\mathop{\mathrm{dst}}\nolimits}(\textcolor{#9D75C4}{o})$ | Destination address of contribution occurrence $\textcolor{#9D75C4}{o}$ |
| $\textcolor{#5688C7}{\phi}_{\textcolor{#9D75C4}{s}}$ | Statement's write map |
| $\textcolor{#9D75C4}{E}_{\textcolor{#9D75C4}{s}}$ | Statement's contribution expression |
| $(\textcolor{#9D75C4}{s},\textcolor{#5688C7}{\nu})$ | Tagged contribution occurrence |
| $\textcolor{#9D75C4}{\mathcal{O}}_{\textcolor{#9D75C4}{P}}$ | All contribution occurrences of program $\textcolor{#9D75C4}{P}$ |
| $\textcolor{#9D75C4}{\mathcal{C}}_{\textcolor{#9D75C4}{P}}(T,p)$ | Occurrences addressing coordinate $p$ of $T$ |
| $\textcolor{#9D75C4}{\mathop{\mathrm{tab}}\nolimits},\textcolor{#9D75C4}{\mathop{\mathrm{at}}\nolimits}$ | Array construction and scalar coordinate selection |
| $C_b,B_{\textcolor{#9D75C4}{s}}$ | Contracted variables of a surface term and elaborated additive body |

### Scalar foundations, denotational values, and equations

| Symbol | Meaning |
| --- | --- |
| $K$ | Scalar carrier |
| $\mathcal{K}$ | Scalar semiring structure |
| $\oplus,\otimes$ | Contribution/reduction combination and multiplication |
| $0_K,1_K$ | Additive and multiplicative identities |
| $\textcolor{#398B83}{V}_{\textcolor{#5688C7}{L}}$ | Canonical pure-einsum result tensor |
| $\textcolor{#398B83}{\rho},\textcolor{#398B83}{\eta}$ | Complete tensor environment and input environment |
| $\textcolor{#398B83}{\mathop{\mathrm{Result}}\nolimits}(\textcolor{#5688C7}{\tau}),\textcolor{#398B83}{\bot}$ | Successful typed values or an undefined result |
| $\textcolor{#398B83}{\mathopen{[\![}} \textcolor{#9D75C4}{E}\textcolor{#398B83}{\mathclose{]\!]}}_{\textcolor{#398B83}{\rho},\textcolor{#5688C7}{\nu}}\downarrow v$ | Expression interpretation is defined with value $v$ |
| $\textcolor{#398B83}{\mathop{\mathrm{lift}}\nolimits}_2$ | Strict lifting of a scalar binary operation to results |
| $\textcolor{#398B83}{\rho}_{\textcolor{#A87C28}{\sigma}}$ | Complete environment reconstructed from a complete store |
| $\textcolor{#398B83}{\zeta}$ | Decoded output environment |
| $\textcolor{#398B83}{\Delta}_G$ | Exact fiber aggregate for a successful ready occurrence group |
| $\textcolor{#398B83}{\mathop{\mathrm{AdmEnv}}\nolimits}(\textcolor{#9D75C4}{P})$ | Complete environments on which all actual contributions are defined |
| $\textcolor{#398B83}{V}_{\textcolor{#9D75C4}{s}}^{\textcolor{#398B83}{\rho}}$ | Contribution tensor of statement $\textcolor{#9D75C4}{s}$ in environment $\textcolor{#398B83}{\rho}$ |
| $\textcolor{#398B83}{\mathop{\mathrm{Collect}}\nolimits}_{\textcolor{#9D75C4}{P}}(\textcolor{#398B83}{\rho})$ | Values collected for all defined tensors |
| $\textcolor{#398B83}{\Phi}_{\textcolor{#9D75C4}{P}}$ | Partial equation operator preserving inputs and collecting defined tensors |
| $\textcolor{#398B83}{\mathop{\mathrm{Input}}\nolimits}_{\textcolor{#5688C7}{\Sigma}},\textcolor{#398B83}{\mathop{\mathrm{Output}}\nolimits}_{\textcolor{#5688C7}{\Sigma}}$ | Value environments on the program's designated input and output identifiers |
| $\textcolor{#398B83}{\mathop{\mathrm{AdmInput}}\nolimits}(\textcolor{#9D75C4}{P})$ | Well-typed inputs admitting exactly one complete model |
| $\mathbf{1}_{\textcolor{#9D75C4}{Q}}$ | Iverson value of predicate $\textcolor{#9D75C4}{Q}$ |
| $\textcolor{#398B83}{\delta}_J$ | Equality-indicator tensor on $J\times J$ |
| $\mathbf{1}_J$ | All-ones tensor on coordinate domain $J$ |
| $\textcolor{#398B83}{\mathcal{D}}_f$ | Domain of definition of primitive $f$ |
| $H_l$ | Logical history slice $H[:,l]$ |
| $\textcolor{#398B83}{\mathopen{[\![}}\cdot\textcolor{#398B83}{\mathclose{]\!]}}$ | Interpretation brackets, with parameters as specified |
| $\textcolor{#398B83}{\mathop{\mathrm{Models}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$ | Complete environments satisfying the collected equations on inputs $\textcolor{#398B83}{\eta}$ |

### Reference execution and readiness

| Symbol | Meaning |
| --- | --- |
| $\textcolor{#A87C28}{\sigma}$ | Partial store of available coordinate values |
| $\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu}),\textcolor{#A87C28}{\mathop{\mathrm{Read}}\nolimits}(\textcolor{#9D75C4}{o})$ | Read footprints of an expression instance and an occurrence |
| $\textcolor{#A87C28}{\mathop{\mathrm{Dep}}\nolimits}(a),r$ | Coordinate dependency set and strictly increasing dependency rank |
| $\textcolor{#A87C28}{\sigma}\textcolor{#A87C28}{\sqsubseteq}\textcolor{#398B83}{\rho}$ | The complete environment agrees with every published store value |
| $\textcolor{#A87C28}{\mathop{\mathrm{Eval}}\nolimits}_{\textcolor{#A87C28}{\sigma}}(\textcolor{#9D75C4}{E},\textcolor{#5688C7}{\nu})$ | Expression result from an available footprint, independent of complete extension |
| $\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U}$ | Defined-coordinate accumulators and pending occurrence set |
| $\textcolor{#A87C28}{\mathop{\mathrm{Init}}\nolimits}(\textcolor{#9D75C4}{P},\textcolor{#398B83}{\eta})$ | Initial store, zero accumulators, and all pending occurrences |
| $\textcolor{#A87C28}{\mathsf{Failed}}(\textcolor{#9D75C4}{o},\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{\alpha},\textcolor{#A87C28}{U})$ | Terminal undefined-contribution error with its occurrence and state |
| $\textcolor{#A87C28}{\mu}$ | Number of pending occurrences plus unpublished defined coordinates |
| $\textcolor{#A87C28}{\mathsf{pub}}(a),\textcolor{#A87C28}{\mathsf{acc}}(a)$ | Published-value and unpublished-accumulator resource identities |
| $\textcolor{#A87C28}{\mathop{\mathrm{Need}}\nolimits}_{\mathrm{pub}}(\textcolor{#A87C28}{\sigma},\textcolor{#A87C28}{U})$ | Published coordinates required by remaining contributions or outputs |
| $\textcolor{#A87C28}{\mathsf{Conf}},\textcolor{#A87C28}{\longrightarrow},\textcolor{#A87C28}{\Downarrow}$ | Machine configuration, execution-step relation, and successful termination |

### Compiled execution and physical representation

| Symbol | Meaning |
| --- | --- |
| $\textcolor{#C16C86}{\mathcal{B}},m_{\textcolor{#C16C86}{\beta}}$ | Physical buffer identifiers and their capacities |
| $\textcolor{#C16C86}{\mathop{\mathrm{Slot}}\nolimits}_{\textcolor{#C16C86}{\mathcal{B}}},\textcolor{#C16C86}{\xi}$ | Physical slot set and a slot $(\textcolor{#C16C86}{\beta},k)$ |
| $\textcolor{#C16C86}{M}$ | Partial exact-value memory on physical slots |
| $\textcolor{#C16C86}{\Pi},\textcolor{#C16C86}{\kappa}_t$ | Execution plan and a kernel command with logical annotations |
| $\textcolor{#C16C86}{\mathsf{Accumulate}}(G),\textcolor{#C16C86}{\mathsf{Publish}}(B),\textcolor{#C16C86}{\mathsf{Storage}}(\textcolor{#C16C86}{\theta})$ | Batched contribution, block publication, and representation-only action contracts |
| $\textcolor{#C16C86}{\mathsf{C}},\textcolor{#C16C86}{\mathsf{pc}},\textcolor{#C16C86}{\chi}$ | Concrete state, command position, and plan control/layout metadata |
| $\textcolor{#C16C86}{\lambda}_{\textcolor{#C16C86}{\mathsf{C}}}$ | Partial resource-to-slot layout view |
| $\textcolor{#C16C86}{\mathcal{R}}_{\textcolor{#C16C86}{\Pi}}$ | Concrete/reference representation relation |
| $\textcolor{#C16C86}{\mathop{\mathrm{Start}}\nolimits}_{\textcolor{#C16C86}{\Pi}},\textcolor{#C16C86}{\mathop{\mathrm{Decode}}\nolimits}_{\textcolor{#C16C86}{\Pi}}$ | Concrete initialization and whole-output decoding |
| $\textcolor{#9D75C4}{P}\vdash\textcolor{#C16C86}{\Pi}\ \textcolor{#C16C86}{\mathsf{valid}}$ | Valid plan: certified schedule, representation, and kernel behavior (Definition 31.1) |
| $\textcolor{#C16C86}{\longrightarrow}_{\textcolor{#C16C86}{\Pi}},\textcolor{#C16C86}{\Downarrow}_{\textcolor{#C16C86}{\Pi}}$ | Concrete plan-step and decoded successful-execution relations |
| $\textcolor{#C16C86}{\mathsf{PlanFailed}}(\textcolor{#9D75C4}{o})$ | Terminal concrete failure matched to an undefined source occurrence |

## References and related documents

- Pedro Domingos, [*Tensor Logic: The Language of AI*](https://arxiv.org/html/2510.12269v3).
  Its additive convention motivates this specification; the definitions and
  implementation correspondence here must be stated independently.
- [*The Syntax and Semantics of einsum*](https://arxiv.org/html/2509.20020).
  Sections [3](tensor_logic_semantics_part_i.md#3-axes-index-variables-and-valuations)-[4](tensor_logic_semantics_part_i.md#4-tensor-signatures-coordinates-and-values) provide the pure-einsum syntax and global-position semantics;
  Sections [5](tensor_logic_semantics_part_i.md#5-environments-and-stores)-[7](tensor_logic_semantics_part_i.md#7-free-indices-contraction-and-broadcasting) supply algebraic, nesting, delta, and neutral-operand results.
  [Section 17](tensor_logic_semantics_part_ii.md#17-pure-einsum-semantics-and-transformation-foundations) adapts the relevant foundations to this document's conventions.
- [Tensor logic and einsum](../einsum_tensor_logic.md).
- [Integer constants and affine index arithmetic](../index_arithmetic.md).
- [Iteration in tensor logic](../iteration.md).

Related repository documents describe existing designs or implementations.
They are context, not substitutes for the definitions in this specification.

---

[Previous: Part V: Compilation and refinement](tensor_logic_semantics_part_v.md) | [Contents](README.md) | [Next: Contents](tensor_logic_semantics.md)
