# Tensor Logic in PyRel

PyRel is an extension of Datalog that subsumes tensor logic: every tensor logic program can be expressed as a PyRel program, and PyRel adds recursive rules, aggregation, and arithmetic that go beyond what tensor logic specifies. This document describes the systematic translation from tensor logic equations to PyRel, using the examples in `einsum.py`.

---

## Representing Tensors

In tensor logic a tensor is a mathematical object — a function from index tuples to values. In PyRel a tensor is a **relation** whose columns are the index values plus a value column. A matrix S of shape 4×5 is declared as:

```python
S = model.Relationship(f"{Integer:i} {Integer:j} {Float:val}")
```

Each row `(i, j, val)` stores one entry S[i,j] = val. Index columns are typed (`Integer`, `String`, etc.); the value column is conventionally named `val` but is just another column with no special status.

For tensors whose tuples are computed rather than loaded from data, PyRel offers `model.Concept`, which creates objects with named attributes:

```python
R = model.Concept("result")
# ...
R.new(i=i, k=k, val=sum(vs*vs2).per(i,k))
```

`Relationship` and `Concept` are semantically equivalent for the purposes of tensor computation; `Concept` is more convenient when the output schema is not known in advance.

---

## Core Translation Rules

The table below maps each tensor logic construct to its PyRel equivalent. The sections that follow give a worked example for each.

| Tensor logic construct | PyRel equivalent |
|---|---|
| Join on shared index | Share a variable across patterns in `where(...)` |
| Contraction (sum over non-output index) | `sum(expr).per(output_indices)` |
| Plain output (no contraction) | Arithmetic on value variables directly; no `.per()` |
| Repeated index (diagonal / trace) | Same variable in two positions: `S(i, i, vs)` |
| Index arithmetic | Expressions in index positions: `S(x+i, y+j, vs)` |
| Elementwise nonlinearity | Applied to value expression: `sigm(...)`, `relu(...)` |
| Intermediate named value | Walrus operator inside `where(...)`: `tmp := expr` |

---

## Worked Examples

### 1. Trace — `S[i,i]`

Select the diagonal entries of S and sum them.

**Tensor logic**
```
scalar = S[i,i]          -- sum over diagonal
```

**PyRel**
```python
i, vs = Integer.ref(), Float.ref()
where(S(i, i, vs)).select(sum(vs))
```

Placing the same variable `i` in both index positions of `S` constrains the join to rows where the two indices are equal — the diagonal. The result has no output indices, so it is a scalar.

---

### 2. Matrix Self-Product — `R[i,k] = S[i,j] S[k,j]`

Join two copies of S on their second index, contract j, retain i and k.

**Tensor logic**
```
R[i,k] = S[i,j] S[k,j]
```

**PyRel**
```python
j, k, vs, vs2 = Integer.ref(), Integer.ref(), Float.ref(), Float.ref()
where(S(i,j,vs), S(k,j,vs2)).define(
    R.new(i=i, k=k, val=sum(vs*vs2).per(i,k))
)
```

Sharing `j` between the two `S` patterns performs the join. `sum(...).per(i,k)` contracts over every variable not named in `.per()` — here `j` — and retains `i` and `k` as output indices.

An alternative attribute-access style is semantically identical:

```python
S2 = S.ref()
where(S["j"] == S2["j"]).define(
    R.new(i=S["i"], k=S2["i"], val=sum(S["val"]*S2["val"]).per(S["i"], S2["i"]))
)
```

The positional style is more concise; the attribute style is closer to SQL and may read more naturally when joining a relation against itself.

---

### 3. Single Neural Net Layer — `R[i] = sigm(S[i,j] U[j])`

Dot product of each row of S with vector U, apply sigmoid.

**Tensor logic**
```
R[i] = sigm(S[i,j] U[j])
```

**PyRel**
```python
j, vs, vu = Integer.ref(), Float.ref(), Float.ref()
where(S(i,j,vs), U(j,vu)).define(
    R.new(i=i, val=sigm(sum(vs*vu).per(i)))
)
```

Sharing `j` joins S and U on their common index. The contraction `sum(vs*vu).per(i)` sums the products over `j` for each fixed `i`. The nonlinearity `sigm(...)` wraps the entire aggregated expression and is applied elementwise to the scalar result at each `i`.

---

### 4. Broadcast Addition — `R[i,j,k] = T[i,j,k] + S[i,j] + U[k]`

Add three tensors of different ranks by broadcasting over shared indices.

**Tensor logic**
```
R[i,j,k] = T[i,j,k] + S[i,j] + U[k]
```

**PyRel**
```python
vt, vs, vu = Float.ref(), Float.ref(), Float.ref()
where(T(i,j,k,vt), S(i,j,vs), U(k,vu)).define(
    R.new(i=i, j=j, k=k, val=vt+vs+vu)
)
```

Each triple `(i,j,k)` uniquely determines one entry in each of T, S, and U (S via `i,j`; U via `k`). Because the join already pins every variable, no aggregation is needed — `val=vt+vs+vu` is a plain arithmetic expression with no `.per()`. This is how broadcasting is expressed in PyRel: the index structure of the join does the alignment.

---

### 5. Convolution — `R[x,y] = S[x,y] + S[x+i,y+j] K[i,j]`

Compute a sum of a tensor with a locally weighted sum of its shifted copies.

**Tensor logic**
```
R[x,y] = S[x,y] + S[x+i,y+j] K[i,j]
```

**PyRel**
```python
x, y, i, j = Integer.ref(), Integer.ref(), Integer.ref(), Integer.ref()
vs, vs2, vk = Float.ref(), Float.ref(), Float.ref()
( where(S(x,y,vs), K(i,j,vk), S(x+i,y+j,vs2))
    .define(R.new(i=x, j=y, val=vs+sum(vs2*vk).per(x,y))) )
```

Index arithmetic appears directly in the pattern: `S(x+i, y+j, vs2)` matches the entry of S at position (x+i, y+j). The kernel K is joined on `i,j` and its product with the shifted S entry is summed over `i` and `j` via `.per(x,y)`. The unshifted `S[x,y]` value `vs` is added outside the aggregation.

---

### 6. Complex Contraction with Intermediates — `R[i,k] = T[i,j,k] * log(|S[i,j]/U[j]|)`

Contract over j after computing a nonlinear function of two tensors.

**Tensor logic**
```
R[i,k] = T[i,j,k] * log(abs(S[i,j] / U[j]))
```

**PyRel**
```python
vt, vs, vu = Float.ref(), Float.ref(), Float.ref()
where(T(i,j,k,vt), S(i,j,vs), U(j,vu),
      atmp := log(abs(vs/vu))).define(
    R.new(i=i, k=k, val=sum(vt*atmp).per(i,k))
)
```

The walrus operator `:=` inside `where(...)` binds an intermediate value `atmp` to `log(abs(vs/vu))` for each joined tuple. This value is then available as a variable in the `.define(...)` expression. Intermediates can be chained — each `:=` binding is in scope for all subsequent patterns and the `.define(...)`.

---

## Translating `*`-Indexed Equations (Virtual Indices)

Tensor logic's `*t` notation marks a **virtual index**: the tensor is updated in-place at each step and no storage is allocated for the t dimension. The canonical example is a recurrent neural network:

**Tensor logic**
```
R[0, j]    = U[j]
R[l+1, i]  = sigm(W[l,i,j] R[l,j])
```

PyRel has no `*` notation. Instead, recurrence is expressed using an explicit integer layer index and two separate rules — a base case and a recursive case:

```python
R = model.Relationship(f"{Integer:layer} {Integer:dim} {Float:val}")
l, i, j = Integer.ref(), Integer.ref(), Integer.ref()
vr, vw, vu = Float.ref(), Float.ref(), Float.ref()

# base case: R[0, j] = U[j]
where(U(j, vu)).define(R(0, j, vu))

# recursive case: R[l+1, i] = sigm(W[l,i,j] * R[l,j])
where(R(l,i,vr), W(l,i,j,vw)).define(
    R(l+1, i, sigm(sum(vw*vr).per(j,l)))
)
```

The difference from tensor logic is representational: tensor logic's `*t` discards intermediate states; PyRel's integer layer index stores all of them. In practice this distinction matters for memory but not for the computed values at the final layer.

Note: as of writing, the recursive rule above does not execute correctly in PyRel — recursive aggregation through a self-referential `Relationship` is a known open issue.

---

## Translating `.`-Indexed Equations (Normalization Axes)

Tensor logic's `t.` notation marks the **normalization axis**: the named function (softmax, layer norm) is applied as a whole-vector operation over that index for each combination of the others. There is no equivalent built-in syntax in PyRel; `.`-indexed operations must be expanded manually.

**Tensor logic**
```
R[i., j, k] = softmax(T[i, j, k])
```

The `i.` on the LHS means: for each fixed (j,k), apply softmax to the vector of T values indexed by i.

**PyRel** (numerically stable expansion)
```python
i, j, k = Integer.ref(), Integer.ref(), Integer.ref()
vt = Float.ref()
( where(T(i,j,k,vt),
        tmaxjk := max(vt).per(j,k),
        texpjk := exp(vt - tmaxjk),
        z      := sum(texpjk).per(j,k))
    .define(R.new(i=i, j=j, k=k, val=texpjk/z)) )
```

The expansion has three steps, each introduced via `:=`:

1. `tmaxjk` — the maximum of T over i for each (j,k), used for numerical stability
2. `texpjk` — the shifted exponential `exp(T[i,j,k] - max)`
3. `z` — the normalizing sum of shifted exponentials over i for each (j,k)

The final value `texpjk/z` is the softmax. In tensor logic, a single `.`-suffix captures all three steps; in PyRel they must be spelled out explicitly. Any vector normalization that depends on an entire slice — softmax, log-sum-exp, layer norm — requires this kind of manual expansion.

---

## Limitations and Differences

**No dimension type-checking.** PyRel does not verify that two tensors joined on a shared index have the same axis length. Mismatched dimensions produce empty or wrong results silently.

**No covariant/contravariant distinction.** Tensor logic (and einsum) treat all indices as untyped positions. PyRel follows the same convention.

**Two equivalent syntactic styles.** PyRel supports both positional pattern matching (`S(i,j,vs)`) and attribute access (`S["j"]`). They are semantically identical; the positional style is more concise for tensor work.

**`Concept` vs. `Relationship`.** `model.Concept` creates objects with named attributes and is convenient for derived tensors with a computed schema. `model.Relationship` is more natural when the schema is fixed and tuples are asserted directly. Both support the same `where(...).define(...)` pattern.

**`*`-indexed recurrence is not yet supported.** The recursive aggregation pattern required to implement multi-layer networks through a self-referential relation does not currently execute correctly in PyRel.

**`.`-indexed normalization requires manual expansion.** Tensor logic's normalization axis notation has no PyRel counterpart and must be expanded into explicit intermediate bindings.
