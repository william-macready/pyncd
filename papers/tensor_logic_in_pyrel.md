# Tensor Logic in PyRel

[PyRel](https://docs.relational.ai) is an extension of Datalog that subsumes tensor logic: every tensor logic program can be expressed as a PyRel program, with PyRel adding recursive rules, aggregation, and arithmetic beyond what tensor logic specifies. This document describes the translation, using examples from `einsum.py`.

---

## Representing Tensors

In PyRel, a tensor is a **relation** whose columns are the index values plus a value column. A matrix S is declared as:

```python
S = model.Relationship(f"{Integer:i} {Integer:j} {Float:val}")
```

Each row `(i, j, val)` stores one entry S[i,j] = val; the size of the matrix is determined by the tuples that populate the relation. Index columns are typed (`Integer`, `String`, etc.); `val` is a convention, not a special column.

PyRel also offers `model.Concept`, which creates objects with named attributes:

```python
R = model.Concept("result")
R.new(i=i, k=k, val=sum(vs*vs2).per(i,k))
```

`Relationship` and `Concept` are semantically equivalent; `Concept` is more convenient when the output schema is computed.

---

## Core Translation Rules

| Tensor logic construct | PyRel equivalent |
| --- | --- |
| Join on shared index | Share a variable across patterns in `where(...)` |
| Contraction (sum over non-output index) | `sum(expr).per(output_indices)` |
| Plain output (no contraction) | Arithmetic on value variables; no `.per()` |
| Repeated index (diagonal / trace) | Same variable in two positions: `S(i, i, vs)` |
| Index arithmetic | Expressions in index positions: `S(x+i, y+j, vs)` |
| Elementwise nonlinearity | Applied to value expression: `sigm(...)`, `relu(...)` |
| Intermediate named value | Walrus operator inside `where(...)`: `tmp := expr` |

---

## Worked Examples

### 1. Trace — `S[i,i]`

```text
scalar = S[i,i]
```

```python
i, vs = Integer.ref(), Float.ref()
where(S(i, i, vs)).select(sum(vs))
```

Using the same variable `i` in both positions constrains the match to diagonal rows. No output indices means a scalar result.

---

### 2. Matrix Self-Product — `R[i,k] = S[i,j] S[k,j]`

```text
R[i,k] = S[i,j] S[k,j]
```

```python
j, k, vs, vs2 = Integer.ref(), Integer.ref(), Float.ref(), Float.ref()
where(S(i,j,vs), S(k,j,vs2)).define(
    R.new(i=i, k=k, val=sum(vs*vs2).per(i,k))
)
```

Sharing `j` performs the join; `.per(i,k)` contracts over `j` and retains `i`,`k`.

An attribute-access style is semantically identical:

```python
S2 = S.ref()
where(S["j"] == S2["j"]).define(
    R.new(i=S["i"], k=S2["i"], val=sum(S["val"]*S2["val"]).per(S["i"], S2["i"]))
)
```

The positional style is more concise; attribute access reads more naturally when joining a relation against itself.

---

### 3. Single Neural Net Layer — `R[i] = sigm(S[i,j] U[j])`

```text
R[i] = sigm(S[i,j] U[j])
```

```python
j, vs, vu = Integer.ref(), Float.ref(), Float.ref()
where(S(i,j,vs), U(j,vu)).define(
    R.new(i=i, val=sigm(sum(vs*vu).per(i)))
)
```

Shared `j` joins S and U; `sum(vs*vu).per(i)` contracts over `j` for each `i`; `sigm` is applied elementwise to the result.

---

### 4. Broadcast Addition — `R[i,j,k] = T[i,j,k] + S[i,j] + U[k]`

```text
R[i,j,k] = T[i,j,k] + S[i,j] + U[k]
```

```python
vt, vs, vu = Float.ref(), Float.ref(), Float.ref()
where(T(i,j,k,vt), S(i,j,vs), U(k,vu)).define(
    R.new(i=i, j=j, k=k, val=vt+vs+vu)
)
```

The join on shared indices uniquely pins every value, so no `.per()` is needed. Broadcasting is handled by the index structure of the join.

---

### 5. Convolution — `R[x,y] = S[x,y] + S[x+i,y+j] K[i,j]`

```text
R[x,y] = S[x,y] + S[x+i,y+j] K[i,j]
```

```python
x, y, i, j = Integer.ref(), Integer.ref(), Integer.ref(), Integer.ref()
vs, vs2, vk = Float.ref(), Float.ref(), Float.ref()
( where(S(x,y,vs), K(i,j,vk), S(x+i,y+j,vs2))
    .define(R.new(i=x, j=y, val=vs+sum(vs2*vk).per(x,y))) )
```

Index arithmetic appears directly in patterns: `S(x+i, y+j, vs2)` matches S at the shifted position. K is contracted over `i,j` via `.per(x,y)`; the unshifted value `vs` is added outside the aggregation.

---

### 6. Complex Contraction with Intermediates — `R[i,k] = T[i,j,k] * log(|S[i,j]/U[j]|)`

```text
R[i,k] = T[i,j,k] * log(abs(S[i,j] / U[j]))
```

```python
vt, vs, vu = Float.ref(), Float.ref(), Float.ref()
where(T(i,j,k,vt), S(i,j,vs), U(j,vu),
      atmp := log(abs(vs/vu))).define(
    R.new(i=i, k=k, val=sum(vt*atmp).per(i,k))
)
```

`:=` binds an intermediate value for each joined tuple, available in all subsequent patterns and the `.define(...)`. Intermediates can be chained.

---

## Translating `*`-Indexed Equations (Virtual Indices)

Tensor logic's `*t` updates a tensor in-place with no storage for the t dimension. PyRel has no `*` notation; recurrence uses an explicit integer index with base and recursive rules:

```text
R[0, j]   = U[j]
R[l+1, i] = sigm(W[l,i,j] R[l,j])
```

```python
R = model.Relationship(f"{Integer:layer} {Integer:dim} {Float:val}")
l, i, j = Integer.ref(), Integer.ref(), Integer.ref()
vr, vw, vu = Float.ref(), Float.ref(), Float.ref()

where(U(j, vu)).define(R(0, j, vu))
where(R(l,i,vr), W(l,i,j,vw)).define(R(l+1, i, sigm(sum(vw*vr).per(j,l))))
```

PyRel stores all intermediate layers rather than discarding them; this affects memory but not the final values.

**Note:** the recursive rule above does not currently execute correctly — recursive aggregation through a self-referential `Relationship` is a known open issue.

---

## Translating `.`-Indexed Equations (Normalization Axes)

Tensor logic's `t.` applies a whole-vector normalization over that index for each combination of the others. PyRel has no built-in equivalent; `.`-indexed operations must be expanded manually.

```text
R[i., j, k] = softmax(T[i, j, k])
```

```python
i, j, k = Integer.ref(), Integer.ref(), Integer.ref()
vt = Float.ref()
( where(T(i,j,k,vt),
        tmaxjk := max(vt).per(j,k),
        texpjk := exp(vt - tmaxjk),
        z      := sum(texpjk).per(j,k))
    .define(R.new(i=i, j=j, k=k, val=texpjk/z)) )
```

The three `:=` steps are: (1) per-slice max for numerical stability, (2) shifted exponential, (3) normalizing sum. Tensor logic's single `.`-suffix abstracts all three. Any slice-dependent normalization — softmax, log-sum-exp, layer norm — requires this expansion in PyRel.

---

## Limitations and Differences

**No dimension type-checking.** Mismatched axis lengths on a shared index produce empty or wrong results silently.

**No covariant/contravariant distinction.** All indices are untyped positions, as in einsum.

**Two syntactic styles.** Positional matching (`S(i,j,vs)`) and attribute access (`S["j"]`) are semantically identical; the positional style is more concise for tensor work.

**`Concept` vs. `Relationship`.** Both support `where(...).define(...)`; `Concept` is convenient for derived tensors with a computed schema, `Relationship` for fixed-schema data.

**`*`-indexed recurrence not yet supported.** Recursive aggregation through a self-referential relation does not currently execute correctly.

**`.`-indexed normalization requires manual expansion.** No built-in normalization axis syntax; must be written as explicit intermediate bindings.
