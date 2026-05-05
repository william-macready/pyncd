import numpy as np
import pandas as pd
from relationalai.semantics import (
    Model, Float, Integer, define, select, where )
from relationalai.semantics.std.aggregates import sum, max
from relationalai.semantics.std.math import maximum, exp, log, abs
import relationalai.semantics.std.common as common

# testing einsum notation in pyrel
# like einsum we ignore whether dimensions are covariant/contravariant
# no type-checking of index dimensions is done

model = Model("tensor")
rng = np.random.default_rng(42)

def relu(x): return maximum(0.0, x)
def sigm(x): return 1.0/(1.0+exp(-x))

# logical 2x2
Neigh = model.Relationship(f"{Integer:i} {Integer:j}")
rows = [(2*i-1, 2*j-1) for i in range(2) for j in range(2)]
df = pd.DataFrame(rows)
src = model.data(df)
model.define(Neigh(src[0], src[1]))

# numerical 2x2
K = model.Relationship(f"{Integer:i} {Integer:j} {Float:val}")
rows = [(i, j, float(v)) for (i, j), v in np.ndenumerate(rng.normal(0,1,(2, 2)))]
df = pd.DataFrame(rows)
src = model.data(df)
model.define(K(src[0], src[1], src[2]))

# numerical S is 4×5
S = model.Relationship(f"{Integer:i} {Integer:j} {Float:val}")
rows = [(i, j, float(v)) for (i, j), v in np.ndenumerate(rng.normal(0,1,(4, 5)))]
df = pd.DataFrame(rows)
src = model.data(df)
model.define(S(src[0], src[1], src[2]))

# numerical T is 2×3×4
T = model.Relationship(f"{Integer:i} {Integer:j} {Integer:k} {Float:val}")
rows = [(i, j, k, float(v)) for (i, j, k), v in np.ndenumerate(rng.normal(0,1,(2, 3, 4)))]
df = pd.DataFrame(rows)
src = model.data(df)
model.define(T(src[0], src[1], src[2], src[3]))

# numerical W is 4x5x5
W = model.Relationship(f"{Integer:i} {Integer:j} {Integer:k} {Float:val}")
rows = [(i, j, k, float(v)) for (i, j, k), v in np.ndenumerate(rng.normal(0,1,(4, 5, 5)))]
df = pd.DataFrame(rows)
src = model.data(df)
model.define(W(src[0], src[1], src[2], src[3]))

# numerical U is 5x1
U = model.Relationship(f"{Integer:i} {Float:val}")
rows = [(i, float(v)) for i, v in enumerate(rng.normal(0,1,5))]
df = pd.DataFrame(rows)
src = model.data(df)
model.define(U(src[0], src[1]))

# print("--- original tensors ---")
# print("Neigh:")
# select(Neigh[0], Neigh[1]).inspect()
# print("K:")
# select(K[0], K[1], K[2]).inspect()
# print("S:")
# select(S[0], S[1], S[2]).inspect()
# print("T:")
# select(T[0], T[1], T[2], T[3]).inspect()
# print("U:")
# select(U[0], U[1]).inspect()

# R = model.Relationship(f"{Integer:layer} {Integer:dim} {Float:val}")
# d, vr = Integer.ref(), Float.ref()
# where(d==common.range(3)).define(R(0, d, d))
# where(R(0,d,vr)).define(R(1, d, sum(vr)))
# select(R[0], R[1], R[2]).inspect()


print("--- einsum examples ---")                   
print("S[i,i]:")
i, vs = Integer.ref(), Float.ref()
where(S(i,i,vs)).select(sum(vs)).inspect()
# where(S["i"] == S["j"]).select(sum(S["val"])).inspect()

print("R[i,k] = S[i,j]*S[k,j]:")
R = model.Concept("result")
j, k, vs2 = Integer.ref(), Integer.ref(), Float.ref()
where(S(i,j,vs), S(k,j,vs2)).define(R.new(i=i, k=k, val=sum(vs*vs2).per(i,k)))
select(R.i, R.k, R.val).inspect()
# S2 = S.ref()
# where(S["j"]==S2["j"]).define(R.new(i=S["i"], k=S2["i"], val=sum(S["val"]*S2["val"]).per(S["i"],S2["i"])))
# select(R.i, R.k, R.val).inspect()

print("R[i] = sigm[S[i,j]*U[j]]:") # single neural net layer
R = model.Concept("result")
vu = Float.ref()
where(S(i,j,vs), U(j,vu)).define(R.new(i=i, val=sigm(sum(vs*vu).per(i))))
select(R.i, R.val).inspect()
# where(S["j"]==U["i"]).define(R.new(i=S["i"], val=sigm(sum(S["val"]*U["val"]).per(S["i"]))))
# select(R.i, R.val).inspect()

print("R[0,j] = U[j];  R[l+1,i] = sigm[W[l,i,j]*R[l,j]:") # multi-later neural net
tmp = model.Concept("tmp")
R = model.Relationship(f"{Integer:layer} {Integer:dim} {Float:val}")
l, vr, vw = Integer.ref(), Float.ref(), Float.ref()
where(U(j,vu)).define(R(0, j, vu))
where(R(l,i,vr), W(l,i,j,vw)).define(R(l+1, i, sigm(sum(vw*vr).per(j,l)))) # this should work but it doesn't!
select(R[0], R[1], R[2]).inspect()


print("R[i,k] = T[i,j,k] * log[abs[S[i,j]/U[j]]]")
R = model.Concept("result")
vt, vs, vu = Float.ref(), Float.ref(), Float.ref()
where(T(i,j,k,vt), S(i,j,vs), U(j,vu), atmp:=log(abs(vs/vu))).define(R.new(i=i, k=k, val=sum(vt*atmp).per(i,k)))
select(R.i, R.k, R.val).inspect()

print("R[i,j,k] = T[i,j,k] + S[i,j] + U[k]:")
R = model.Concept("result")
where(T(i,j,k,vt), S(i,j,vs), U(k,vu)).define(R.new(i=i, j=j, k=k, val=vt+vs+vu))
select(R.i, R.j, R.k, R.val).inspect()

print("R[x,y] = S[x,y] + S[x+i,y+j] * K[i,j]:")
R = model.Concept("result")
x, y, vk = Integer.ref(), Integer.ref(), Float.ref()
( where(S(x,y,vs), K(i,j,vk), S(x+i,y+j,vs2))
    .define(R.new(i=x, j=y, val=vs+sum(vs2*vk).per(x,y))) )
select(R.i, R.j, R.val).inspect()

print("R[i,j,k] = softmax[T[.i,j,k]]:")
R = model.Concept("result")
( where(T(i,j,k,vt), tmaxjk:=max(vt).per(j,k), texpjk:=exp(vt-tmaxjk),
        z:=sum(texpjk).per(j,k))
    .define(R.new(i=i, j=j, k=k, val=texpjk/z)) )
select(R.i, R.j, R.k, R.val).inspect()
