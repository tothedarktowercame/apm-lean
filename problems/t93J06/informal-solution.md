<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t93J06: No nonvanishing vector field exists on S² or S⁴ (the hairy ball theorem on even spheres)

## Why It's Hard

Both parts ask to *construct or refute*, and the answer is **refute** in each case — but the refutation is
not elementary point-set topology; it needs a genuine global invariant. The difficulty is identifying that
the obstruction is the **Euler characteristic** (or equivalently a degree computation), and that the only
feature distinguishing these spheres from the odd-dimensional ones (which *do* admit nonvanishing fields) is
the *parity of the dimension*:

- A nonvanishing vector field is a *local* gadget, yet whether one exists is a *global* topological
  question. The bridge is **Poincaré–Hopf**: the signed count of zeros of any vector field equals `\chi(M)`,
  so a *zero-free* field forces `\chi(M)=0`. Since `\chi(S^2)=\chi(S^4)=2\ne0`, none can exist.
- The self-contained refutation (no Poincaré–Hopf machinery) is the slick **antipodal-degree** argument: a
  unit tangent field would furnish a homotopy from the identity to the antipodal map, and on an *even*
  sphere those two maps have *different degrees* (`1` versus `-1`) — impossible. Seeing that the homotopy
  `\cos t\,x+\sin t\,v(x)` lands on the sphere (using tangency `x\perp v(x)`) is the crux.
- The trap is to think `S^4`, being higher-dimensional, might behave differently from `S^2`; in fact the
  *only* thing that matters is that `4` and `2` are **even**.

## The Key Insight

A closed manifold admits a nowhere-zero vector field iff `\chi=0` (Poincaré–Hopf: zero-free `\Rightarrow
\sum\text{indices}=0=\chi`). For spheres,
$$
\chi(S^n) = 1 + (-1)^n = \begin{cases}2,& n\text{ even}\\ 0,& n\text{ odd},\end{cases}
$$
so `\chi(S^2)=\chi(S^4)=2\ne0` and **neither admits a nonvanishing field**. Equivalently and elementarily: a
unit tangent field `v` on `S^n` gives the homotopy `H(x,t)=\cos t\,x+\sin t\,v(x)` from `\mathrm{id}` (degree
`1`) to the antipodal map (degree `(-1)^{n+1}`); for even `n` these degrees differ (`1\ne-1`), a
contradiction.

## Complete Proof

**Both answers: such fields cannot exist.** We refute (a) and (b) simultaneously, since both `S^2` and `S^4`
are *even*-dimensional spheres; we give two proofs.

### Proof via Poincaré–Hopf

For a closed (compact, boundaryless) smooth manifold `M` and a smooth vector field `V` on `M` with isolated
zeros, the **Poincaré–Hopf theorem** states
$$
\sum_{p\,:\,V(p)=0}\operatorname{ind}_p(V) = \chi(M).
$$
If `V` were **nowhere zero**, it would have no zeros (vacuously isolated), so the sum is empty and
$$
\chi(M) = 0.
$$
Contrapositively, **if `\chi(M)\ne0` then every smooth vector field on `M` has a zero.**

Now compute Euler characteristics from `H_*(S^n)\cong\mathbb Z` in degrees `0` and `n` (and `0` otherwise):
$$
\chi(S^n) = \sum_k (-1)^k b_k = (-1)^0 + (-1)^n = 1 + (-1)^n .
$$
For `n=2` and `n=4` (both even),
$$
\chi(S^2) = 1+1 = 2 \ne 0, \qquad \chi(S^4) = 1+1 = 2 \ne 0 .
$$
Therefore neither `S^2` nor `S^4` admits a nonvanishing vector field. ∎

### Self-contained proof via the antipodal degree

Suppose, for contradiction, that `S^n` (with `n` even) carries a nowhere-zero smooth tangent vector field
`V`. Normalizing, `v(x) = V(x)/|V(x)|` is a **unit** tangent field: `|v(x)|=1` and, since `v(x)` is tangent
to the sphere at `x`, it is orthogonal to the position vector, `\langle x, v(x)\rangle = 0`.

Define `H : S^n\times[0,\pi]\to\mathbb R^{n+1}` by
$$
H(x,t) = \cos t\, x + \sin t\, v(x).
$$
Then `H(x,t)` lies on `S^n`, because
$$
|H(x,t)|^2 = \cos^2 t\,|x|^2 + 2\cos t\sin t\,\langle x, v(x)\rangle + \sin^2 t\,|v(x)|^2 = \cos^2 t + 0 + \sin^2 t = 1,
$$
using `|x|=1`, `\langle x,v(x)\rangle=0`, `|v(x)|=1`. So `H` is a (continuous, even smooth) homotopy in
`S^n` with
$$
H(x,0) = x = \mathrm{id}(x), \qquad H(x,\pi) = -x = a(x),
$$
where `a` is the antipodal map. Hence `\mathrm{id}\simeq a`, so they have equal degree:
$$
\deg(\mathrm{id}) = \deg(a).
$$
But `\deg(\mathrm{id}) = 1`, while the antipodal map `a(x)=-x` is the composition of the `n+1` coordinate
reflections (each of degree `-1`), so `\deg(a) = (-1)^{n+1}`. Thus
$$
1 = (-1)^{n+1}.
$$
For `n` **even**, `(-1)^{n+1} = -1\ne 1` — a contradiction. Hence no nonvanishing tangent vector field
exists on `S^n` for even `n`, in particular on `S^2` (the classical **hairy ball theorem**, "you cannot comb
a hairy ball flat") and on `S^4`. ∎

**Remark.** The parity of `n` is everything. For *odd* `n` a nonvanishing field exists explicitly: pairing
coordinates,
$$
V(x_1,x_2,\dots,x_{n},x_{n+1}) = (-x_2, x_1, -x_4, x_3, \dots, -x_{n+1}, x_n)
$$
is tangent (`\langle x, V(x)\rangle = 0`) and never zero (`|V(x)|=|x|=1`); correspondingly
`\chi(S^{\text{odd}})=0` and `(-1)^{n+1}=1`, so both obstructions vanish. The two proofs are two faces of the
same coin: Poincaré–Hopf packages the obstruction as `\chi(M)`, while the antipodal-homotopy argument exposes
it as the degree of the antipodal map — and on `S^2, S^4` both read out the nonzero value forbidding a
zero-free field.
