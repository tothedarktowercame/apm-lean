<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t94A08: A smooth conic in ℂP² is a manifold; a degenerate conic (two lines) is not

## Why It's Hard

Both `\Sigma_1=\{z_0^2+z_1^2+z_2^2=0\}` and `\Sigma_2=\{z_1^2+z_2^2=0\}` are "quadrics" — zero sets of a
homogeneous degree-`2` polynomial in `\mathbb{CP}^2` — so they look superficially alike. The difficulty is
that *whether such a set is a manifold is decided by a delicate condition*: the **nondegeneracy** of the
quadratic form, i.e. whether the gradient of the defining polynomial vanishes anywhere on the set.

- **(a)** is a regular-value argument, but one must work in **affine charts** (a homogeneous polynomial isn't
  a function on `\mathbb{CP}^2`) and check that the only common zero of the polynomial and its gradient is
  the origin — which is *not* a point of projective space. Missing a chart or mis-stating regularity sinks
  it.
- **(b)** is the real trap. `z_1^2+z_2^2` **factors** as `(z_1+iz_2)(z_1-iz_2)`, so `\Sigma_2` is a *union of
  two projective lines* crossing at one point. Showing it is *not* a manifold cannot be done by "it has a
  corner" — one needs a genuine **topological invariant** that a `2`-manifold point must satisfy but the
  crossing point violates. The clean one: a small *punctured* neighborhood of a `2`-manifold point is
  **connected** (`\mathbb R^2\setminus\{0\}` is connected), whereas the node's punctured neighborhood splits
  into **two** components (one per line).

## The Key Insight

- **(a)** `F=z_0^2+z_1^2+z_2^2` has gradient `(2z_0,2z_1,2z_2)`, which vanishes only at the origin — never on
  `\Sigma_1`. So in each affine chart `0` is a regular value of the dehomogenized equation, and `\Sigma_1` is
  a smooth complex curve (real `2`-manifold). The form has **rank 3** (nondegenerate): a *smooth* conic.
- **(b)** `z_1^2+z_2^2=(z_1+iz_2)(z_1-iz_2)`, so `\Sigma_2 = L_+\cup L_-` is two lines meeting at
  `p=[1:0:0]`. Near `p` it is two `2`-disks joined only at `p`; deleting `p` disconnects a neighborhood into
  two pieces, so `p` has no neighborhood homeomorphic to `\mathbb R^2`. `\Sigma_2` is **not** a manifold.

## Complete Proof

`\mathbb{CP}^2` has homogeneous coordinates `[z_0:z_1:z_2]` and standard affine charts
`U_i=\{z_i\ne0\}`, which cover it.

### (a) `\Sigma_1=\{z_0^2+z_1^2+z_2^2=0\}` is a manifold

Let `F(z)=z_0^2+z_1^2+z_2^2`, homogeneous of degree `2`. Its (complex) gradient is
$$
\nabla F = (2z_0,\,2z_1,\,2z_2),
$$
which vanishes **only** at `z=(0,0,0)` — not a point of `\mathbb{CP}^2`. So `\nabla F\ne0` at every point of
`\Sigma_1`. We turn this into a manifold statement chart by chart.

In `U_0` (`z_0\ne0`), use affine coordinates `(x,y)=(z_1/z_0,\,z_2/z_0)`; dividing `F=0` by `z_0^2`,
$$
\Sigma_1\cap U_0 = \{(x,y)\in\mathbb C^2 : f_0(x,y):=x^2+y^2+1=0\}.
$$
The holomorphic map `f_0:\mathbb C^2\to\mathbb C` has derivative `df_0=(2x,2y)`, which is **surjective**
(nonzero) except at `(x,y)=(0,0)`; but there `f_0(0,0)=1\ne0`, so `(0,0)\notin\Sigma_1\cap U_0`. Hence `0` is
a **regular value** of `f_0`, and by the (holomorphic) implicit function / regular value theorem,
`\Sigma_1\cap U_0` is a smooth complex `1`-dimensional submanifold (real dimension `2`) of `U_0`.

By the symmetry of `F` in the three coordinates, the same computation works in `U_1` (coords
`(z_0/z_1,z_2/z_1)`, equation `u^2+1+v^2=0`, gradient `(2u,2v)`, bad point value `1\ne0`) and in `U_2`. Since
`U_0,U_1,U_2` cover `\mathbb{CP}^2`, every point of `\Sigma_1` has a chart in which it is a regular level set.
Therefore `\Sigma_1` is a **smooth submanifold** of `\mathbb{CP}^2`, of real dimension `2` — a manifold. (It
is a *nonsingular* conic; in fact `\Sigma_1\cong\mathbb{CP}^1\cong S^2`.) ∎

### (b) `\Sigma_2=\{z_1^2+z_2^2=0\}` is not a manifold

**`\Sigma_2` is two lines crossing at a point.** Factor the defining polynomial:
$$
z_1^2+z_2^2 = (z_1+iz_2)(z_1-iz_2),
$$
so
$$
\Sigma_2 = L_+\cup L_-, \qquad L_+=\{z_1+iz_2=0\},\quad L_-=\{z_1-iz_2=0\}.
$$
Each `L_\pm` is the zero set of a *linear* form, hence a **projective line** `\cong\mathbb{CP}^1` (a smooth
`2`-manifold). They meet where `z_1+iz_2=0` **and** `z_1-iz_2=0`, forcing `z_1=z_2=0`, i.e. at the single
point
$$
p=[1:0:0].
$$
Thus `\Sigma_2` is two `2`-spheres (lines) glued at the one point `p`, and `\Sigma_2\setminus\{p\}=(L_+\setminus
\{p\})\sqcup(L_-\setminus\{p\})` is a `2`-manifold; the only possibly-bad point is `p`.

**The crossing point `p` has no Euclidean neighborhood.** Work in the chart `U_0` with affine coordinates
`(x,y)=(z_1/z_0,z_2/z_0)`, where `p=(0,0)` and
$$
\Sigma_2\cap U_0 = \{x+iy=0\}\cup\{x-iy=0\},
$$
two **distinct complex lines through the origin** in `\mathbb C^2` — i.e. two real `2`-planes meeting only at
`0`. Let `N` be any sufficiently small neighborhood of `p` in `\Sigma_2`; it is a union of a disk `D_+\subset
L_+` and a disk `D_-\subset L_-`, meeting only at `p`. Deleting `p`,
$$
N\setminus\{p\} = (D_+\setminus\{p\})\ \sqcup\ (D_-\setminus\{p\}),
$$
a disjoint union of two **punctured disks**. Each punctured disk `D_\pm\setminus\{p\}` is connected, and the
two are disjoint (the lines meet only at `p`), so `N\setminus\{p\}` has **(at least) two connected
components**.

Now suppose, for contradiction, that `\Sigma_2` were a manifold near `p`. Away from `p` it has dimension `2`
(the lines are `2`-dimensional), so its dimension is `2`, and `p` would have a neighborhood `V`
homeomorphic to `\mathbb R^2`. Shrinking `V` inside `N`, the homeomorphism carries `V\setminus\{p\}` to
`\mathbb R^2\setminus\{q\}` for a point `q` — which is **connected**. But `V\setminus\{p\}\subseteq
N\setminus\{p\}`, and small punctured neighborhoods of `p` have two components, so `V\setminus\{p\}` is
**disconnected** — contradiction.

Therefore `p` has no neighborhood homeomorphic to `\mathbb R^2`, and `\Sigma_2` is **not a manifold**. ∎

**Remark.** The dichotomy is rank of the quadratic form. `\Sigma_1`'s form `z_0^2+z_1^2+z_2^2` has rank `3`
(**nondegenerate**), so the gradient never vanishes on the curve and `\Sigma_1` is a smooth conic. `\Sigma_2`'s
form `z_1^2+z_2^2` has rank `2` — it omits `z_0` entirely — making it **degenerate**, and a degenerate
quadratic form factors into linear factors, so the "conic" splits into lines; the gradient
`(0,2z_1,2z_2)` of `z_1^2+z_2^2` *does* vanish on `\Sigma_2`, exactly at the node `p=[1:0:0]`, which is the
singular point. The non-manifold proof is the standard "punctured-neighborhood connectivity" test for nodal
singularities: an ordinary double point (two smooth branches crossing transversally) always disconnects a
small punctured neighborhood, which an `\mathbb R^n` point (`n\ge2`) cannot do.
