<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t93J04: The two factor spheres in S²×S² are not homotopic — distinguished by homology / the intersection form

## Why It's Hard

The two spheres `S^2\times\{p\}` and `\{p\}\times S^2` look interchangeable: each is a copy of `S^2`
embedded as a coordinate factor, and the **swap** homeomorphism `(x,y)\mapsto(y,x)` of `S^2\times S^2`
carries one onto the other. This tempts the answer "yes, homotopic." The trap is that an *ambient symmetry
of the space* is **not** the same as a *homotopy of one inclusion map to the other within the space* —
homotopy of the maps `f(x)=(x,p)` and `g(x)=(p,x)` is a finer question that the swap does not settle.

The honest test is a homotopy invariant of *maps* `S^2\to S^2\times S^2`. The right one is the induced class
in `H_2(S^2\times S^2)\cong\mathbb Z^2`: the two inclusions hit the **two different basis generators**, so
they cannot be homotopic. The geometry behind "different generators" is the **intersection form** — the two
spheres meet each other once but each misses a parallel copy of itself, so they sit differently in the
4-manifold. Recognizing that the question is about the *maps* (not the abstract diffeomorphism type of the
images) is the whole difficulty.

## The Key Insight

By Künneth, `H_2(S^2\times S^2)\cong\mathbb Z^2` has basis `\alpha=[S^2\times\{p\}]` and
`\beta=[\{p\}\times S^2]`. The inclusions `f(x)=(x,p)` and `g(x)=(p,x)` satisfy
$$
f_*[S^2]=\alpha, \qquad g_*[S^2]=\beta, \qquad \alpha\ne\beta .
$$
Homotopic maps induce the **same** homomorphism on homology, so `f\simeq g` would force `\alpha=\beta` — a
contradiction. Hence **`S^2\times\{p\}` is not homotopic to `\{p\}\times S^2`.** Geometrically, the
intersection form is hyperbolic — `\alpha\cdot\alpha=\beta\cdot\beta=0` but `\alpha\cdot\beta=1` — so
`\alpha\ne\beta` (if they were equal, `\alpha\cdot\alpha` would be both `0` and `1`).

## Complete Proof

**Answer: No.** The two spheres are not smoothly (indeed not even continuously) homotopic.

Let `f, g : S^2\to S^2\times S^2` be the two inclusions,
$$
f(x) = (x, p) \quad(\text{image } S^2\times\{p\}), \qquad g(x) = (p, x) \quad(\text{image } \{p\}\times S^2).
$$
"Homotopic" means these maps are homotopic. (Since both are smooth and smooth homotopy classes of maps
between manifolds coincide with continuous ones by smooth approximation, it suffices to rule out a continuous
homotopy.)

### Step 1: the homology of `S^2\times S^2`

`S^2` has `H_0(S^2)=H_2(S^2)=\mathbb Z` and all other homology zero. By the **Künneth theorem** (no Tor
terms, as everything is free),
$$
H_2(S^2\times S^2) \cong \bigoplus_{i+j=2} H_i(S^2)\otimes H_j(S^2) = \big(H_0\otimes H_2\big)\oplus\big(H_2\otimes H_0\big) = \mathbb Z\oplus\mathbb Z,
$$
with basis the two factor classes
$$
\alpha = [S^2\times\{p\}] = f_*[S^2], \qquad \beta = [\{p\}\times S^2] = g_*[S^2].
$$
These are *distinct* basis elements of `\mathbb Z^2`; in particular `\alpha\ne\beta`.

### Step 2: homotopic maps would identify `\alpha` and `\beta`

Suppose, for contradiction, that `f\simeq g` (homotopic). Homology is a homotopy functor: homotopic maps
induce the same homomorphism on `H_*`. Hence `f_*=g_*` on `H_2(S^2)`, so applied to the fundamental class
`[S^2]`,
$$
\alpha = f_*[S^2] = g_*[S^2] = \beta .
$$
But `\alpha` and `\beta` are independent generators of `H_2(S^2\times S^2)=\mathbb Z^2`, so `\alpha\ne\beta`
— a contradiction. Therefore `f` and `g` are **not homotopic**.

### Step 3: the geometric reason — the intersection form

To see concretely why `\alpha\ne\beta`, compute the intersection pairing on `H_2` of the oriented closed
`4`-manifold `S^2\times S^2`:

- **`\alpha\cdot\beta = 1`.** The representatives `S^2\times\{p\}` and `\{p\}\times S^2` meet exactly where
  `(x,p)=(p,y)`, i.e. at the single point `(p,p)`. There the tangent spaces are
  `T_{(p,p)}(S^2\times\{p\}) = T_pS^2\times 0` and `T_{(p,p)}(\{p\}\times S^2) = 0\times T_pS^2`, which are
  complementary in `T_pS^2\times T_pS^2 = T_{(p,p)}(S^2\times S^2)`. So the intersection is transverse and
  consists of one point: `\alpha\cdot\beta = \pm1`.
- **`\alpha\cdot\alpha = 0`.** Push `\alpha` off itself: `S^2\times\{p\}` and `S^2\times\{q\}` are disjoint
  for `q\ne p`, and `[S^2\times\{q\}]=\alpha`, so `\alpha\cdot\alpha = 0`. Likewise `\beta\cdot\beta = 0`.

Thus the intersection form is the hyperbolic form `\begin{psmallmatrix}0&1\\1&0\end{psmallmatrix}` in the
basis `(\alpha,\beta)`. If `\alpha=\beta`, then `\alpha\cdot\alpha = \alpha\cdot\beta`, i.e. `0=1` —
impossible. This re-proves `\alpha\ne\beta`, confirming the spheres are not homotopic. ∎

**Remark.** The lesson is to distinguish *homotopy of the inclusion maps* from *abstract equivalence of the
images*: the swap `(x,y)\mapsto(y,x)` is a self-diffeomorphism of `S^2\times S^2` carrying one sphere to the
other, and the two spheres are of course diffeomorphic to each other (both `\cong S^2`) — but neither fact
makes the *inclusions* homotopic, because a homotopy must move one map to the other *inside* `S^2\times S^2`
without an ambient symmetry, and the homology class it would have to preserve obstructs this. The intersection
form pinpoints the obstruction: the two factor spheres have *self*-intersection `0` but mutual intersection
`1`, so each "links" the other and they occupy genuinely different `H_2`-classes. (The same computation shows
no map homotopic to `f` can be made disjoint from `\{p\}\times S^2`, since `\alpha\cdot\beta=1\ne0`.)
