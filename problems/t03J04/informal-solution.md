<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t03J04: The torus has Euler characteristic 0, and anything it locally-diffeomorphically covers does too

## Why It's Hard

The three parts chain together into one conclusion (`\chi = 0` propagates), and each link uses a different
piece of machinery that must be invoked with its hypotheses:

- **(a)(i)** asks for an *explicit* vector field with isolated zeros. The slick move is to realize the torus
  is **parallelizable** (a Lie group), so a constant vector field descends from `\mathbb R^n` and is
  **nowhere zero** — its zero set is empty, hence vacuously "isolated." Overthinking this (trying to build a
  field with actual zeros and compute indices) is unnecessary.
- **(a)(ii)** is **Poincaré–Hopf**: `\chi` equals the sum of indices of *any* vector field with isolated
  zeros. With the nowhere-zero field, that sum is empty, forcing `\chi(T^n) = 0`. The subtlety is that
  Poincaré–Hopf requires a *closed* manifold and isolated zeros — both satisfied — and that "no zeros"
  immediately gives `\chi = 0` (a closed manifold admits a nonvanishing field iff `\chi = 0`).
- **(b)** is where the real argument lives: an orientation-preserving **local diffeomorphism from a compact
  manifold** is automatically a **finite-sheeted covering map** (compactness makes it proper, and proper
  local diffeos are coverings). Then Euler characteristic **multiplies by the degree**, `\chi(T^n) = k\,
  \chi(X)`, and since the left side is `0` with `k\ge 1`, `\chi(X)` is *forced* to be `0`. The trap is to
  forget that compactness upgrades "local diffeomorphism" to "covering," without which the conclusion fails.

## The Key Insight

- **(a)** The constant field `V = \partial/\partial x_1` descends from `\mathbb R^n` to `T^n` and is
  nowhere zero, so by **Poincaré–Hopf** `\chi(T^n) = \sum_{\text{zeros}}\operatorname{ind} = 0`. (Equally:
  `\chi(T^n) = \chi(S^1)^n = 0^n = 0`.)
- **(b)** A local diffeomorphism `\varphi : T^n \to X` with `T^n` compact and `X` connected is a degree-`k`
  covering (`k\ge 1` finite), so `\chi(T^n) = k\,\chi(X)`. As `\chi(T^n) = 0`, the **only possible value is**
  $$\chi(X) = 0,$$
  and it is attained (e.g. `X = T^n`, `\varphi = \mathrm{id}`).

## Complete Proof

Write `T^n = \mathbb R^n/\mathbb Z^n`, a closed (compact, boundaryless) smooth oriented `n`-manifold.

### (a)(i) A vector field with isolated zeros

The translations of `\mathbb Z^n` are isometries of `\mathbb R^n`, so the constant vector field `e_1 =
(1,0,\dots,0)` on `\mathbb R^n` is invariant under the deck group `\mathbb Z^n` and **descends** to a
well-defined smooth vector field on the quotient:
$$
V = \frac{\partial}{\partial x_1} \quad\text{on } T^n .
$$
Since `e_1 \ne 0` everywhere on `\mathbb R^n` and the quotient map is a local diffeomorphism, `V` is
**nowhere zero** on `T^n`. Its zero set is empty, so its zeros are (vacuously) isolated. This is the
required explicit example. (It is the infinitesimal generator of the rotation flow in the first circle
factor.)

### (a)(ii) `\chi(T^n) = 0`

`T^n` is a closed smooth manifold, and `V` is a vector field with isolated zeros (none). By the
**Poincaré–Hopf theorem**, the Euler characteristic equals the sum of the indices of the zeros:
$$
\chi(T^n) = \sum_{p : V(p) = 0} \operatorname{ind}_p(V) = \sum_{\varnothing} = 0 .
$$
$$
\boxed{\ \chi(T^n) = 0 \quad (n \ge 1).\ }
$$
*(Independent check: `\chi` is multiplicative on products and `\chi(S^1) = 0`, so `\chi(T^n) =
\chi(S^1)^n = 0`.)*

### (b) The only possible value is `\chi(X) = 0`

Let `\varphi : T^n \to X` be an orientation-preserving local diffeomorphism into a smooth oriented manifold
`X`. Since `\varphi` is a local diffeomorphism, `\dim X = n` and `X` is boundaryless near the image; we take
`X` connected (the relevant component containing `\varphi(T^n)` — see the note below).

**Step 1: `\varphi` is a finite covering map.** A local diffeomorphism is an **open** map and a local
homeomorphism. Hence `\varphi(T^n)` is open in `X`; it is also compact (continuous image of the compact
`T^n`), hence closed in the Hausdorff space `X`. Being nonempty, open, and closed in the connected `X`, we
get `\varphi(T^n) = X`: `\varphi` is **surjective**. Now `\varphi` is a *proper* (compact domain) local
diffeomorphism onto `X`; such a map is a **covering map**. Concretely, for `x \in X` the fiber
`\varphi^{-1}(x)` is a discrete closed subset of the compact `T^n`, hence finite, say `\{p_1,\dots,p_k\}`;
choosing disjoint neighborhoods `U_i \ni p_i` on which `\varphi` is a diffeomorphism and using compactness
to shrink, one finds an evenly covered neighborhood of `x`. So `\varphi` is a `k`-sheeted covering for some
finite degree `k \ge 1` (the degree is constant on the connected `X`). In particular `X` is a closed
manifold.

**Step 2: Euler characteristic multiplies by the degree.** For a `k`-sheeted covering `\varphi : T^n \to X`
of closed manifolds, the Euler characteristic is multiplicative:
$$
\chi(T^n) = k \cdot \chi(X) .
$$
(Triangulate `X`; lift the triangulation to `T^n`, where each simplex has exactly `k` preimages, so every
face count multiplies by `k`, hence so does the alternating sum `\chi`.)

**Step 3: conclude.** Using part (a)(ii), `\chi(T^n) = 0`, so
$$
0 = \chi(T^n) = k \cdot \chi(X), \qquad k \ge 1 \ \Longrightarrow\ \chi(X) = 0 .
$$
Therefore the **only possible value** is
$$
\boxed{\ \chi(X) = 0.\ }
$$
This value does occur: take `X = T^n` and `\varphi = \mathrm{id}` (a degree-1 covering), or any
self-covering `T^n \to T^n` — all have `\chi(X) = 0`. ∎

**Remark.** The engine is *covering-degree multiplicativity of `\chi`*, and it is the compactness of `T^n`
that turns the merely-local hypothesis "local diffeomorphism" into the global one "covering." Without
compactness this fails (e.g. an open embedding `\mathbb R^n \hookrightarrow X` is a local diffeomorphism but
not a covering, and constrains nothing). The orientation-preserving hypothesis guarantees `X` is oriented
and the cover is honest, though `\chi`-multiplicativity would hold for any finite cover. Geometrically, `X`
must be a closed flat manifold finitely covered by `T^n` — indeed (orientation-preserving, so by Bieberbach)
again an `n`-torus — and *every* such `X` necessarily has vanishing Euler characteristic, the torus's
`\chi = 0` being inherited by everything it covers. If one drops connectedness of `X`, `\varphi(T^n)` is a
single closed component with `\chi = 0`, while other components are unconstrained; the natural reading takes
`X = \varphi(T^n)`.
