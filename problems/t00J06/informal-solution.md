<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t00J06: Any map from the torus to a genus-2 surface lifts to an infinite covering

## Why It's Hard

The statement is a *universal* one — it must hold for **every** map `f : \mathbb T \to \Sigma`, with no
hypothesis on `f` (it need not be a covering, an immersion, or even injective on `\pi_1`). So the proof
cannot use any special structure of `f`; it has to extract the one feature shared by all such maps. That
feature lives at the level of fundamental groups, and the difficulty is seeing which algebraic fact does
the work:

- The lifting criterion reduces "f lifts to the covering `\widetilde\Sigma_H \to \Sigma`" to a purely
  group-theoretic condition: `f_*(\pi_1\mathbb T) \subseteq H`. And "the covering is **infinite**" means the
  subgroup `H` has **infinite index**. So the whole problem becomes: *find an infinite-index subgroup of
  `\pi_1(\Sigma)` containing the image of `f_*`.*
- The natural candidate is `H = f_*(\pi_1\mathbb T)` itself. The crux is then to prove this image has
  infinite index — and the only thing one knows about it is that, being a homomorphic image of
  `\pi_1\mathbb T = \mathbb Z^2`, it is **abelian**. The real content is the topological fact that *a
  genus-2 surface group has no finite-index abelian subgroup* — indeed every abelian subgroup has infinite
  index. Recognizing that "abelian image ⇒ infinite index" is the entire engine, and proving it cleanly
  (via Euler characteristics of covers) is the heart of the problem.

## The Key Insight

Take `H := f_*(\pi_1\mathbb T) \le \pi_1(\Sigma)`. Since `\pi_1(\mathbb T) = \mathbb Z^2` is **abelian**, so
is `H`. But `\pi_1(\Sigma)` (genus `2`) has **no finite-index abelian subgroup**: a finite-index subgroup
would be `\pi_1` of a finite cover of `\Sigma`, i.e. a *closed orientable surface of Euler characteristic
`[\,\pi_1:H\,]\cdot(2-2\cdot 2) < 0`*, hence of genus `\ge 2`, whose fundamental group is **non-abelian** —
a contradiction. Therefore `H` has **infinite index**, so the covering `\widetilde\Sigma_H \to \Sigma` it
determines has infinitely many sheets, and by the **lifting criterion** (`f_*(\pi_1\mathbb T) = H \subseteq
H`) the map `f` lifts to it.

## Complete Proof

Write `\mathbb T` for the 2-torus and `\Sigma` for the closed oriented surface of genus `2`. Fix basepoints
`t_0 \in \mathbb T`, `x_0 = f(t_0) \in \Sigma`, and set `G := \pi_1(\Sigma, x_0)`. Recall
$$
\pi_1(\mathbb T, t_0) \cong \mathbb Z^2 \quad(\text{abelian}), \qquad \chi(\Sigma) = 2 - 2\cdot 2 = -2 .
$$

### Step 1: the image subgroup is abelian

Let `H := f_*\big(\pi_1(\mathbb T, t_0)\big) \le G`, the image of the induced homomorphism
`f_* : \pi_1(\mathbb T, t_0) \to G`. As the homomorphic image of the abelian group `\mathbb Z^2`, the
subgroup `H` is **abelian**.

### Step 2: `H` has infinite index in `G`

Suppose, for contradiction, that `n := [G : H] < \infty`. Because `\Sigma` is a connected manifold (hence
locally path-connected and semilocally simply connected), covering-space theory provides a connected
covering `p : \widetilde\Sigma_H \to \Sigma` with `p_*\big(\pi_1(\widetilde\Sigma_H)\big) = H` and with
exactly `n = [G:H]` sheets. A finite covering of a closed surface is a closed surface; a covering of an
*orientable* surface is orientable. Hence `\widetilde\Sigma_H` is a **closed orientable surface**, and the
Euler characteristic multiplies by the number of sheets:
$$
\chi(\widetilde\Sigma_H) = n\,\chi(\Sigma) = n\,(-2) = -2n < 0 .
$$
By the classification of closed orientable surfaces, a negative Euler characteristic forces genus
`\widetilde g = \tfrac{2-\chi}{2} = n+1 \ge 2`. The fundamental group of a closed orientable surface of
genus `\ge 2` is **non-abelian** (e.g. it surjects onto the non-abelian free group `F_2` via abelianizing
all but two generators, or simply: only `S^2` and `T^2`, with `\chi \ge 0`, have abelian surface groups).
But `\pi_1(\widetilde\Sigma_H) \cong H` is abelian by Step 1 — a contradiction.

Therefore no finite `n` is possible: `[G : H] = \infty`.

*(The same computation rules out the degenerate cases uniformly: if `H` were trivial of finite index `n`,
`\widetilde\Sigma_H` would be a closed surface with `\pi_1 = 1`, i.e. `S^2` with `\chi = 2`, contradicting
`\chi = -2n < 0`.)*

### Step 3: the infinite covering exists and `f` lifts to it

Since `\Sigma` is connected, locally path-connected and semilocally simply connected, the subgroup `H \le
G` is realized by a connected covering
$$
p : \widetilde\Sigma \to \Sigma, \qquad p_*\big(\pi_1(\widetilde\Sigma, \tilde x_0)\big) = H,
$$
for a suitable basepoint `\tilde x_0 \in p^{-1}(x_0)`. The number of sheets of `p` equals the index
`[G : H] = \infty` (Step 2), so `p` is an **infinite covering**.

Now apply the **lifting criterion**: a map `f : \mathbb T \to \Sigma` from a path-connected, locally
path-connected space lifts through `p` (with `f(t_0) \mapsto \tilde x_0`) **if and only if**
$$
f_*\big(\pi_1(\mathbb T, t_0)\big) \subseteq p_*\big(\pi_1(\widetilde\Sigma, \tilde x_0)\big) .
$$
Here the right-hand side is `H`, and the left-hand side is `H` by definition (Step 1), so the inclusion
holds (with equality). The torus `\mathbb T` is path-connected and locally path-connected, so the criterion
applies and yields a continuous lift
$$
\tilde f : \mathbb T \to \widetilde\Sigma \qquad\text{with}\qquad p \circ \tilde f = f .
$$

Thus `f` factors through the infinite covering `p : \widetilde\Sigma \to \Sigma`; that is, `f` lifts to an
infinite covering of `\Sigma`. ∎

**Remark.** The argument never used anything about `f` beyond the abelianness of `\pi_1(\mathbb T)`, which
is exactly why it is universal. The load-bearing fact is that surface groups of genus `\ge 2` are "large":
they have no finite-index abelian subgroups (more is true — every abelian subgroup is *infinite cyclic or
trivial*, since an infinite-index subgroup is `\pi_1` of an open surface, hence free, and a free abelian
group is cyclic). Geometrically, `\Sigma` carries a hyperbolic metric and `G` acts on `\mathbb H^2` as a
cocompact Fuchsian group; its abelian subgroups are cyclic, generated by single hyperbolic translations.
The torus, being flat (`\chi = 0`), can never finitely cover the negatively curved `\Sigma`, and that
curvature/Euler-characteristic mismatch is precisely what forces every such `f` up into an infinite cover.
