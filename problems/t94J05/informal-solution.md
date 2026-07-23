<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t94J05: A smooth map from the torus to S³ is null-homotopic (dimension gap via Sard)

## Why It's Hard

Proving a map is null-homotopic means producing a deformation to a constant, which is hard to do by hand for
an arbitrary `f`. The trick is to find structural slack: here the **dimension gap** between the source
`S^1 \times S^1` (dimension `2`) and the target `S^3` (dimension `3`). The key realization is that a *smooth*
map cannot fill up a higher-dimensional target — by Sard's theorem its image has measure zero — so `f` must
**miss a point** of `S^3`. Once `f` misses a point, it factors through `S^3` minus that point, which is just
`\mathbb R^3` (stereographic projection) and is contractible, so `f` is automatically null-homotopic.
Recognizing that "lower-dimensional smooth source `\Rightarrow` non-surjective `\Rightarrow` lands in a
contractible space" is the whole idea; the smoothness hypothesis is what makes Sard available.

## The Key Insight

`f : T^2 \to S^3` is smooth and `\dim T^2 = 2 < 3 = \dim S^3`. So at every point the differential `df` has rank
`\le 2 < 3` — every point is a critical point — and by **Sard's theorem** the image `f(T^2)` (a set of
critical values) has measure zero. Hence `f` is **not surjective**: there is `q \in S^3 \setminus f(T^2)`.
Then `f` maps into `S^3 \setminus \{q\} \cong \mathbb R^3` (stereographic projection from `q`), which is
**contractible**, so `f` is null-homotopic; composing with the contraction homotopy carries `f` to a constant,
which (since `S^3` is path-connected) may be taken to be `(0,0,0,1)`.

## Complete Proof

Let `f : S^1 \times S^1 \to S^3` be smooth.

**Step 1 — `f` is not surjective (Sard).** Since `\dim(S^1 \times S^1) = 2 < 3 = \dim S^3`, the differential
`df_x : T_x(S^1\times S^1) \to T_{f(x)}S^3` has rank at most `2`, hence is never surjective; so *every* point
`x` is a critical point and *every* value `f(x)` is a critical value. By **Sard's theorem**, the set of
critical values has measure zero in `S^3`, so

$$f(S^1 \times S^1) \text{ has measure zero in } S^3.$$

In particular `f(S^1 \times S^1) \ne S^3` (the whole sphere has positive measure), so there exists
`q \in S^3 \setminus f(S^1 \times S^1)`.

**Step 2 — `f` lands in a contractible set.** Since `f` misses `q`, it factors through the inclusion

$$f : S^1 \times S^1 \longrightarrow S^3 \setminus \{q\}.$$

Stereographic projection from `q` is a homeomorphism `S^3 \setminus \{q\} \cong \mathbb R^3`, and `\mathbb R^3`
is contractible. So `S^3 \setminus \{q\}` is contractible: there is a homotopy
`H : (S^3\setminus\{q\}) \times [0,1] \to S^3 \setminus \{q\}` with `H_0 = \mathrm{id}` and `H_1 \equiv p_0` for
some point `p_0`.

**Step 3 — Contract `f`.** Define `\widetilde H : (S^1\times S^1) \times [0,1] \to S^3\setminus\{q\} \subseteq S^3`
by `\widetilde H(x,t) = H(f(x), t)`. This is a homotopy with `\widetilde H_0 = f` and `\widetilde H_1 \equiv p_0`
(a constant map). Thus `f` is homotopic (within `S^3`) to a constant map.

**Step 4 — Normalize the constant.** `S^3` is path-connected, so any two constant maps are homotopic: choosing
a path from `p_0` to `(0,0,0,1)` and sliding the constant value along it gives a homotopy from the constant
`p_0` to the constant `(0,0,0,1)`. Concatenating with Step 3,

$$\boxed{\ f \text{ is homotopic to the constant map } x \mapsto (0,0,0,1).\ }\qquad\blacksquare$$

**Remark.** The engine is the **dimension gap**: a smooth map from a `2`-manifold into a `3`-manifold cannot
be onto (Sard), and a sphere minus a point is Euclidean, hence contractible. The same argument shows any
smooth `f : M^m \to S^n` with `m < n` is null-homotopic. Topologically the result also follows from `S^3`
being `2`-connected (`\pi_1 = \pi_2 = 0`) and `T^2` being a `2`-complex — obstruction theory kills the map
cell by cell — but the Sard argument is more elementary and uses the smoothness hypothesis directly. (Without
smoothness the statement is still true for `T^2 \to S^3` by connectivity, but space-filling continuous maps
exist, so one could not simply invoke non-surjectivity.)
