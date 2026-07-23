<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t93J01: An infinite product of spheres is compact, so its image is bounded

## Why It's Hard

The space `X = \prod_{k=1}^\infty \mathbb S^k` is an *infinite* product, and infinite products are where
intuition about compactness and boundedness often breaks down — infinite-dimensional spaces (like the unit
ball of an infinite-dimensional Banach space) are typically *not* compact, so one might worry that `f(X)`
could be unbounded and meet spheres of every radius. The whole question turns on whether this infinite
product is compact. The decisive fact is **Tychonoff's theorem**: an arbitrary product of compact spaces is
compact in the product topology. Each `\mathbb S^k` is compact, so `X` is compact despite being
"infinite-dimensional," and from there the answer is immediate. Recognizing that Tychonoff applies — and that
the product *topology* (not the box topology) is what makes it work — is the crux.

## The Key Insight

By **Tychonoff**, `X = \prod_k \mathbb S^k` is compact. A continuous image of a compact space is compact, so
`f(X) \subseteq \mathbb R^3` is compact, hence **bounded**: `f(X) \subseteq \{\,y : |y| \le b\,\}` for some
`b` (e.g. `b = \max_{x\in X}|f(x)|`, attained since `|f|` is continuous on the compact `X`). Then any sphere
centered at the origin of radius `r > b` is disjoint from `f(X)`. **Yes** — such a sphere always exists.

## Complete Proof

**Claim.** For every continuous `f : X \to \mathbb R^3`, there is a sphere centered at the origin disjoint
from `f(X)`.

**Step 1 — `X` is compact.** Each `\mathbb S^k` (the `k`-sphere of radius `k` in `\mathbb R^{k+1}`) is a
closed bounded subset of Euclidean space, hence compact. By **Tychonoff's theorem**, the product
`X = \prod_{k=1}^\infty \mathbb S^k` with the product topology is compact.

**Step 2 — `f(X)` is bounded.** Since `f` is continuous and `X` is compact, `f(X)` is a compact subset of
`\mathbb R^3`, hence closed and bounded. Concretely, `g := |f| : X \to [0,\infty)`, `g(x) = |f(x)|`, is
continuous on the compact space `X`, so it attains a maximum

$$b := \max_{x \in X} |f(x)| < \infty,$$

and `f(X) \subseteq \overline B(0, b) = \{\,y \in \mathbb R^3 : |y| \le b\,\}`.

**Step 3 — A large sphere misses `f(X)`.** Choose any `r > b` (e.g. `r = b + 1 > 0`). The sphere
`S_r = \{\,y : |y| = r\,\}` satisfies: for every `x \in X`, `|f(x)| \le b < r`, so `f(x) \notin S_r`.
Therefore

$$S_r \cap f(X) = \varnothing.$$

A sphere centered at the origin and disjoint from `f(X)` always exists.

$$\boxed{\ \text{Yes — any sphere of radius } > \max_{x}|f(x)| \text{ is disjoint from } f(X).\ }\qquad\blacksquare$$

**Remark.** The entire content is **Tychonoff's theorem**: the infinite product of compact spheres is compact
in the product topology, which defeats the intuition that an infinite-dimensional space ought to be
"non-compact and able to map onto unbounded sets." Once `X` is compact, `f(X)` is bounded for purely general
reasons (continuous image of a compact set), and *every* sufficiently large origin-centered sphere works —
indeed `f(X)` misses an entire ray of radii `(b, \infty)`. The result would fail if `X` were merely the
infinite product with the *box* topology (not compact) or an infinite-dimensional ball; the product topology
and Tychonoff are exactly what save it. (Note no hypothesis on `f` beyond continuity is needed, and the
target dimension `3` plays no role.)
