<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t01A08: A generic line has smooth preimage (Sard via projection)

## Why It's Hard

The question asks whether *some* straight line `\ell \subset \mathbb A^3 = \mathbb R^3` has the property that
its preimage `f^{-1}(\ell)` under a smooth map `f : X \to \mathbb R^3` is a smooth manifold. The obstacle is
that for a *badly chosen* line, `f^{-1}(\ell)` can be singular — `f` may fail to be transverse to `\ell`, and
then the preimage can have corners, self-intersections, or jumps in dimension. So a single, hand-picked line
won't do; one needs a *genericity* argument showing that almost every line is good.

The difficulty is finding the right reformulation. A line is a codimension-`2` affine subspace, and
"transverse to a codimension-`2` thing" looks like a two-dimensional condition that is hard to control
directly. The key is to convert "preimage of a **line**" into "preimage of a **point**" under an auxiliary
map, so that the single, powerful tool — **Sard's theorem** — applies. That reformulation is the whole
insight; once made, the answer is an immediate "yes."

## The Key Insight

Fix any direction `v \in \mathbb R^3` and let `\pi : \mathbb R^3 \to \mathbb R^2 = \mathbb R^3/\langle v\rangle`
be the linear projection along `v`. Lines in direction `v` are exactly the fibers `\ell = \pi^{-1}(p)`,
`p \in \mathbb R^2`. Therefore

$$f^{-1}(\ell) = f^{-1}\big(\pi^{-1}(p)\big) = (\pi\circ f)^{-1}(p).$$

Set `g = \pi\circ f : X \to \mathbb R^2`. By **Sard's theorem**, almost every `p \in \mathbb R^2` is a regular
value of `g`, and for a regular value the preimage `g^{-1}(p)` is a smooth submanifold of `X` (of codimension
`2`, or empty). Pick such a `p`; then `\ell = \pi^{-1}(p)` is a line with `f^{-1}(\ell) = g^{-1}(p)` a smooth
manifold. (Indeed `p` is a regular value of `g` iff `f` is transverse to `\ell`, so this is the transversality
condition in disguise.) **Yes**, such a line always exists.

## Complete Proof

**Claim.** For every smooth map `f : X \to \mathbb A^3 = \mathbb R^3` of smooth manifolds, there exists a
straight line `\ell \subset \mathbb R^3` such that `f^{-1}(\ell)` is a smooth manifold. (In fact, in any fixed
direction, almost every line works.)

**Construction.** Choose a nonzero `v \in \mathbb R^3` and let `\pi : \mathbb R^3 \to \mathbb R^2` be a linear
surjection with kernel `\langle v\rangle` (projection along `v`; concretely, projection onto a plane
transverse to `v`). The fibers of `\pi` are precisely the lines parallel to `v`: `\pi^{-1}(p)` is the line
through any point of that fiber in direction `v`.

Define the smooth map

$$g = \pi \circ f : X \longrightarrow \mathbb R^2.$$

**Apply Sard.** By **Sard's theorem**, the set of critical values of `g` has measure zero in `\mathbb R^2`, so
the regular values are dense (of full measure); choose a regular value `p \in \mathbb R^2`.

**The preimage is a manifold.** By the **regular value theorem** (preimage theorem), since `p` is a regular
value of `g`, the set `g^{-1}(p)` is a smooth embedded submanifold of `X`, of dimension `\dim X - 2` (and the
empty set, also a smooth manifold, if `p \notin g(X)`). Now let `\ell = \pi^{-1}(p)`, the line in direction `v`
over `p`. Then

$$f^{-1}(\ell) = f^{-1}\big(\pi^{-1}(p)\big) = (\pi\circ f)^{-1}(p) = g^{-1}(p),$$

which is a smooth manifold.

Therefore such a line `\ell` always exists. $\qquad\blacksquare$

**Remark (transversality reading).** The argument is exactly *parametric transversality*. A regular value `p`
of `g = \pi\circ f` means: at each `x \in g^{-1}(p)`, `d g_x = \pi \circ df_x` is onto `\mathbb R^2`, i.e.
`\operatorname{im}(df_x) + \ker\pi = \mathbb R^3`, i.e. `\operatorname{im}(df_x) + T_{f(x)}\ell = \mathbb R^3`
— precisely the condition that `f` is **transverse** to the line `\ell`. Sard's theorem guarantees a
transverse line exists (in fact, almost all lines in any chosen direction are transverse), and transversality
to a codimension-`2` submanifold makes the preimage a codimension-`2` submanifold. The crucial move is the
reformulation `f^{-1}(\text{line}) = (\pi\circ f)^{-1}(\text{point})`, which reduces a transversality question
to the standard regular-value/Sard machinery. (No compactness or dimension hypotheses on `X` are needed:
if `\dim X < 2`, then `g(X)` has measure zero and almost every `p` gives `f^{-1}(\ell) = \varnothing`, still a
smooth manifold.)
