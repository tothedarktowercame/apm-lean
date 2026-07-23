<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t93A04: A generic line has smooth preimage (Sard via projection)

## Why It's Hard

The question asks whether *some* line `\ell \subset \mathbb R^3` makes `f^{-1}(\ell)` a smooth manifold for a
given smooth `f : X \to \mathbb R^3`. For a badly chosen line, `f^{-1}(\ell)` can be singular: `f` may fail to
be transverse to `\ell`, and the preimage then has corners or jumps in dimension. So a hand-picked line is not
enough — one needs a *genericity* argument showing almost every line is good. The obstacle is that "transverse
to a line" looks like a codimension-`2` condition, hard to control directly. The trick is to reformulate
"preimage of a **line**" as "preimage of a **point**" under an auxiliary map, so that the single powerful tool
— **Sard's theorem** — applies. Once made, the answer is an immediate "yes."

## The Key Insight

Fix any direction `v \in \mathbb R^3` and let `\pi : \mathbb R^3 \to \mathbb R^2 = \mathbb R^3/\langle v\rangle`
be the linear projection along `v`. Lines in direction `v` are exactly the fibers `\ell = \pi^{-1}(p)`, so

$$f^{-1}(\ell) = f^{-1}\big(\pi^{-1}(p)\big) = (\pi \circ f)^{-1}(p).$$

Set `g = \pi \circ f : X \to \mathbb R^2`. By **Sard's theorem**, almost every `p \in \mathbb R^2` is a
regular value of `g`, and for a regular value `g^{-1}(p)` is a smooth submanifold of `X`. Picking such `p`,
the line `\ell = \pi^{-1}(p)` has `f^{-1}(\ell) = g^{-1}(p)` smooth. **Yes**, such a line always exists.

## Complete Proof

**Claim.** For every smooth map `f : X \to \mathbb R^3` of smooth manifolds, there is a straight line
`\ell \subset \mathbb R^3` with `f^{-1}(\ell)` a smooth manifold (in fact, almost every line in any fixed
direction works).

**Construction.** Fix a nonzero `v \in \mathbb R^3` and a linear surjection `\pi : \mathbb R^3 \to \mathbb R^2`
with kernel `\langle v\rangle` (projection along `v` onto a transverse plane). Its fibers are exactly the
lines parallel to `v`: `\pi^{-1}(p)` is the line in direction `v` through any point mapping to `p`. Define the
smooth map

$$g = \pi \circ f : X \longrightarrow \mathbb R^2.$$

**Apply Sard.** By **Sard's theorem**, the critical values of `g` form a measure-zero subset of `\mathbb R^2`,
so the regular values are dense (full measure); choose a regular value `p \in \mathbb R^2`.

**The preimage is a manifold.** By the **regular value theorem**, `g^{-1}(p)` is a smooth embedded submanifold
of `X` of dimension `\dim X - 2` (and the empty set — still a smooth manifold — if `p \notin g(X)`). Setting
`\ell = \pi^{-1}(p)`, the line in direction `v` over `p`,

$$f^{-1}(\ell) = f^{-1}\big(\pi^{-1}(p)\big) = (\pi \circ f)^{-1}(p) = g^{-1}(p)$$

is a smooth manifold. Hence such a line exists.

$$\boxed{\ \text{Yes: a straight line } \ell \subset \mathbb R^3 \text{ with } f^{-1}(\ell) \text{ a smooth manifold always exists.}\ }\qquad\blacksquare$$

**Remark (transversality reading).** A regular value `p` of `g = \pi \circ f` means `dg_x = \pi \circ df_x` is
onto `\mathbb R^2` at each `x \in g^{-1}(p)`, i.e. `\operatorname{im}(df_x) + \ker\pi = \mathbb R^3`, i.e.
`\operatorname{im}(df_x) + T_{f(x)}\ell = \mathbb R^3` — exactly that `f` is **transverse** to the line `\ell`.
So the argument is parametric transversality: the reformulation `f^{-1}(\text{line}) = (\pi \circ f)^{-1}(\text{point})`
reduces a codimension-`2` transversality condition to the standard regular-value / Sard machinery, and Sard
guarantees a transverse (hence good) line — indeed almost all lines in any chosen direction. No compactness or
dimension hypotheses on `X` are needed: if `\dim X < 2`, then `g(X)` has measure zero and almost every `p`
gives `f^{-1}(\ell) = \varnothing`, still a manifold.
