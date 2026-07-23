<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t96J05: Some origin-centered sphere meets a connected submanifold in a nonempty manifold

## Why It's Hard

"Find a sphere `S` such that `X\cap S` is a smooth manifold" is a transversality/regular-value statement in
disguise, and three requirements must be met *simultaneously*, which is where the difficulty lies:

- **Manifold:** `X\cap S` is a smooth manifold when `S` meets `X` *cleanly*, i.e. when the corresponding
  value is a **regular value** of `\rho(x)=\|x\|^2` restricted to `X`. Sard's theorem guarantees regular
  values exist — but Sard alone is not enough.
- **Nonempty:** a regular value of `\rho` might fail to be *attained* (then `X\cap S=\varnothing`, vacuously
  a manifold but disallowed). One must pick the value **inside the image** `\rho(X)`, not merely a regular
  value somewhere on `\mathbb R`.
- **A genuine sphere:** the value must be **positive** (radius `>0`), which is delicate because `\rho\ge0`
  and the value `0` (the degenerate "sphere" `\{0\}`) must be avoided.

And there is a genuinely different **degenerate case**: if `X` lies entirely on one sphere (`\rho` constant),
that sphere has *no* regular value in its image, yet `X\cap S=X` is a manifold anyway. Connectedness of `X`
is what makes `\rho(X)` an interval, so that — when `\rho` is non-constant — its interior is a nonempty open
set of attained, positive values in which Sard can find a regular one.

## The Key Insight

Let `\rho:X\to\mathbb R`, `\rho(x)=\|x\|^2`. Then `X\cap S_r=\rho^{-1}(r^2)`, so spheres centered at `0`
correspond to level sets of `\rho`. If `c=r^2` is a **regular value** of `\rho`, the regular-value theorem
makes `\rho^{-1}(c)=X\cap S_r` a smooth submanifold.

- If `\rho` is **constant** `=c_0` (so `X` lies on the sphere `S_{\sqrt{c_0}}`, and `c_0>0` since `X` has a
  nonzero point), then `X\cap S_{\sqrt{c_0}}=X` is a nonempty manifold.
- If `\rho` is **non-constant**, then `\rho(X)` is a *nondegenerate interval* (`X` connected), so its interior
  `(a,b)\subseteq(0,\infty)` is nonempty; by **Sard**, pick a regular value `c\in(a,b)`. It is attained (so
  `X\cap S_{\sqrt c}\ne\varnothing`) and positive (so `S_{\sqrt c}` is a genuine sphere), and
  `\rho^{-1}(c)=X\cap S_{\sqrt c}` is a smooth manifold.

## Complete Proof

Let `X\subseteq\mathbb R^n` be a nonempty connected smooth submanifold of dimension `k\ge1`. Write `S_r=\{x:
\|x\|=r\}` for the sphere of radius `r>0` centered at `0`, and define the smooth function
$$
\rho:X\to\mathbb R, \qquad \rho(x)=\|x\|^2 = \textstyle\sum_i x_i^2 .
$$
For any `r>0`,
$$
X\cap S_r = \{x\in X:\|x\|=r\} = \{x\in X:\rho(x)=r^2\} = \rho^{-1}(r^2).
$$

**`X` contains a nonzero point.** Since `\dim X=k\ge1`, `X` is not a single point (a positive-dimensional
manifold is uncountable), so some `x_*\in X` has `x_*\ne0`, giving `\rho(x_*)=\|x_*\|^2>0`. Hence `\rho` takes
a positive value.

### Case 1: `\rho` is constant on `X`

Say `\rho\equiv c_0`. By the previous paragraph `c_0=\rho(x_*)>0`. Then every point of `X` has norm
`\sqrt{c_0}`, i.e. `X\subseteq S_{\sqrt{c_0}}`, so
$$
X\cap S_{\sqrt{c_0}} = X,
$$
which is a nonempty smooth manifold. Taking `S=S_{\sqrt{c_0}}` finishes this case.

### Case 2: `\rho` is non-constant

**`\rho(X)` is a nondegenerate interval.** `X` is connected and `\rho` continuous, so `\rho(X)\subseteq
[0,\infty)` is connected, i.e. an interval; being non-constant, it contains more than one point, so it is a
nondegenerate interval and its interior `\operatorname{int}\rho(X)=(a,b)` (with `a=\inf\rho(X)`,
`b=\sup\rho(X)`) is a **nonempty** open interval. Since `a=\inf\rho(X)\ge0`, every point of `(a,b)` is
`>a\ge0`, so
$$
\operatorname{int}\rho(X)=(a,b)\subseteq(0,\infty).
$$

**Choose a regular value (Sard).** `\rho:X\to\mathbb R` is a smooth map to `\mathbb R`, so by **Sard's
theorem** its set of critical values has Lebesgue measure zero in `\mathbb R`. The open interval `(a,b)` has
positive length, so it cannot be contained in a measure-zero set; hence there exists a **regular value**
$$
c\in(a,b)=\operatorname{int}\rho(X).
$$

**Conclude.** This `c` has the three needed properties:

- `c\in(a,b)\subseteq\rho(X)`, so `c` is **attained**: `\rho^{-1}(c)\ne\varnothing`, i.e. `X\cap S_{\sqrt
  c}\ne\varnothing`;
- `c>0`, so `\sqrt c>0` and `S_{\sqrt c}` is a **genuine sphere**;
- `c` is a **regular value** of `\rho`, so by the **regular value theorem**, `\rho^{-1}(c)` is a smooth
  submanifold of `X` (of dimension `k-1`).

Therefore `X\cap S_{\sqrt c}=\rho^{-1}(c)` is a nonempty smooth manifold, and `S=S_{\sqrt c}` is the required
sphere. ∎

**Remark.** The proof recasts "intersect with a sphere" as "take a level set of `\rho=\|\cdot\|^2`," reducing
the problem to finding a regular value of `\rho` *inside its image*. Sard supplies regularity (almost every
value works), connectedness of `X` makes the image an interval so that its interior is an open set of
*attained* values, and `\rho\ge0` plus passing to the interior guarantees *positivity* (a real sphere, not
the point `\{0\}`). The constant case — `X` contained in a single sphere — is the one place the regular-value
machinery is silent (`\rho` has no regular values at all), but there the intersection is all of `X`, a
manifold by fiat. Geometrically, for generic radii the sphere is *transverse* to `X` and slices it into a
codimension-one submanifold; the content of the problem is that "generic radius" can be chosen so the slice
is also nonempty, which is exactly what "regular value in the interior of the image" delivers.
