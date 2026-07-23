<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t01A07: A smooth quartic surface in ℝP³ and its (vanishing) intersection number with a line

## Why It's Hard

The defining polynomial `F = X^4 - Y^4 - Z^4 + W^4` is **homogeneous of degree 4**, so it is *not a
function* on `\mathbb{RP}^3` (rescaling multiplies it by `\lambda^4`). One cannot just "apply the regular
value theorem to `F`"; the smoothness in (a) has to be established either chart-by-chart (where `F` becomes
an honest affine function) or via the projectivized cone. The recurring subtlety is that the gradient
`\nabla F = (4X^3, -4Y^3, -4Z^3, 4W^3)` vanishes only at the origin — which is *not a point of
`\mathbb{RP}^3`* — so one must confirm the critical locus never meets `S` in any chart.

Part (b) is where the real surprise lives. Naïvely counting real intersection points of `S` with the line
`\ell` gives **two** points (`X^4 = Y^4 \Rightarrow X = \pm Y`), and the complex Bézout count would be `4`.
But the *oriented* intersection number is neither `2` nor `4`: it is **0**, because the two real crossings
come with **opposite signs**. Seeing why the signs cancel — and confirming it conceptually — is the crux:
the even degree of `F` makes `\operatorname{sign}(F)` well-defined on `\mathbb{RP}^3\setminus S`, so `S`
*separates* `\mathbb{RP}^3` and is null-homologous (`H_2(\mathbb{RP}^3;\mathbb Z) = 0`), forcing every such
intersection number to vanish. Trusting the unsigned count (or Bézout) is the trap.

## The Key Insight

- **(a)** In each affine chart of `\mathbb{RP}^3`, `S` is the zero set of an affine function whose gradient
  vanishes only at the chart's origin — and that origin is *not on `S`* (the equation reads `\pm 1 = 0`
  there). So `0` is a regular value in every chart, and `S` is a smooth codimension-1 (hence
  `2`-dimensional) submanifold.
- **(b)** `S\cap\ell = \{[1{:}1{:}0{:}0],\ [1{:}{-}1{:}0{:}0]\}`, two transverse points. Restricted to
  `\ell = \{[\cos\theta:\sin\theta:0:0]\}`, `F = \cos^4\theta - \sin^4\theta = \cos 2\theta`: the loop
  `\ell` crosses `S` exactly where `\cos 2\theta` changes sign, and a closed loop changes sign an even
  number of times with **alternating** intersection signs. Hence
  $$I_{\mathbb{RP}^3}(S,\ell) = (+1) + (-1) = 0,$$
  consistent with `[S] = 0` in `H_2(\mathbb{RP}^3;\mathbb Z) = 0` (the even-degree `F` makes `S` separate
  `\mathbb{RP}^3`).

## Complete Proof

### (a) `S` is a smooth submanifold of `\mathbb{RP}^3`

`\mathbb{RP}^3` is covered by the four standard affine charts `U_X = \{X\ne 0\}, U_Y, U_Z, U_W`. We check `S`
is a regular level set in each.

**Chart `U_W` (`W\ne 0`).** Set `(x,y,z) = (X/W, Y/W, Z/W)`; dividing `F=0` by `W^4`, `S\cap U_W` is the zero
set of
$$
g(x,y,z) = x^4 - y^4 - z^4 + 1 .
$$
Its gradient `\nabla g = (4x^3, -4y^3, -4z^3)` vanishes **only** at `(x,y,z) = (0,0,0)`. But there
`g(0,0,0) = 1 \ne 0`, so no critical point of `g` lies on `S`. Hence every point of `S\cap U_W` is a regular
point, `0` is a regular value of `g`, and by the regular value (preimage) theorem `S\cap U_W` is a smooth
`2`-dimensional submanifold of `U_W \cong \mathbb R^3`.

**The other charts** are identical by symmetry. E.g. in `U_X` (`x'=1`), `S` is `\{1 - y^4 - z^4 + w^4 = 0\}`
with gradient `(-4y^3, -4z^3, 4w^3)` vanishing only at the origin, where the value is `1 \ne 0`; in `U_Y` the
value at the bad point is `-1 \ne 0`; in `U_Z`, `-1\ne 0`. In each chart `\nabla(\cdot)` vanishes only at the
chart origin, which is never on `S`.

Since the four charts cover `\mathbb{RP}^3` (hence `S`), `S` is a smooth submanifold of `\mathbb{RP}^3` of
dimension `2` (codimension `1`). ∎

*(Equivalently: `\nabla F` vanishes only at `0\in\mathbb R^4`, so `\hat S = F^{-1}(0)\setminus\{0\}` is a
smooth `\mathbb R^\times`-invariant `3`-submanifold of `\mathbb R^4\setminus\{0\}`, and its image under the
submersion `\mathbb R^4\setminus\{0\}\to\mathbb{RP}^3` is the smooth surface `S`.)*

### (b) `I_{\mathbb{RP}^3}(S, \ell) = 0`

Take `\ell = \{[X:Y:0:0]\}`, a projective line `\cong \mathbb{RP}^1`. Note `\dim S + \dim \ell = 2 + 1 = 3 =
\dim\mathbb{RP}^3`, so the intersection number is defined (both orientable, as given).

**The intersection points.** A point `[X:Y:0:0]` lies on `S` iff `X^4 - Y^4 - 0 + 0 = 0`, i.e.
`X^4 = Y^4`. Over `\mathbb R`, with `(X,Y)\ne(0,0)`, this gives `X = \pm Y`, so
$$
S\cap\ell = \{\,p_1 = [1:1:0:0],\quad p_2 = [1:-1:0:0]\,\} \quad(\text{two points}).
$$

**Transversality.** Work in chart `U_X` (`X\ne 0`), coordinates `(y,z,w) = (Y/X, Z/X, W/X)`, where `S` is
`g(y,z,w) = 1 - y^4 - z^4 + w^4 = 0` and `\ell = \{z = w = 0\}` is the `y`-axis (oriented by `+\partial_y`).
The two points are `p_1 = (1,0,0)` and `p_2 = (-1,0,0)`. Here `\nabla g = (-4y^3, -4z^3, 4w^3)`, so
$$
T_{p_i}S = \ker dg = \{v : \partial_y g\, (p_i)\, v_y = 0\} = \{v_y = 0\}\ (\text{the }z\text{-}w\text{ plane}),
$$
since `\partial_y g(p_i) = -4y^3 \ne 0` at `y = \pm 1`. The line direction `\partial_y` has `v_y = 1\ne 0`,
so `\partial_y \notin T_{p_i}S`; thus `T_{p_i}S \oplus T_{p_i}\ell = T_{p_i}\mathbb{RP}^3` — both
intersections are **transverse**.

**The signs cancel.** Coorient `S` by the gradient `\nabla g` and orient `\ell` by `+\partial_y`; the local
intersection sign at `p_i` is then `\operatorname{sign}\big(\partial_y g(p_i)\big)` (the sign with which the
oriented line pierces the cooriented hypersurface). Now
$$
\partial_y g = -4y^3:\qquad \partial_y g(p_1) = -4(1)^3 = -4 < 0,\qquad \partial_y g(p_2) = -4(-1)^3 = +4 > 0,
$$
so `\operatorname{sign}(p_1) = -1` and `\operatorname{sign}(p_2) = +1`. Therefore
$$
\boxed{\,I_{\mathbb{RP}^3}(S,\ell) = \operatorname{sign}(p_1) + \operatorname{sign}(p_2) = -1 + 1 = 0\,}.
$$

**Conceptual confirmation (why it must be `0`).** Restrict `F` to `\ell` via
`[\cos\theta : \sin\theta : 0 : 0]`:
$$
F\big|_\ell = \cos^4\theta - \sin^4\theta = (\cos^2\theta - \sin^2\theta)(\cos^2\theta + \sin^2\theta) = \cos 2\theta .
$$
As `\theta` traverses `\mathbb{RP}^1` (i.e. `\theta\in[0,\pi)`), `\cos 2\theta` is `+` on
`[0,\tfrac\pi4)\cup(\tfrac{3\pi}4,\pi)`, `-` on `(\tfrac\pi4,\tfrac{3\pi}4)`, vanishing exactly at
`\theta = \tfrac\pi4` (`= p_1`) and `\theta = \tfrac{3\pi}4` (`= p_2`). So the **closed** loop `\ell` passes
from the region `\{F>0\}` into `\{F<0\}` and back, crossing `S` twice with opposite orientations — net `0`.

This is no accident: because `F` has **even** degree, `F(\lambda p) = \lambda^4 F(p)` has the sign of
`F(p)`, so `\operatorname{sign}(F)` is well-defined on `\mathbb{RP}^3\setminus S`, splitting it into
`\{F>0\}` and `\{F<0\}`. Thus `S` **separates** `\mathbb{RP}^3` and is the boundary
`S = \partial\overline{\{F>0\}}` — a null-homologous hypersurface. Indeed `H_2(\mathbb{RP}^3;\mathbb Z) = 0`
(cellular complex `\mathbb Z\xrightarrow{0}\mathbb Z\xrightarrow{2}\mathbb Z\xrightarrow{0}\mathbb Z` gives
`H_2 = \ker(\times 2) = 0`), so `[S] = 0` and `I_{\mathbb{RP}^3}(S,\ell) = 0` for **every** line `\ell`,
independent of orientation conventions. ∎

**Remark.** The unsigned real count (`2`) and the complex Bézout number (`4`) both differ from the oriented
real intersection number (`0`); the discrepancy is exactly the alternating signs forced by `\ell` being a
closed loop crossing the separating surface `S`. The even degree of `F` is what does it: it both gives `S` a
global coorientation (so `S` is orientable, as stated) and makes `S` bound, killing all its intersection
numbers. A line through `S` an *odd* number of times (impossible here, since `S` separates) would be the
signature of a non-separating, homologically nontrivial surface — which a degree-4 surface in
`\mathbb{RP}^3` can never be.
