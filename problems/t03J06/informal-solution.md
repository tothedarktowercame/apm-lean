<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t03J06: A deliberately messy 2-form — dω = 3 dx∧dy∧dz, and ∫_B ω = 7π by capping with a disk

## Why It's Hard

The 2-form `\omega` is built to look terrifying: coefficients like `z^2 e^{xz}\ln(x^2+1)` and
`y^2z^3\cos(y^2+z^2)` make a *direct* surface integral over the bullet `B` hopeless. The entire problem is
designed so that **the mess never has to be integrated**:

- **(a)** Computing `d\omega` only invokes *one specific partial derivative* of each ugly coefficient, and in
  every case the scary term has no dependence on the relevant variable, so it differentiates to `0`. What
  survives is `d\omega = 3\,dx\wedge dy\wedge dz` — clean. Recognizing that closedness is decided by this
  one tidy computation (and that *not closed ⇒ not exact*) is the first hurdle.
- **(b)** `B` is a surface *with boundary* (open at the bottom), and `\omega` is *not closed*, so neither
  "Stokes makes it zero" nor "it's exact" applies. The trick is to **cap** `B` with the bottom disk `D` to
  form the closed boundary `\partial V` of the solid bullet `V`, then use the divergence form of Stokes:
  `\int_{\partial V}\omega = \int_V d\omega`. This replaces the impossible integral over the curved `B` by a
  trivial volume integral of the constant `3` plus a trivial flux through the flat disk `D` (where `dz = 0`
  kills all the bad terms). The subtleties are getting the **orientations** consistent (the given
  "`dx\wedge dy>0` at the top" must be the outward orientation) and computing `\int_D\omega` correctly with
  the downward outward normal.

## The Key Insight

Differentiate: every ugly coefficient is independent of the variable it would be differentiated by, so
$$
d\omega = \big(\partial_z z - \partial_y(\cdots - y) + \partial_x(x + \cdots)\big)\,dx\wedge dy\wedge dz = (1 - (-1) + 1)\,dx\wedge dy\wedge dz = 3\,dx\wedge dy\wedge dz \ne 0,
$$
so `\omega` is **not closed**, hence **not exact**. For the integral, cap `B` with the bottom disk `D` so
`B\cup D = \partial V` (solid bullet `V`), oriented outward (which matches the given orientation of `B`).
Then
$$
\int_B \omega = \int_V d\omega - \int_D \omega = 3\,\mathrm{vol}(V) - \int_D\omega = 3\cdot\tfrac{8\pi}{3} - \pi = 8\pi - \pi = 7\pi.
$$

## Complete Proof

Write `\omega = P\,dx\wedge dy + Q\,dx\wedge dz + R\,dy\wedge dz` with
$$
P = z,\qquad Q = z^2 e^{xz}\ln(x^2+1) - y,\qquad R = x + y^2 z^3\cos(y^2+z^2).
$$

### (a) `\omega` is not closed (hence not exact)

For a `2`-form in `\mathbb R^3`, only the "third" partial of each coefficient survives in `d\omega`:
$$
d\omega = \frac{\partial P}{\partial z}\,dz\wedge dx\wedge dy + \frac{\partial Q}{\partial y}\,dy\wedge dx\wedge dz + \frac{\partial R}{\partial x}\,dx\wedge dy\wedge dz = \Big(\frac{\partial P}{\partial z} - \frac{\partial Q}{\partial y} + \frac{\partial R}{\partial x}\Big)\,dx\wedge dy\wedge dz,
$$
using `dz\wedge dx\wedge dy = dx\wedge dy\wedge dz` and `dy\wedge dx\wedge dz = -\,dx\wedge dy\wedge dz`.
Now compute the three partials — crucially, each complicated term is independent of the differentiating
variable and drops out:
$$
\frac{\partial P}{\partial z} = \partial_z(z) = 1, \qquad
\frac{\partial Q}{\partial y} = \partial_y\big(z^2 e^{xz}\ln(x^2+1) - y\big) = -1, \qquad
\frac{\partial R}{\partial x} = \partial_x\big(x + y^2z^3\cos(y^2+z^2)\big) = 1.
$$
Therefore
$$
\boxed{\ d\omega = \big(1 - (-1) + 1\big)\,dx\wedge dy\wedge dz = 3\,dx\wedge dy\wedge dz \ne 0.\ }
$$
Since `d\omega \ne 0`, `\omega` is **not closed**. An exact form is always closed (`\omega = d\eta
\Rightarrow d\omega = d^2\eta = 0`), so `\omega` is also **not exact**.

### (b) `\int_B \omega = 7\pi`

**The solid bullet and its boundary.** Let `V` be the solid bullet: the solid cylinder
`\{x^2+y^2\le 1,\ -1\le z\le 1\}` together with the solid hemisphere
`\{x^2+y^2+(z-1)^2\le 1,\ z\ge 1\}`. Its boundary `\partial V` consists of the bullet surface `B` (lateral
cylinder + hemispherical cap) **plus** the bottom disk
$$
D = \{x^2+y^2\le 1,\ z = -1\}.
$$
So `\partial V = B \cup D`.

**Orientations.** Orient `\partial V` by the outward normal. At the top `(0,0,2)` the outward normal of `V`
is `+\partial_z`, and the area form for that normal is exactly `dx\wedge dy`; the problem orients `B` so that
`dx\wedge dy > 0` there, so the given orientation of `B` **is** the outward orientation. Thus
`\partial V = B\cup D`, both outward, and the divergence form of Stokes gives
$$
\int_B\omega + \int_D\omega = \int_{\partial V}\omega = \int_V d\omega, \qquad\text{i.e.}\qquad \int_B\omega = \int_V d\omega - \int_D\omega.
$$

**Volume integral.** By part (a), `d\omega = 3\,dx\wedge dy\wedge dz`, so
$$
\int_V d\omega = 3\int_V dx\,dy\,dz = 3\,\mathrm{vol}(V).
$$
The volume is cylinder plus hemisphere:
$$
\mathrm{vol}(V) = \underbrace{\pi\cdot 1^2\cdot 2}_{\text{cylinder, height }2} + \underbrace{\tfrac12\cdot\tfrac{4}{3}\pi\cdot 1^3}_{\text{hemisphere, radius }1} = 2\pi + \tfrac{2}{3}\pi = \tfrac{8\pi}{3},
$$
hence `\int_V d\omega = 3\cdot\tfrac{8\pi}{3} = 8\pi`.

**Disk integral.** On `D` we have `z\equiv -1`, so `dz = 0` and every term of `\omega` containing `dz`
vanishes; only `P\,dx\wedge dy` survives:
$$
\omega\big|_D = z\,dx\wedge dy = -\,dx\wedge dy \quad(\text{since } z=-1).
$$
Equivalently, writing `\omega` as a flux form `F\cdot n\,dA` with `F = (R, -Q, z)`, the bottom disk has
outward normal `n = (0,0,-1)`, so `F\cdot n = -z = -(-1) = 1` and
$$
\int_D\omega = \int_D F\cdot n\,dA = \int_D 1\,dA = \mathrm{Area}(D) = \pi\cdot 1^2 = \pi.
$$
(Consistently: with the downward outward normal, `\int_D(-\,dx\wedge dy) = -(-\mathrm{Area}) = \pi`.)

**Conclusion.**
$$
\int_B\omega = \int_V d\omega - \int_D\omega = 8\pi - \pi = \boxed{7\pi}.
$$
∎

**Remark.** The design is transparent once you see it: the frightening coefficients are arranged so that the
*one* partial derivative each contributes to `d\omega` annihilates them, leaving the constant `3`; and the
capping disk lies in a plane `z = \text{const}` where `dz = 0` strips `\omega` down to its harmless
`z\,dx\wedge dy` part. The whole computation is "differentiate to a constant, then integrate a constant over
a volume" plus a one-line flat-disk flux — never touching the curved bullet directly. This is the standard
divergence-theorem move for evaluating a flux through an awkward open surface: close it up with a convenient
cap, integrate the (simple) divergence over the enclosed solid, and subtract the (simple) cap flux. The
non-closedness of `\omega` is exactly what makes the volume term `3\,\mathrm{vol}(V)` nonzero and carry the
answer.
