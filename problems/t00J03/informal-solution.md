<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t00J03: Integrating the descended angle form over ℝP¹ — the half-turn and a degree-2 cover

## Why It's Hard

The form `\eta = \dfrac{x^0\,dx^1 - x^1\,dx^0}{(x^0)^2+(x^1)^2}` is the familiar **angle form** `d\theta` on
`ℝ^2\setminus\{0\}`, whose integral over the *full* circle is `2\pi`. The trap is to assume the answer over
`ℝP^1` is therefore `2\pi` (or `\pi` by "half," guessed without justification). Three things have to be got
right:

- **Why the form descends at all.** For `\eta` to define a form `\omega` on the quotient `ℝP^1 =
  (ℝ^2\setminus\{0\})/\sim`, it must be invariant under *all* the rescalings `(x^0,x^1)\mapsto(\lambda
  x^0,\lambda x^1)`, `\lambda\ne 0` — including `\lambda<0` (the antipodal identification). One checks
  `\eta` is homogeneous of degree `0`, hence invariant; this is exactly the hypothesis "`\eta` descends."
- **`ℝP^1` is only "half" a circle's worth of angle.** A point of `ℝP^1` is a *line* through the origin,
  determined by its direction **mod `\pi`**, not mod `2\pi`: the angles `\theta` and `\theta+\pi` give the
  same line. So one full traversal of `ℝP^1` corresponds to `\theta` sweeping an interval of length `\pi`,
  not `2\pi`. Getting this factor right is the crux, and it is *why* the answer is `\pi`.
- **Orientation must be pinned down**, since the problem demands it: `\omega` is nowhere zero, so it
  *defines* an orientation of `ℝP^1`; the sign of the integral (`+\pi` vs `-\pi`) is exactly the choice of
  which way to traverse. The clean cross-check is the **degree-2 covering** `S^1\to ℝP^1`, which forces
  `\int_{ℝP^1}\omega = \tfrac12\int_{S^1} d\theta = \pi`.

## The Key Insight

`\eta = d\theta` is the angle form, invariant under all rescalings, so it descends to a nowhere-vanishing
1-form `\omega` on `ℝP^1 \cong S^1`. Because antipodal directions are identified, **traversing `ℝP^1` once
advances `\theta` by `\pi`**, so
$$\int_{ℝP^1}\omega = \int_{\theta=0}^{\pi} d\theta = \pi,$$
with the orientation for which `\omega` is positive (the opposite orientation gives `-\pi`). Equivalently,
the unit circle `S^1 \to ℝP^1` is a degree-`2` cover pulling `\omega` back to `d\theta`, and
`\int_{S^1} d\theta = 2\pi = 2\int_{ℝP^1}\omega`.

## Complete Proof

### Step 1: the form is the angle form, and it descends

On `ℝ^2 \setminus \{0\}`, in polar coordinates `x^0 = r\cos\theta`, `x^1 = r\sin\theta`, one has the
standard identity
$$
\eta := \frac{x^0\,dx^1 - x^1\,dx^0}{(x^0)^2 + (x^1)^2} = d\theta ,
$$
the angle 1-form (closed, `d\eta = 0`, but not exact — `\theta` is only locally defined).

*Invariance under rescaling.* Under `(x^0,x^1) \mapsto (\lambda x^0, \lambda x^1)` with `\lambda \ne 0`, the
numerator `x^0\,dx^1 - x^1\,dx^0` scales by `\lambda^2` and the denominator `(x^0)^2+(x^1)^2` scales by
`\lambda^2`, so `\eta` is unchanged: it is homogeneous of degree `0`. In particular `\eta` is invariant
under the antipodal map `(\lambda = -1)`. Hence `\eta` is constant on the equivalence classes of `ℝP^1` and
descends: there is a 1-form `\omega` on `ℝP^1` with `\pi^*\omega = \eta`, where `\pi : ℝ^2\setminus\{0\} \to
ℝP^1` is the quotient projection. (This is the content of "the form descends.") Since `d\theta` is nowhere
zero, `\omega` is a nowhere-vanishing 1-form on `ℝP^1`.

### Step 2: `ℝP^1` is a circle; a fundamental domain is a half-turn

Every point of `ℝP^1` is a line through the origin, which meets the unit circle `S^1 = \{(\cos\theta,
\sin\theta)\}` in a pair of antipodal points `\theta` and `\theta + \pi`. Thus directions are parametrized
by `\theta \in [0,\pi]` with the endpoints `\theta = 0` and `\theta = \pi` (the same line `[1:0]=[-1:0]`)
identified — so `ℝP^1` is topologically a **circle**, and the semicircular arc
$$
\gamma(\theta) = (\cos\theta, \sin\theta), \qquad \theta \in [0,\pi],
$$
projects under `\pi` onto all of `ℝP^1`, bijectively on `[0,\pi)` and once around. (A `1`-manifold is always
orientable; `\omega`, being nowhere zero, picks out an orientation.)

### Step 3: compute the integral

Integrate `\omega` over `ℝP^1` by pulling back along the parametrization `\theta \mapsto \pi(\gamma(\theta))`,
`\theta : 0 \to \pi`. Since `\pi^*\omega = \eta = d\theta` and `\gamma` is the unit-circle arc,
$$
\int_{ℝP^1}\omega = \int_{[0,\pi]} \gamma^*\eta = \int_{0}^{\pi} d\theta = \boxed{\pi},
$$
taken with the orientation of `ℝP^1` for which `\omega > 0` (i.e. increasing `\theta`). With the opposite
orientation the value is `-\pi`.

### Step 4: orientation discussion and cross-check via the double cover

**Orientation.** `ℝP^1` is an orientable `1`-manifold, and the nowhere-vanishing form `\omega` *defines* an
orientation: declare a tangent direction positive when `\omega` evaluates positively on it. This is the
orientation in which `\theta` increases, and it is the one inherited from the standard (counterclockwise)
orientation of `ℝ^2` via the projection. With this canonical choice `\int_{ℝP^1}\omega = +\pi`; reversing
the orientation negates the integral to `-\pi`. The *magnitude* `\pi` is orientation-independent.

**Cross-check (degree-2 cover).** The map `p : S^1 \to ℝP^1`, `(\cos\theta,\sin\theta) \mapsto [\cos\theta :
\sin\theta]`, identifies antipodal points, so it is a **2-sheeted covering** (degree `2`). By construction
`p^*\omega = \eta = d\theta` on `S^1`, and integration over a covering multiplies by the degree:
$$
\int_{S^1} d\theta = \int_{S^1} p^*\omega = (\deg p)\int_{ℝP^1}\omega = 2\int_{ℝP^1}\omega .
$$
Since `\int_{S^1} d\theta = 2\pi`, this gives `\int_{ℝP^1}\omega = \pi`, confirming Step 3. ∎

**Remark.** The whole computation is the statement that `ℝP^1` carries "half the angle" of the circle: the
identification of antipodal directions folds the `2\pi` of `S^1` down to `\pi`. The form `\omega` is the
generator of `H^1_{dR}(ℝP^1)\cong\mathbb R` (note `ℝP^1` is orientable, unlike `ℝP^2`), and its integral
`\pi` is the period that detects this nontrivial cohomology class — the projective-line analogue of the
`2\pi` period of `d\theta` on the circle. The required "discussion of orientation" is precisely that `\omega`
itself fixes the sign: `+\pi` for the orientation it induces.
