<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m96J06: Local solvability of a nonlinear functional equation via the contraction mapping / inverse function theorem

## Why It's Hard

The equation
$$x(t) - 2x(0) + x\big(\tfrac t2+1\big)\,x\big(\tfrac t2-1\big) = y(t), \qquad |t|\le 2,$$
is **nonlinear** (it has the quadratic term `x(t/2+1)x(t/2−1)`) and **nonlocal** (the value of the
unknown `x` at `t` is coupled to its values at the *shifted, rescaled* points `t/2±1`). There is no hope
of solving it pointwise or by an explicit formula. The right move is to read it as a single equation
`Φ(x) = y` between Banach spaces and invert `Φ` near the known solution `Φ(0) = 0`. Three things have to
be checked, and each is a genuine step:

- **The map stays inside the space.** For `|t| ≤ 2` the arguments `t/2+1` and `t/2−1` must again lie in
  `[-2,2]` (they do, landing in `[0,2]` and `[-2,0]`), or `Φ(x)` would not even be defined on `[-2,2]`.
- **The linearization at `0` must be invertible** — and this is the subtle part, because the linear part
  `x(t) − 2x(0)` is *not* the identity; the `−2x(0)` term couples every value to the value at the origin.
  One has to actually solve `x(t) − 2x(0) = z(t)` and verify the inverse is bounded. (Pleasantly, this
  linear operator turns out to be its **own inverse** — an involution.)
- **The quadratic term must be controlled** uniformly on a small ball, with a Lipschitz constant that can
  be made `< 1` by shrinking the ball — which is exactly what restricts `y` to a *small* neighborhood of
  `0`.

The standard reflex "apply the inverse function theorem" hides all three of these under one citation; the
honest proof carries them out, and the cleanest way is a direct **contraction mapping** argument that
also pins down an explicit neighborhood.

## The Key Insight

Write the equation as `Φ(x) = y` with
$$\Phi(x)(t) = \underbrace{x(t) - 2x(0)}_{L(x)(t)} \;+\; \underbrace{x(\tfrac t2+1)\,x(\tfrac t2-1)}_{Q(x)(t)},$$
splitting `Φ = L + Q` into a **bounded linear** part `L` and a **quadratic** (hence `O(‖x‖²)`,
derivative-`0`-at-`0`) part `Q`. The linear part is invertible — in fact `L^{-1} = L`:
$$L(x)(t) = x(t) - 2x(0) \quad\Longrightarrow\quad L^{-1}(z)(t) = z(t) - 2z(0), \qquad L^2 = I,\ \ \|L^{-1}\| \le 3.$$
So `Φ` is a `C¹` perturbation of an isomorphism, and the inverse function theorem applies. Concretely,
apply `L^{-1}` to `Φ(x)=y` and rearrange into a **fixed-point equation**
$$x = T(x) := L^{-1}\big(y - Q(x)\big).$$
On a small closed ball the quadratic term `Q` is Lipschitz with a tiny constant, so `T` is a contraction
that maps the ball into itself once `‖y‖` is small enough. Banach's fixed-point theorem then delivers the
solution `x ∈ C([-2,2])`.

## Complete Proof

Work in the Banach space `X = C([-2,2])` with the sup norm `‖x‖ = \max_{|t|\le 2}|x(t)|`.

### Step 0: `Φ` is a well-defined map `X → X`

For `|t| ≤ 2` we have `t/2 ∈ [-1,1]`, so
$$\tfrac t2 + 1 \in [0,2] \subseteq [-2,2], \qquad \tfrac t2 - 1 \in [-2,0] \subseteq [-2,2].$$
Hence for `x ∈ X` the compositions `t ↦ x(t/2+1)` and `t ↦ x(t/2−1)` are defined and continuous on
`[-2,2]` (continuous `x` composed with continuous affine maps), their product is continuous, and `x(t)`,
`x(0)` are too. Therefore
$$\Phi(x)(t) = x(t) - 2x(0) + x(\tfrac t2+1)x(\tfrac t2-1) \in C([-2,2]) = X.$$
Note `Φ(0) = 0`, so `x = 0` solves the equation for `y = 0`.

### Step 1: the linear part `L` is an invertible isometry-class operator (`L^{-1} = L`)

Define `L : X → X` by `L(x)(t) = x(t) - 2x(0)`. It is linear and bounded: `|L(x)(t)| ≤ ‖x‖ + 2‖x‖ = 3‖x‖`,
so `‖L‖ ≤ 3`.

Solve `L(x) = z`. Evaluating `x(t) - 2x(0) = z(t)` at `t = 0` gives `-x(0) = z(0)`, i.e. `x(0) = -z(0)`;
substituting back, `x(t) = z(t) + 2x(0) = z(t) - 2z(0)`. Thus `L` is a bijection with

$$L^{-1}(z)(t) = z(t) - 2z(0), \qquad \|L^{-1}\| \le 3.$$

(Indeed `L^{-1}` has the same form as `L`, so `L^2 = I`; one checks directly
`L(L(x))(t) = (x(t)-2x(0)) - 2(x(0)-2x(0)) = x(t)`.) In particular `L` is a Banach-space isomorphism of
`X`.

### Step 2: the quadratic part `Q` is locally Lipschitz with small constant

Define `Q : X → X` by `Q(x)(t) = x(t/2+1)\,x(t/2−1)`. Abbreviate `a = a(t) = t/2+1`, `b = b(t) = t/2−1`.
For `x, x' ∈ X`, the bilinear identity `pq - p'q' = p(q-q') + (p-p')q'` gives, pointwise,

$$
Q(x)(t) - Q(x')(t) = x(a)\big(x(b)-x'(b)\big) + \big(x(a)-x'(a)\big)x'(b),
$$

so

$$
|Q(x)(t) - Q(x')(t)| \le \|x\|\,\|x-x'\| + \|x-x'\|\,\|x'\| = \big(\|x\| + \|x'\|\big)\,\|x-x'\|.
$$

Taking the sup over `t`,
$$
\|Q(x) - Q(x')\| \le \big(\|x\| + \|x'\|\big)\,\|x - x'\|. \tag{$\star$}
$$
Also, setting `x' = 0` (so `Q(0)=0`), `‖Q(x)‖ ≤ ‖x‖²`.

### Step 3: reformulate as a fixed-point problem and contract

Since `L` is invertible, `Φ(x) = y ⟺ L(x) = y - Q(x) ⟺ x = L^{-1}(y - Q(x))`. Define
$$
T(x) := L^{-1}\big(y - Q(x)\big).
$$
A fixed point of `T` is exactly a solution of the original equation. Fix the radius `r = \tfrac{1}{12}`
and let `\bar B_r = \{x ∈ X : ‖x‖ ≤ r\}`, a complete metric space (closed subset of a Banach space).

**`T` is a contraction on `\bar B_r`.** For `x, x' ∈ \bar B_r`, using `‖L^{-1}‖ ≤ 3` and `(★)` with
`‖x‖,‖x'‖ ≤ r`,
$$
\|T(x) - T(x')\| = \|L^{-1}(Q(x') - Q(x))\| \le 3\,(\,r + r\,)\,\|x - x'\| = 6r\,\|x - x'\| = \tfrac12\|x-x'\|,
$$
so `T` is Lipschitz with constant `\tfrac12 < 1`.

**`T` maps `\bar B_r` into itself, provided `y` is small.** For `x ∈ \bar B_r`,
$$
\|T(x)\| = \|L^{-1}(y - Q(x))\| \le 3\big(\|y\| + \|Q(x)\|\big) \le 3\|y\| + 3r^2.
$$
With `r = \tfrac1{12}`, `3r^2 = \tfrac{3}{144} = \tfrac1{48}`. Hence if
$$
\|y\| \le \tfrac1{48} \quad\Big(\text{then } 3\|y\| \le \tfrac{1}{16} = \tfrac{3}{48}\Big),
$$
we get `‖T(x)‖ ≤ \tfrac{3}{48} + \tfrac{1}{48} = \tfrac{4}{48} = \tfrac1{12} = r`, so `T(x) ∈ \bar B_r`.

### Step 4: conclusion

Let `W = \{ y ∈ C([-2,2]) : \|y\| < \tfrac1{48} \}`, an open neighborhood of `0` in `C([-2,2])`. For
every `y ∈ W`, Steps 3 show that `T : \bar B_{1/12} → \bar B_{1/12}` is a contraction with constant
`\tfrac12`. By the **Banach fixed-point theorem**, `T` has a (unique) fixed point `x ∈ \bar B_{1/12} ⊆
C([-2,2])`, which satisfies
$$
x(t) - 2x(0) + x(\tfrac t2+1)x(\tfrac t2-1) = y(t), \qquad |t| \le 2.
$$
Thus the equation has a solution `x ∈ C([-2,2])` for every `y` in the small open neighborhood `W` of `0`.
∎

**Remark.** This is the inverse function theorem in Banach spaces made explicit: `Φ = L + Q` is `C¹` with
`DΦ(0) = L` an isomorphism (the quadratic `Q` has `DQ(0)=0`), so `Φ` is a local diffeomorphism at `0` and
`Φ(x)=y` is solvable for `y` near `Φ(0)=0`. The contraction argument both *proves* this in the case at
hand and yields a concrete neighborhood `‖y‖ < 1/48` together with a quantitative solution bound
`‖x‖ ≤ 1/12`; the fixed point is in fact the *unique* small solution. The only structural facts used are
the invertibility of the linearization (Step 1) and the quadratic — hence locally small-Lipschitz —
nature of the nonlinearity (Step 2).
