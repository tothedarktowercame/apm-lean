<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m02J06: Mollification and Kolmogorov–Riesz compactness in L¹

## Why It's Hard

This is a compactness problem in an *infinite-dimensional* space, so Heine–Borel
is useless: closed and bounded does not imply compact in `L¹(ℝ)`. You need a
genuine compactness criterion — the Kolmogorov–Riesz–Fréchet theorem — whose
hypotheses are (i) uniform boundedness, (ii) uniform `L¹`-equicontinuity of
translation, and (iii) uniform decay at infinity.

The subtlety is that the smoothness you are *handed* is the wrong **kind**. The
defining bound on `K` is an *averaged* (L¹) modulus of continuity,
`∫|f(x+h)−f(x)|dx ≤ h^{1/2}`. The functions in `K` need not be continuous at all,
so Arzelà–Ascoli — the tool you instinctively want — cannot touch `K` directly.

The whole problem is a single engineered maneuver: **mollify**. Convolving with
`φ_ε` turns each rough `f` into an honestly continuous `f ∗ φ_ε`. Part (a) says
the mollified copy is uniformly close to the original; part (b) says the
mollified family is genuinely (pointwise) equicontinuous, with the L¹ Hölder-½
bound reincarnated as a *pointwise* Hölder-½ bound. Then Arzelà–Ascoli applies to
the smooth family, and the uniform approximation of (a) transfers total
boundedness back down to `K`. Parts (a) and (b) are not side-quests; they are the
scaffolding of part (c).

## The Key Insight

The mollifier is a **bridge between two notions of smoothness**: the weak,
averaged `L¹` modulus of continuity that `K` actually possesses, and the strong,
pointwise equicontinuity that Arzelà–Ascoli demands.

Both convolution estimates collapse onto the *same* one-line input — the single
translation bound `‖τ_t f − f‖₁ ≤ |t|^{1/2}` — which is exactly the defining
property of `K`. In (a) you integrate that bound against `φ_ε` (supported in
`|t| ≤ ε`), so the error inherits `ε^{1/2}`. In (b) you pull the difference of
translates out under the integral and integrate against `|φ_ε| ≤ M/ε`, so the
modulus inherits `(M/ε)|x−y|^{1/2}`. The Hölder exponent ½ survives untouched in
both directions because each estimate reduces to that one translation bound. Once
the smooth family `K_ε` is uniformly bounded, uniformly compactly supported, and
Hölder-½ equicontinuous, Arzelà–Ascoli finishes it, and `ε^{1/2} → 0` does the
rest.

## Complete Proof

Throughout, `‖·‖` denotes the `L¹(ℝ)` norm and `τ_t f(x) := f(x − t)`. We assume
the standard *nonnegative* mollifier: `φ ∈ C_0^∞(ℝ)`, `φ ≥ 0`, `∫φ = 1`,
`φ(x) = 0` for `|x| ≥ 1`, and `max|φ| = M`. Then
`φ_ε(x) = ε^{-1} φ(x/ε)` satisfies `φ_ε ≥ 0`, `∫φ_ε = 1`,
`max|φ_ε| = M/ε`, and `φ_ε(t) = 0` for `|t| ≥ ε`.

**The one translation bound we use repeatedly.** The defining property of `K`,
`∫|f(x+h) − f(x)|dx ≤ h^{1/2}` for `h > 0`, extends to all real `t` by
translation invariance of Lebesgue measure: for `t < 0`, writing `t = −s` with
`s > 0` and substituting `y ↦ y + s`,
`∫|f(y+t) − f(y)|dy = ∫|f(y) − f(y+s)|dy ≤ s^{1/2} = |t|^{1/2}`. Hence

$$\|\tau_t f - f\| = \int |f(x-t) - f(x)|\,dx \le |t|^{1/2}\quad\text{for all }t\in\mathbb{R}. \tag{$\ast$}$$

---

### (a)  `‖f − f ∗ φ_ε‖ ≤ ε^{1/2}`

Since `∫φ_ε = 1`, we may write `f(x) = ∫ f(x)\,φ_ε(t)\,dt`, so

$$f(x) - (f \ast \varphi_\epsilon)(x) = \int \big[f(x) - f(x-t)\big]\,\varphi_\epsilon(t)\,dt.$$

Taking absolute values, using `φ_ε ≥ 0`, and integrating in `x`, Tonelli's
theorem lets us swap the order of integration:

$$\|f - f\ast\varphi_\epsilon\|
= \int_x \left| \int_t [f(x)-f(x-t)]\varphi_\epsilon(t)\,dt \right| dx
\le \int_t \varphi_\epsilon(t) \left( \int_x |f(x)-f(x-t)|\,dx \right) dt.$$

The inner integral is `‖f − τ_t f‖ ≤ |t|^{1/2}` by `(∗)`. Since `φ_ε` is
supported in `|t| ≤ ε`, we have `|t|^{1/2} ≤ ε^{1/2}` on that support, so

$$\|f - f\ast\varphi_\epsilon\| \le \int_t \varphi_\epsilon(t)\,|t|^{1/2}\,dt
\le \epsilon^{1/2} \int \varphi_\epsilon(t)\,dt = \epsilon^{1/2}\cdot 1 = \epsilon^{1/2}.$$

This bound is **uniform over** `f ∈ K`, since `(∗)` holds for every `f ∈ K`. ∎

---

### (b)  `K_ε` is equicontinuous:  `|f ∗ φ_ε(x) − f ∗ φ_ε(y)| ≤ (M/ε)|x−y|^{1/2}`

Write the convolution as `(f ∗ φ_ε)(x) = ∫ f(x−t)\,φ_ε(t)\,dt`. Then

$$(f\ast\varphi_\epsilon)(x) - (f\ast\varphi_\epsilon)(y)
= \int \big[f(x-t) - f(y-t)\big]\,\varphi_\epsilon(t)\,dt,$$

so, bounding `|φ_ε| ≤ max|φ_ε| = M/ε`,

$$\big|(f\ast\varphi_\epsilon)(x) - (f\ast\varphi_\epsilon)(y)\big|
\le \frac{M}{\epsilon} \int |f(x-t) - f(y-t)|\,dt.$$

Substitute `u = y − t` (Lebesgue measure is translation invariant), so
`x − t = u + (x−y)`:

$$\int |f(x-t) - f(y-t)|\,dt = \int |f(u + (x-y)) - f(u)|\,du = \|\tau_{-(x-y)} f - f\| \le |x-y|^{1/2}$$

by `(∗)` with `t = −(x−y)`. Therefore

$$\big|(f\ast\varphi_\epsilon)(x) - (f\ast\varphi_\epsilon)(y)\big|
\le \frac{M}{\epsilon}\,|x-y|^{1/2},$$

with the same `M`, and the bound is identical for every `f ∈ K` — i.e. `K_ε` is
(uniformly) equicontinuous, indeed uniformly Hölder-½. ∎

---

### (c)  `K` is compact in `L¹(ℝ)`

We read the third defining condition of `K` as the **uniform compact-support
(tightness)** requirement that there is a fixed bounded set outside of which
every `f ∈ K` vanishes; concretely, take `f(x) = 0` for `|x| ≥ 1` for all
`f ∈ K`. (This is the condition Kolmogorov–Riesz needs to control mass escaping
to infinity; the source statement is garbled at this point.) We show `K` is
**totally bounded** and **closed** in the complete space `L¹(ℝ)`, hence compact.

**Step 1 — Reduce to `K_ε`.** Fix `η > 0` and choose `ε ∈ (0,1]` with
`ε^{1/2} < η/2`. By part (a), every `f ∈ K` lies within `η/2` (in `L¹`) of
`f ∗ φ_ε ∈ K_ε`. Hence any finite `(η/2)`-net for `K_ε` in `L¹` becomes a finite
`η`-net for `K` (enlarge each ball's radius from `η/2` to `η`). So it suffices to
show `K_ε` is totally bounded in `L¹`.

**Step 2 — `K_ε` is a nice family on a fixed compact set.** Let `g = f ∗ φ_ε`
with `f ∈ K`.

- *Fixed compact support.* `f` is supported in `[−1,1]` and `φ_ε` in `[−ε,ε]`, so
  `g` is supported in `[−1−ε, 1+ε] ⊆ [−2,2]` (as `ε ≤ 1`).
- *Uniform sup bound.* For each `x`,
  `|g(x)| = |∫ f(x−t)φ_ε(t)\,dt| ≤ max|φ_ε|\cdot\|f\| ≤ (M/ε)\cdot 1 = M/ε`,
  using `‖f‖ ≤ 1`. So `‖g‖_∞ ≤ M/ε` uniformly over `K_ε`.
- *Equicontinuity.* By part (b), `|g(x) − g(y)| ≤ (M/ε)|x−y|^{1/2}` — a single
  modulus of continuity for the whole family.

**Step 3 — Arzelà–Ascoli, then back to `L¹`.** On the fixed compact interval
`[−2,2]`, `K_ε` is a uniformly bounded, equicontinuous family of continuous
functions, so by the **Arzelà–Ascoli theorem** it is totally bounded in
`C([−2,2])` under the sup norm. Because every `g ∈ K_ε` is supported in `[−2,2]`
(length `4`), sup-norm proximity controls `L¹` proximity:

$$\|g - g'\| = \int_{-2}^{2} |g - g'|\,dx \le 4\,\|g - g'\|_\infty.$$

Thus a finite `(δ/4)`-net of `K_ε` in `C([−2,2])` is a finite `δ`-net in `L¹`, and
`K_ε` is **totally bounded in `L¹`**. By Step 1, so is `K`.

**Step 4 — `K` is closed.** Each defining condition is preserved under `L¹`
limits. Suppose `f_n ∈ K` and `f_n → f` in `L¹`.

- `‖f‖ = lim ‖f_n‖ ≤ 1` (norm is continuous).
- For each fixed `h`, `τ_h f_n − f_n → τ_h f − f` in `L¹` (translation is an `L¹`
  isometry), so `∫|f(x+h)−f(x)|dx = lim ∫|f_n(x+h)−f_n(x)|dx ≤ h^{1/2}`.
- Some subsequence converges a.e., so `f = 0` a.e. on `|x| ≥ 1` as well.

Hence `f ∈ K`, and `K` is closed.

**Conclusion.** `K` is a closed, totally bounded subset of the complete metric
space `L¹(ℝ)`. A closed totally bounded subset of a complete space is compact.
Therefore `K` is compact. ∎
