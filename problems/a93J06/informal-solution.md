# Informal Solution: a93J06

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.* The hypotheses look tailor-made for Schwarz’ lemma, but the derivative bound is on \(f'\), not on \(f\) itself, so the usual trick of dividing by \(z\) doesn’t immediately apply. Students often try to differentiate Schwarz or guess a power series bound without justification. The real issue is finding a controlled integral expression for \(f\) that exposes the derivative bound.

*Key insight.* Parametrize the straight segment from \(0\) to \(z\) and integrate \(f'\) along it:
\[
 f(z) = f(z) - f(0) = \int_0^1 \frac{d}{dt} f(tz)\,dt = \int_0^1 z f'(tz)\,dt.
\]
Taking absolute values and using \(|f'(tz)| ≤ 1\) for \(|z|<1\) turns the integral into \(|z|^2/2\).

*Complete proof.* Let \(|z|<1\). Define \(\gamma(t)=tz\) for \(0≤t≤1\); then
\(f(z)-f(0)=\int_0^1 f'(\gamma(t))\gamma'(t)\,dt = \int_0^1 z f'(tz)\,dt\).
Therefore
\[
|f(z)| = \left|\int_0^1 z f'(tz)\,dt\right| \le \int_0^1 |z|\,|f'(tz)|\,dt \le |z| \int_0^1 1·t\,dt = \frac{|z|^2}{2},
\]
where the second inequality uses the hypothesis \(|f'(w)|≤1\) for \(|w|<1\). Hence \(|f(z)|≤|z|^2/2\) for every \(|z|<1\).

*What connects.* This is a baby version of Schwarz–Pick: derivative bounds on the disk force quadratic vanishing at the origin. The “integrate along the radial segment” trick also shows up when proving the mean value inequality for harmonic functions and when deriving higher-order versions of Schwarz’ lemma (vanishing of order \(k\) gives a \(|z|^k/k!\) bound). Keep it in your prelim toolkit whenever you are given uniform derivative bounds and need a comparison for \(f\) itself.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Radial integral lemma.* Need the identity \(f(z)=\int_0^1 z f'(tz) dt\) for analytic \(f\) with \(f(0)=0\). *Lean target:* `analytic_radial_integral`.
- *Bounding the integral.* Uses triangle inequality plus \(|f'(tz)|≤1\). *Lean target:* `schwarz_like_bound`.
- *Elementary calculus fact.* Evaluate \(∫_0^1 t dt = 1/2\). Already in Mathlib; no new lemma.

**Stage 3 — LEAN FORMALIZATION**

Plan: in `Main.lean`, prove `radial_integral`: for `f` analytic on the ball, `f z = z * ∫_{0}^{1} (deriv f (t•z)) * ? dt` (encode as a real integral over `[0,1]`). Use Mathlib’s `intervalIntegral.map_sub_left` machinery to rewrite the complex integral and the lemma `hasDerivAt.mul_const`. With that identity, short-circuit to the inequality using `norm_integral_le_integral_norm`. Remaining Lean tasks are implementing the radial integral lemma and applying norm inequalities; no sorrys inserted yet. Stage 3 is thus “in progress.”

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the Lean proof is finished, mirror the exact radial integral lemma used (including any `Real` coercions) and note that the bound hinges only on the derivative estimate and the elementary integral; this keeps the exposition aligned with the formal certificate.
