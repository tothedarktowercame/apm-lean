<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a99J10: |y|^{-1/2} growth lands f in a Hardy space, where vanishing radial limits force f ≡ 0

## Why It's Hard

Two obstacles block the obvious moves:

1. **f is not bounded.** The estimate |f(x+iy)| ≤ |y|^{-1/2} lets f blow up as z approaches the real diameter (−1,1). So the maximum-modulus principle and the boundary-uniqueness theorems for *bounded* holomorphic functions do not apply directly.
2. **The boundary hypothesis is weak.** "Radial limit 0 for every θ" is a *pointwise-along-radii* statement — much weaker than continuous boundary values or a uniform bound on a boundary arc — so one cannot simply read off that f is small near the circle.

The resolution turns on the precise exponent ½. Growth like |Im z|^{-1/2} is **mild enough to be L^p-integrable on circles** for p < 2: near the two points ±1 where the real diameter meets the circle, |f|^p behaves like |sin θ|^{-p/2}, which is integrable in θ exactly when p < 2. This is just enough to place f in a **Hardy space**, the natural home of "almost bounded" holomorphic functions, where a strong boundary-uniqueness theorem is available. The hypotheses are then perfectly matched: the growth bound gives membership, and the vanishing radial limits trigger uniqueness.

## The Key Insight

Two steps.

- **Membership.** On the circle |z| = r, |f(re^{iθ})| ≤ |r sin θ|^{-1/2}, so

  $$\int_0^{2\pi} |f(re^{i\theta})|\,d\theta \;\leq\; r^{-1/2}\int_0^{2\pi} |\sin\theta|^{-1/2}\,d\theta \;<\; \infty,$$

  uniformly for r bounded away from 0 (and trivially bounded for small r, where f is bounded on a compact disk). Hence the integral means stay bounded: **f ∈ H¹(Δ)**.

- **Uniqueness.** A Hardy-space function has nontangential boundary values a.e., and — the key theorem — a function in H^p that is **not** identically 0 has boundary values vanishing only on a set of **measure zero** (because log|f*| is integrable on the circle). Here the radial limits are 0 for *every* θ, i.e. f* = 0 a.e. — a set of full measure. So f ≡ 0.

## Complete Proof

Assume f ≢ 0 and seek a contradiction (or directly produce f ≡ 0 at the end).

**Step 1: f ∈ H¹(Δ).** Recall f ∈ H¹ means sup_{0<r<1} (1/2π)∫_0^{2π} |f(re^{iθ})|\,dθ < ∞. Bound the integral means in two regimes.

- *Small radii (0 < r ≤ 1/2).* The closed disk {|z| ≤ 1/2} is a compact subset of Δ, and f is continuous there, so |f| ≤ C₀ on it for some finite C₀. Then ∫_0^{2π} |f(re^{iθ})|\,dθ ≤ 2π C₀ for all r ≤ 1/2.

- *Large radii (1/2 ≤ r < 1).* For z = re^{iθ}, Im z = r sin θ, so by hypothesis

  $$|f(re^{i\theta})| \leq |r\sin\theta|^{-1/2} = r^{-1/2}\,|\sin\theta|^{-1/2}.$$

  Now |sin θ|^{-1/2} is integrable over [0, 2π]: its only singularities are at θ = 0, π, 2π, where |sin θ|^{-1/2} ∼ |θ − θ₀|^{-1/2}, and ∫ |t|^{-1/2}\,dt converges (exponent ½ < 1). Set C₁ := ∫_0^{2π} |\sin θ|^{-1/2}\,dθ < ∞. Then for 1/2 ≤ r < 1,

  $$\int_0^{2\pi} |f(re^{i\theta})|\,d\theta \;\leq\; r^{-1/2} C_1 \;\leq\; \sqrt{2}\,C_1.$$

Combining, sup_{0<r<1} ∫_0^{2π} |f(re^{iθ})|\,dθ ≤ max(2πC₀, √2 C₁) < ∞. Hence **f ∈ H¹(Δ)**.

(Indeed the same computation with exponent p, using ∫|sin θ|^{-p/2}dθ < ∞ ⟺ p < 2, shows f ∈ H^p for every p ∈ [1, 2) — the ½ in the hypothesis is exactly what keeps p below the threshold 2.)

**Step 2: the boundary function vanishes a.e.** By Fatou's theorem for Hardy spaces, an H¹ function has a nontangential (in particular radial) limit f*(e^{iθ}) for almost every θ, and f* ∈ L¹(∂Δ). By hypothesis the radial limit lim_{r→1⁻} f(re^{iθ}) exists and equals 0 for *every* θ; in particular it equals 0 for a.e. θ. Since the radial limit coincides with f* wherever the latter exists, we get

$$f^*(e^{i\theta}) = 0 \quad \text{for a.e. } \theta \in [0, 2\pi].$$

**Step 3: Hardy-space uniqueness.** The boundary-uniqueness theorem for Hardy spaces states: if f ∈ H^p (p > 0) and f ≢ 0, then log|f*| ∈ L¹(∂Δ); in particular f* ≠ 0 almost everywhere, so the zero set {f* = 0} has measure zero. Contrapositively, if f* = 0 on a set of positive measure, then f ≡ 0.

Here f* = 0 on a set of full measure (Step 2), which certainly has positive measure. Therefore

$$f \equiv 0 \quad \text{on } \Delta. \qquad \blacksquare$$

## What Connects

**Within analysis**: This is a **growth-into-Hardy-space** argument followed by **boundary uniqueness**. The dividing line is the exponent: a singularity |Im z|^{-α} on the real diameter is L^p on circles iff pα < 1, so α < 1 guarantees membership in some H^p with p ≥ 1 — and α = ½ comfortably qualifies (p up to 2). Once inside a Hardy space, the rigidity of H^p (the boundary function's log is integrable, so it cannot vanish on positive measure) converts a *pointwise* vanishing hypothesis into a *global* identity. This rigidity is the F. and M. Riesz / Privalov circle of uniqueness theorems.

**The reusable principle**: don't try to bound an unbounded holomorphic function — instead *measure* its growth in an L^p-mean sense to place it in the right Hardy (or Nevanlinna) class, where boundary-value theorems do the work. The same strategy proves uniqueness for functions with controlled growth in half-planes and strips (paired with Phragmén–Lindelöf when the growth is borderline).
