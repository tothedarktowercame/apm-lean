

# APM a94A08: Iterates of a strict Schwarz contraction converge to 0

## 1. Informal proof

**Why it's hard.** The Schwarz lemma gives |f(z)| ≤ |z| globally, but this alone only shows |fₙ(z)| ≤ |z| — no decay. The strict inequality |f'(0)| < 1 (not just ≤ 1) is what provides contraction, but the contraction ratio depends on how close to the boundary you are: on the full disk, the best ratio is 1 (no contraction). The challenge is proving contraction on compact subsets.

**The key insight.** On the closed disk |z| ≤ r < 1, the Schwarz lemma applied to g(z) = f(z)/z gives |g(z)| ≤ 1 on the unit disk with |g(0)| = |f'(0)| < 1. By the maximum principle on |z| ≤ r: |g(z)| ≤ λ(r) < 1 (a continuous function on a compact set that is strictly less than 1 everywhere achieves a maximum strictly less than 1). So |f(z)| ≤ λ|z| on |z| ≤ r. Iterating: |fₙ(z)| ≤ λⁿ|z| → 0.

**Proof.**

*Step 1: The strict contraction on compact subdisks.* Define g(z) = f(z)/z for z ≠ 0 and g(0) = f'(0). By the Schwarz lemma (since f(0) = 0 and f(Δ) ⊂ Δ), g is analytic on Δ with |g(z)| ≤ 1 for all z ∈ Δ.

Moreover, |g| < 1 strictly on Δ: if |g(z₀)| = 1 for some z₀ ∈ Δ, the maximum modulus principle forces g constant of modulus 1, so f(z) = e^{iθ}z, giving |f'(0)| = 1 — contradicting |f'(0)| < 1.

Fix r ∈ (0,1). On the compact set {|z| ≤ r}, the continuous function |g| achieves its maximum: λ(r) = max_{|z|≤r} |g(z)|. Since |g| < 1 strictly on Δ and {|z| ≤ r} ⊂ Δ, we have λ(r) < 1.

Therefore: |f(z)| = |z| · |g(z)| ≤ λ(r) · |z| for all |z| ≤ r.

*Step 2: Iterate.* For |z| ≤ r: |f(z)| ≤ λr < r (since λ < 1), so f maps {|z| ≤ r} into itself. By induction:

|fₙ(z)| ≤ λⁿ · |z| ≤ λⁿ · r.

Since λ < 1, λⁿ → 0, so |fₙ(z)| → 0 uniformly on {|z| ≤ r}.

*Step 3: Extend to compact subsets.* Any compact K ⊂ Δ is contained in {|z| ≤ r} for some r < 1. By Step 2, fₙ → 0 uniformly on K. ∎

**What connects.** This is the Denjoy-Wolff theorem for the special case of a fixed point at the origin with |f'(0)| < 1: the iterates of any analytic self-map of the disk with an interior fixed point whose derivative has modulus < 1 converge uniformly on compacts to that fixed point. The general Denjoy-Wolff theorem handles the case where f has no interior fixed point (the iterates converge to a boundary point). The result is the complex-analytic analogue of the Banach contraction principle, with the Schwarz lemma providing the contraction estimate. The key subtlety is that the contraction constant λ depends on r (approaching 1 as r → 1), so the convergence is uniform on compacts but not on the whole disk.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

open Complex Metric Set Filter Topology

noncomputable section

/-- The Schwarz function g(z) = f(z)/z, with g(0) = f'(0). -/
def schwarzQuotient (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then deriv f 0 else f z / z

/-- g = f/z is analytic on the disk. -/
lemma schwarzQuotient_differentiableOn
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf0 : f 0 = 0) :
    DifferentiableOn ℂ (schwarzQuotient f) (ball 0 1) := by
  sorry

/-- |g(z)| < 1 strictly on the disk when |f'(0)| < 1. -/
lemma schwarzQuotient_norm_lt_one
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf_maps : MapsTo f (ball 0 1) (ball 0 1))
    (hf0 : f 0 = 0)
    (hf'0 : ‖deriv f 0‖ < 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖schwarzQuotient f z‖ < 1 := by
  sorry

/-- On {|z| ≤ r}, the contraction ratio λ(r) = max |g| < 1. -/
lemma contraction_on_subdisk
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf_maps : MapsTo f (ball 0 1) (ball 0 1))
    (hf0 : f 0 = 0)
    (hf'0 : ‖deriv f 0‖ < 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ λ : ℝ, 0 ≤ λ ∧ λ < 1 ∧
      ∀ z ∈ closedBall (0 : ℂ) r, ‖f z‖ ≤ λ * ‖z‖ := by
  sorry

/-- f maps {|z| ≤ r} into itself when λr < r. -/
lemma maps_closedBall_to_self
    {f : ℂ → ℂ} {r λ : ℝ}
    (hλ : λ < 1) (hr : 0 < r)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) r, ‖f z‖ ≤ λ * ‖z‖) :
    MapsTo f (closedBall 0 r) (closedBall 0 r) := by
  sorry

/-- The n-th iterate satisfies |fₙ(z)| ≤ λⁿ|z|. -/
lemma iterate_bound
    {f : ℂ → ℂ} {r λ : ℝ}
    (hλ0 : 0 ≤ λ) (hλ1 : λ < 1) (hr : 0 < r)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) r, ‖f z‖ ≤ λ * ‖z‖)
    (n : ℕ) :
    ∀ z ∈ closedBall (0 : ℂ) r, ‖f^[n] z‖ ≤ λ ^ n * ‖z‖ := by
  sorry

/-- Main theorem: fₙ → 0 uniformly on compact subsets. -/
theorem iterates_tendsto_zero_uniformly_on_compacts
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf_maps : MapsTo f (ball 0 1) (ball 0 1))
    (hf0 : f 0 = 0)
    (hf'0 : ‖deriv f 0‖ < 1)
    {K : Set ℂ} (hK : IsCompact K) (hKΔ : K ⊆ ball 0 1) :
    TendstoUniformlyOn (fun n => f^[n]) 0 atTop K := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `DifferentiableOn ℂ f (ball 0 1)` — analyticity on the disk
- `MapsTo f (ball 0 1) (ball 0 1)` — self-map of the disk
- `Function.iterate f n` / `f^[n]` — n-th iterate
- `TendstoUniformlyOn` — uniform convergence on a set
- `Metric.closedBall`, `Metric.ball` — disks
- `IsCompact` — compactness

**Key lemmas:**
- `Complex.norm_le_norm_of_mapsTo_ball_self` — Schwarz lemma: |f(z)| ≤ |z|. In `Mathlib.Analysis.Complex.Schwarz`
- `Complex.schwarz_eq` / equality case — |f(z)/z| = 1 somewhere ⟹ f(z) = cz with |c| = 1
- `IsCompact.exists_isMaxOn` — continuous function on compact set attains max (for λ(r) < 1)
- `IsCompact.subset_ball` — compact K ⊂ ball 0 1 ⟹ K ⊆ closedBall 0 r for some r < 1
- `geom_lt_one` / `tendsto_pow_atTop_nhds_zero_of_lt_one` — λⁿ → 0 for 0 ≤ λ < 1
- `tendstoUniformlyOn_iff` — ε-δ characterisation of uniform convergence
- `Function.iterate_succ'` — f^[n+1] = f ∘ f^[n]
- `norm_nonneg` — ||z|| ≥ 0

**Tactic hints:**
- `induction n with | zero => ... | succ n ih => ...` — induction for the iterate bound
- `calc ‖f^[n+1] z‖ = ‖f (f^[n] z)‖ ≤ λ * ‖f^[n] z‖ ≤ λ * (λ^n * ‖z‖) = λ^(n+1) * ‖z‖` — iterate chain
- `obtain ⟨r, hr0, hr1, hKr⟩ := hK.subset_ball ...` — embedding K in a closed subdisk
- `exact tendsto_pow_atTop_nhds_zero_of_lt_one hλ0 hλ1` — geometric decay
- `gcongr` — for λ * ‖f^[n] z‖ ≤ λ * (λⁿ ‖z‖)
- `positivity` — for r > 0, λ ≥ 0
- `nlinarith` — combining λ < 1, r < 1, λr < r
- `exact?` — finding the Schwarz lemma and maximum principle