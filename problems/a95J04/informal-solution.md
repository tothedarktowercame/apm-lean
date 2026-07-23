

# APM a95J04: Meromorphic extension past the circle of convergence — poles on boundary, bounded coefficients

## 1. Informal proof

**Why it's hard.** Part (a) seems obvious (the radius of convergence is 1, so something must go wrong on ∂Δ), but needs careful argument: if f extends meromorphically to D ⊃ Δ̄ with no poles on ∂Δ, then f would be analytic on an open set containing Δ̄, giving radius of convergence > 1. Part (b) requires extracting coefficient bounds from the order of the poles — connecting local singularity structure to global coefficient asymptotics.

**The key insight.** (a) If there were no poles on ∂Δ, f would be holomorphic on D (which contains Δ̄), so the power series would converge on a disk of radius > 1, contradicting R = 1. (b) Subtract the principal parts at the simple poles on ∂Δ: the remainder is holomorphic on a disk of radius > 1, so its coefficients decay geometrically. Each principal part c/(z - ζ) with |ζ| = 1 contributes Taylor coefficients -c/ζ^{n+1}, which are bounded. Sum of bounded + decaying = bounded.

**Proof.**

**(a) f has at least one pole on ∂Δ.**

Suppose f has no poles on ∂Δ. Since f is meromorphic on D ⊃ Δ̄, the set of poles in D is discrete. Poles in Δ̄ form a finite set (compact + discrete = finite). If none are on ∂Δ, all poles of f in Δ̄ are in the interior Δ. But wait — f is analytic on Δ (given), so f has no poles in Δ either. So f has no poles in Δ̄ at all, meaning f is holomorphic on D ⊃ Δ̄. Since D is open and contains Δ̄, there exists r > 1 with D(0,r) ⊆ D. Then f is analytic on D(0,r), so the radius of convergence ≥ r > 1, contradicting R = 1. ✓

**(b) Simple poles on ∂Δ imply a(n) is bounded.**

Let ζ₁, ..., ζₘ be the poles of f on ∂Δ, each of order 1 with residues c₁, ..., cₘ. Define the principal part:

P(z) = Σⱼ cⱼ/(z - ζⱼ).

Then g(z) = f(z) - P(z) is meromorphic on D with no poles on ∂Δ (the poles at ζⱼ are cancelled). By part (a)'s logic in reverse: since g has no poles on ∂Δ and any remaining poles are in D \ Δ̄ (far from the boundary), g is holomorphic on some disk D(0, R') with R' > 1.

*Coefficients of g:* g(z) = Σ b(n)z^n with R' > 1. By the Cauchy estimates: |b(n)| ≤ M/R'^n → 0 exponentially.

*Coefficients of P:* For each term cⱼ/(z - ζⱼ) with |ζⱼ| = 1:

cⱼ/(z - ζⱼ) = -cⱼ/ζⱼ · 1/(1 - z/ζⱼ) = -Σₙ (cⱼ/ζⱼ^{n+1}) z^n for |z| < 1.

The n-th coefficient is -cⱼ/ζⱼ^{n+1}, which satisfies |-cⱼ/ζⱼ^{n+1}| = |cⱼ| (since |ζⱼ| = 1). So bounded.

*Total:* a(n) = b(n) + Σⱼ (-cⱼ/ζⱼ^{n+1}). Each term is bounded:
- |b(n)| ≤ M/R'^n → 0 (bounded by M).
- |Σ cⱼ/ζⱼ^{n+1}| ≤ Σ|cⱼ| (constant).

So |a(n)| ≤ M + Σ|cⱼ| for all n. The sequence a(n) is bounded. ✓ ∎

**What connects.** This is a fundamental result in analytic combinatorics and singularity analysis: the asymptotic behaviour of Taylor coefficients is governed by the singularities nearest to the origin. Part (a) says the "obstruction" to a larger radius of convergence must manifest as a pole on ∂Δ (if the extension is meromorphic). Part (b) says simple poles give bounded coefficients (in fact, a(n) converges to -Σ cⱼ/ζⱼ^{n+1}, which oscillates but stays bounded). Poles of higher order k would give |a(n)| = O(n^{k-1}) — polynomial growth in n. This connects to the transfer theorems of Flajolet-Odlyzko in analytic combinatorics, where singularity type determines coefficient asymptotics.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Metric Set

noncomputable section

/-- (a) f must have at least one pole on ∂Δ. -/
theorem exists_pole_on_boundary
    {D : Set ℂ} (hD : IsOpen D) (hD_contains : closedBall (0 : ℂ) 1 ⊆ D)
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_mero : ∀ z ∈ D, z ∉ sphere (0 : ℂ) 1 →
      DifferentiableAt ℂ f z ∨ ∃ n : ℕ, 0 < n ∧ DifferentiableAt ℂ (fun w => (w - z) ^ n * f w) z)
    (hR : FormalMultilinearSeries.radius
      (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
        (iteratedDeriv n f 0 / ↑(n !))) = 1) :
    ∃ ζ ∈ sphere (0 : ℂ) 1, ¬DifferentiableAt ℂ f ζ := by
  sorry

/-- (b) Simple poles on ∂Δ imply bounded coefficients. -/
theorem coefficients_bounded_of_simple_poles
    {D : Set ℂ} (hD : IsOpen D) (hD_contains : closedBall (0 : ℂ) 1 ⊆ D)
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_simple : ∀ ζ ∈ sphere (0 : ℂ) 1, ¬DifferentiableAt ℂ f ζ →
      DifferentiableAt ℂ (fun w => (w - ζ) * f w) ζ) :
    ∃ M : ℝ, ∀ n : ℕ, ‖iteratedDeriv n f 0 / ↑(n !)‖ ≤ M := by
  sorry

/-- If f is holomorphic on D ⊃ Δ̄, radius of convergence > 1. -/
lemma radius_gt_one_of_holo_on_nbhd
    {D : Set ℂ} (hD : IsOpen D) (hD_contains : closedBall (0 : ℂ) 1 ⊆ D)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) :
    1 < FormalMultilinearSeries.radius
      (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
        (iteratedDeriv n f 0 / ↑(n !))) := by
  sorry

/-- Taylor coefficients of 1/(z - ζ) with |ζ| = 1 are bounded. -/
lemma coefficients_bounded_simple_pole
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {c : ℂ} :
    ∃ M, ∀ n : ℕ, ‖-c / ζ ^ (n + 1)‖ ≤ M := by
  sorry

/-- Cauchy bound: coefficients of f holomorphic on D(0, R') with R' > 1
    decay geometrically. -/
lemma coefficients_decay_of_larger_radius
    {g : ℂ → ℂ} {R' : ℝ} (hR' : 1 < R')
    (hg : DifferentiableOn ℂ g (ball 0 R')) :
    ∃ M : ℝ, ∀ n : ℕ, ‖iteratedDeriv n g 0 / ↑(n !)‖ ≤ M / R' ^ n := by
  sorry

/-- The poles on the compact set ∂Δ form a finite set. -/
lemma poles_on_circle_finite
    {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℂ} (hf_mero : ∀ z ∈ D, DifferentiableAt ℂ f z ∨
      ∃ n, 0 < n ∧ DifferentiableAt ℂ (fun w => (w-z)^n * f w) z) :
    Set.Finite {ζ ∈ sphere (0 : ℂ) 1 | ¬DifferentiableAt ℂ f ζ} := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `FormalMultilinearSeries.radius` — radius of convergence
- `DifferentiableOn ℂ f S` / `DifferentiableAt ℂ f z` — analyticity
- `iteratedDeriv n f z` — n-th derivative (for Taylor coefficients a(n) = f⁽ⁿ⁾(0)/n!)
- `Metric.sphere (0 : ℂ) 1` — unit circle ∂Δ
- `Metric.closedBall (0 : ℂ) 1` — closed unit disk

**Key lemmas:**
- `FormalMultilinearSeries.le_radius_of_bound` — if |aₙ| ≤ M/Rⁿ then radius ≥ R (for part (a) contrapositive)
- `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` — Cauchy estimates: |f⁽ⁿ⁾(0)/n!| ≤ max|f|/Rⁿ (for the remainder g)
- `isCompact_sphere` — ∂Δ is compact (for finiteness of poles)
- `IsCompact.finite` — finite discrete subset of compact set
- `norm_pow` — ‖ζ^n‖ = ‖ζ‖^n = 1 when |ζ| = 1 (for bounding pole coefficients)
- `norm_div` — ‖c/ζ^{n+1}‖ = |c|/|ζ|^{n+1} = |c|
- `geom_series_def` — 1/(1-z/ζ) = Σ (z/ζ)^n (for Taylor expansion of principal part)
- `DifferentiableOn.sub` — f - P is differentiable

**Tactic hints:**
- `by_contra h; push_neg at h` — for part (a) contrapositive
- `have := radius_gt_one_of_holo_on_nbhd hD hD_contains (by exact ...)` — contradiction with R=1
- `refine ⟨M_g + ∑ j, ‖c j‖, fun n => ?_⟩` — providing the bound in part (b)
- `calc ‖a(n)‖ = ‖b(n) + Σ ...‖ ≤ ‖b(n)‖ + Σ ‖...‖ ≤ ...` — triangle inequality chain
- `simp [norm_pow, hζ]` — simplifying |ζ^n| = 1
- `gcongr` — monotonicity steps
- `linarith` — combining bounds
- `exact?` — finding Cauchy estimate or radius lemma