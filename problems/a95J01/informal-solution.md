

# APM a95J01: Subordination principle — |f'(0)| ≤ |g'(0)| with equality iff f = g ∘ rotation

## 1. Informal proof

**Why it's hard.** The inclusion f(Δ) ⊆ g(Δ) relates the *images* of two univalent functions, but we need a *derivative* comparison at a single point. The functions map into different subdomains of ℂ, so there's no direct pointwise comparison — we need to compose with an inverse.

**The key insight.** Since g is univalent, g⁻¹ exists on g(Δ). The composition h = g⁻¹ ∘ f maps Δ → Δ (since f(Δ) ⊆ g(Δ)), h(0) = g⁻¹(f(0)) = g⁻¹(g(0)) = 0, and h is analytic. By the Schwarz lemma: |h'(0)| ≤ 1, with equality iff h is a rotation. Since f = g ∘ h, f'(0) = g'(0) · h'(0), giving |f'(0)| ≤ |g'(0)|.

**Proof.**

**(a) |f'(0)| ≤ |g'(0)|.**

Since g is one-to-one and analytic on Δ, g has an analytic inverse g⁻¹ : g(Δ) → Δ.

Define h = g⁻¹ ∘ f : Δ → Δ. Then:
- h is analytic on Δ (composition of analytic functions).
- h(Δ) ⊆ Δ (since f(Δ) ⊆ g(Δ) and g⁻¹ maps g(Δ) to Δ).
- h(0) = g⁻¹(f(0)) = g⁻¹(g(0)) = 0.

By the Schwarz lemma: |h'(0)| ≤ 1.

Since f = g ∘ h, the chain rule gives f'(0) = g'(h(0)) · h'(0) = g'(0) · h'(0).

Taking moduli: **|f'(0)| = |g'(0)| · |h'(0)| ≤ |g'(0)|**. ✓

**(b) Equality case.** If |f'(0)| = |g'(0)|, then |h'(0)| = 1. By the equality case of the Schwarz lemma, h(z) = e^{iα}z for some real α. Therefore:

f(z) = g(h(z)) = g(e^{iα}z).

So **f is obtained from g by precomposing with a rotation of the disk**. Equivalently, f and g are related by f(z) = g(e^{iα}z). ✓ ∎

**What connects.** This is the *subordination principle* (Lindelöf's theorem): if f is subordinate to g (meaning f = g ∘ h for a Schwarz function h), then |f'(0)| ≤ |g'(0)| with equality iff the subordination function is a rotation. The result is fundamental in geometric function theory: it gives the Schwarz-Pick lemma as a special case (g = id), and it underpins the de Branges (Bieberbach) theorem. The key reduction is that comparing two univalent functions reduces to applying the Schwarz lemma to their "ratio" h = g⁻¹ ∘ f. This is also the basis for the Koebe distortion theorem and the study of conformal invariants.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.Schwarz

open Complex Metric Set

noncomputable section

/-- (a) |f'(0)| ≤ |g'(0)| when f(Δ) ⊆ g(Δ) and f(0) = g(0). -/
theorem subordination_deriv_le
    {f g : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hg_holo : DifferentiableOn ℂ g (ball 0 1))
    (hf_inj : InjOn f (ball 0 1))
    (hg_inj : InjOn g (ball 0 1))
    (hfg_zero : f 0 = g 0)
    (hfg_sub : f '' ball 0 1 ⊆ g '' ball 0 1) :
    ‖deriv f 0‖ ≤ ‖deriv g 0‖ := by
  sorry

/-- (b) Equality iff f(z) = g(e^{iα}z) for some α. -/
theorem subordination_deriv_eq
    {f g : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hg_holo : DifferentiableOn ℂ g (ball 0 1))
    (hf_inj : InjOn f (ball 0 1))
    (hg_inj : InjOn g (ball 0 1))
    (hfg_zero : f 0 = g 0)
    (hfg_sub : f '' ball 0 1 ⊆ g '' ball 0 1)
    (heq : ‖deriv f 0‖ = ‖deriv g 0‖)
    (hg_ne : deriv g 0 ≠ 0) :
    ∃ α : ℝ, ∀ z ∈ ball (0 : ℂ) 1,
      f z = g (exp (I * ↑α) * z) := by
  sorry

/-- The subordination function h = g⁻¹ ∘ f maps Δ → Δ with h(0) = 0. -/
lemma subordination_function_exists
    {f g : ℂ → ℂ}
    (hg_holo : DifferentiableOn ℂ g (ball 0 1))
    (hg_inj : InjOn g (ball 0 1))
    (hfg_zero : f 0 = g 0)
    (hfg_sub : f '' ball 0 1 ⊆ g '' ball 0 1) :
    ∃ h : ℂ → ℂ,
      DifferentiableOn ℂ h (ball 0 1) ∧
      MapsTo h (ball 0 1) (ball 0 1) ∧
      h 0 = 0 ∧
      ∀ z ∈ ball (0 : ℂ) 1, f z = g (h z) := by
  sorry

/-- The Schwarz lemma: h : Δ → Δ with h(0) = 0 satisfies |h'(0)| ≤ 1. -/
lemma schwarz_deriv_bound
    {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 1))
    (hh_maps : MapsTo h (ball 0 1) (ball 0 1))
    (hh_zero : h 0 = 0) :
    ‖deriv h 0‖ ≤ 1 := by
  sorry

/-- Schwarz equality: |h'(0)| = 1 ⟹ h(z) = e^{iα}z. -/
lemma schwarz_equality
    {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 1))
    (hh_maps : MapsTo h (ball 0 1) (ball 0 1))
    (hh_zero : h 0 = 0)
    (heq : ‖deriv h 0‖ = 1) :
    ∃ α : ℝ, ∀ z ∈ ball (0 : ℂ) 1, h z = exp (I * ↑α) * z := by
  sorry

/-- Chain rule: f = g ∘ h ⟹ f'(0) = g'(0) · h'(0). -/
lemma chain_rule_at_zero
    {f g h : ℂ → ℂ}
    (hg : DifferentiableAt ℂ g (h 0))
    (hh : DifferentiableAt ℂ h 0)
    (hfgh : ∀ z ∈ ball (0 : ℂ) 1, f z = g (h z)) :
    deriv f 0 = deriv g (h 0) * deriv h 0 := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `DifferentiableOn ℂ f (ball 0 1)` — analyticity on the disk
- `InjOn f (ball 0 1)` — univalence (injectivity)
- `MapsTo h (ball 0 1) (ball 0 1)` — self-map of the disk
- `Complex.exp`, `Complex.I` — for rotations e^{iα}

**Key lemmas:**
- `Complex.norm_deriv_le_one_of_mapsTo_ball_self` / `Complex.norm_le_norm_of_mapsTo_ball_self` — Schwarz lemma. In `Mathlib.Analysis.Complex.Schwarz`
- `Complex.eq_smul_of_mapsTo_ball_self` — Schwarz equality case: |h'(0)| = 1 ⟹ h is a rotation. In `Mathlib.Analysis.Complex.Schwarz`
- `DifferentiableOn.comp` — chain rule for composition (g ∘ h differentiable)
- `HasDerivAt.comp` — chain rule at a point: (g ∘ h)'(0) = g'(h(0)) · h'(0)
- `InjOn.invFunOn` — inverse of an injective function on a set
- `DifferentiableOn.invFunOn` — or `AnalyticAt.inv` — inverse function is analytic (for g⁻¹)
- `norm_mul` — ‖ab‖ = ‖a‖ · ‖b‖ (for |f'(0)| = |g'(0)| · |h'(0)|)
- `mul_le_mul_of_nonneg_left` — monotonicity for the bound |g'(0)| · |h'(0)| ≤ |g'(0)|

**Tactic hints:**
- `obtain ⟨h, hh_holo, hh_maps, hh_zero, hh_eq⟩ := subordination_function_exists ...` — construct h
- `have h_schwarz := schwarz_deriv_bound hh_holo hh_maps hh_zero` — apply Schwarz
- `have h_chain := chain_rule_at_zero ...` — chain rule
- `calc ‖deriv f 0‖ = ‖deriv g 0 * deriv h 0‖ = ‖deriv g 0‖ * ‖deriv h 0‖ ≤ ‖deriv g 0‖ * 1` — bound chain
- `simp [norm_mul]` — for product of norms
- `exact?` — finding the Schwarz lemma in Mathlib
- `nlinarith [norm_nonneg (deriv h 0)]` — for the ≤ 1 bound
- `linarith` — combining the equality case