# Proof Outline — a97A02

_Formalization plan from claude-1, 2026-05-01._

## Theorem Statement (Lean 4)

```lean
import Mathlib

open MeasureTheory Set Filter Topology Real

noncomputable section

/-- The local average of f at scale h. -/
def localAverage (f : ℝ → ℂ) (h : ℝ) (t : ℝ) : ℂ :=
  (1 / (2 * h)) • ∫ x in (t - h)..(t + h), f x

/-- L^p bound: |f_h(t)| ≤ (2h)^{-1/p} * ‖f‖_p, via Hölder's inequality. -/
theorem apm_a97A02_pointwise_bound
    (p : ℝ) (hp : 1 ≤ p)
    (f : ℝ → ℂ)
    (hf_supp : ∀ x, x ∉ Set.Icc (0:ℝ) 1 → f x = 0)
    (hf_mem : MemLp f (ENNReal.ofReal p) volume)
    (h : ℝ) (hh : 0 < h)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ‖localAverage f h t‖ ≤
      (2 * h) ^ (-(1 / p)) * (eLpNorm f (ENNReal.ofReal p) volume).toReal := by sorry

/-- Continuity in t of the averaging operator. -/
theorem apm_a97A02_continuous
    (p : ℝ) (hp : 1 ≤ p)
    (f : ℝ → ℂ)
    (hf_supp : ∀ x, x ∉ Set.Icc (0:ℝ) 1 → f x = 0)
    (hf_mem : MemLp f (ENNReal.ofReal p) volume)
    (h : ℝ) (hh : 0 < h) :
    ContinuousOn (localAverage f h) (Set.Icc 0 1) := by sorry

/-- Helper: the L^q norm of 1_{[t-h,t+h]} where q is conjugate to p. -/
theorem apm_a97A02_indicator_Lq_norm
    (p q : ℝ) (hp : 1 < p) (hpq : 1 / p + 1 / q = 1)
    (t h : ℝ) (hh : 0 < h) :
    (eLpNorm (Set.indicator (Set.Icc (t - h) (t + h)) (fun _ : ℝ => (1:ℂ)))
      (ENNReal.ofReal q) volume).toReal = (2 * h) ^ (1 / q) := by sorry

/-- Helper: the symmetric difference of two intervals shifted by Δt
    has measure ≤ 2|Δt|. -/
theorem apm_a97A02_symm_diff_measure
    (t₁ t₂ h : ℝ) (hh : 0 < h) :
    volume (symmDiff (Set.Icc (t₁ - h) (t₁ + h)) (Set.Icc (t₂ - h) (t₂ + h))) ≤
      ENNReal.ofReal (2 * |t₁ - t₂|) := by sorry

/-- Main theorem: f_h is continuous and pointwise bounded. -/
theorem apm_a97A02_main
    (p : ℝ) (hp : 1 ≤ p)
    (f : ℝ → ℂ)
    (hf_supp : ∀ x, x ∉ Set.Icc (0:ℝ) 1 → f x = 0)
    (hf_mem : MemLp f (ENNReal.ofReal p) volume)
    (h : ℝ) (hh : 0 < h) :
    ContinuousOn (localAverage f h) (Set.Icc 0 1) ∧
    ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖localAverage f h t‖ ≤
        (2 * h) ^ (-(1 / p)) * (eLpNorm f (ENNReal.ofReal p) volume).toReal := by sorry
```

## Mathlib Cross-References

Mathlib cross-references

**Types/structures:**
- `MeasureTheory.MemLp` / `MeasureTheory.Memℒp` — membership in L^p
- `MeasureTheory.eLpNorm` / `MeasureTheory.snorm` — L^p (semi)norm
- `MeasureTheory.Lp` — L^p as a Banach space
- `MeasureTheory.Integrable`, `IntegrableOn`
- `intervalIntegral` (`∫ x in a..b, f x`) — interval integral
- `Set.indicator` — indicator function
- `volume` — Lebesgue measure
- `ENNReal.ofReal` — coercion ℝ → ℝ≥0∞
- `ContinuousOn` — continuity on a set

**Key lemmas:**
- `MeasureTheory.integral_mul_le_Lp_mul_Lq` / `MeasureTheory.inner_le_Lp_mul_Lq` — Hölder's inequality
- `MeasureTheory.eLpNorm_indicator_const` — L^p norm of constant times indicator
- `MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict` — indicator vs restriction
- `MeasureTheory.integrableOn_iff_integrable_of_support` — support and integrability
- `intervalIntegral.continuous_of_dominated_interval` — continuity in interval bounds
- `intervalIntegral.continuous_primitive` — primitive is continuous for integrable f
- `MeasureTheory.integral_indicator` — ∫ 1_A · f = ∫_A f
- `Real.rpow_neg` — x^{-a} = 1/x^a
- `Real.rpow_natCast` / `Real.rpow_one_div` — rational exponent identities
- `ENNReal.toReal_rpow` — toReal of rpow
- `MeasureTheory.ae_of_all` — a.e. from everywhere
- `MeasureTheory.norm_setIntegral_le_of_norm_le_const` — ML estimate for set integrals
- `intervalIntegral.norm_integral_le_integral_norm` — |∫| ≤ ∫|·|
- `MeasureTheory.tendsto_setIntegral_of_dominated_convergence` — DCT for set integrals
- `Real.conjugateExponent` / `Real.IsConjugateExponent` — Hölder conjugate
- `MeasureTheory.eLpNorm_lt_top_iff_memLp` — finite L^p norm characterization
- `Real.volume_Icc` — Lebesgue measure of [a,b] is b - a

**Tactic hints:**
- `field_simp` — clear 1/(2h) and 1/p denominators
- `ring` / `ring_nf` — algebraic manipulation of (2h)^{1/q - 1} factors
- `nlinarith` — close p ≥ 1, h > 0 inequalities
- `positivity` — for 0 < 2h, 0 < (2h)^{1/q}, etc.
- `gcongr` — monotone manipulation of L^p norm bounds
- `simp [localAverage]` — unfold definition
- `rcases eq_or_lt_of_le hp with hp1 | hp1` — split p = 1 vs p > 1 cases
- `apply ContinuousOn.intro` / `refine ⟨?_, ?_⟩ts` — assemble the conjunction
- `filter_upwards` — for a.e. arguments
- `exact?` — search for the Hölder bound lemma in the right form
- `convert ... using 1` — match expressions up to small rewrites
- `have hq : 1 / p + 1 / q = 1 := by ...` — set up Hölder conjugate

## Current Blockers

- 4 `sorry` remain in `lean/Main.lean`.
- Closed already:
  - `apm_a97A02_main`
- Remaining:
  - `apm_a97A02_pointwise_bound`
  - `apm_a97A02_continuous`
  - `apm_a97A02_indicator_Lq_norm`
  - `apm_a97A02_symm_diff_measure`
