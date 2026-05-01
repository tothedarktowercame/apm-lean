# Proof Outline — a97A03

_Formalization plan from claude-1, 2026-05-01._

## Theorem Statement (Lean 4)

```lean
import Mathlib

open MeasureTheory Set Filter

noncomputable section

variable {a b : ℝ} (hab : a ≤ b)

/-- Forward direction: Lipschitz implies a.e. bounded derivative. -/
theorem apm_a97A03_lip_to_bounded_deriv
    (f : ℝ → ℝ)
    (hf_ac : ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ δ > 0, ∀ (s : Finset (ℝ × ℝ)),
      (∀ p ∈ s, p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc a b ∧ p.1 ≤ p.2) →
      (s.sum (fun p => p.2 - p.1) < δ) →
      s.sum (fun p => |f p.2 - f p.1|) < ε)
    (B : ℝ) (hB : 0 < B)
    (hLip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ B * |x - y|) :
    ∃ C > 0, ∀ᵐ x ∂(volume.restrict (Set.Icc a b)),
      DifferentiableAt ℝ f x → |deriv f x| ≤ C := by sorry

/-- Reverse direction: AC + a.e. bounded derivative implies Lipschitz. -/
theorem apm_a97A03_bounded_deriv_to_lip
    (f : ℝ → ℝ)
    (hf_ac : ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ δ > 0, ∀ (s : Finset (ℝ × ℝ)),
      (∀ p ∈ s, p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc a b ∧ p.1 ≤ p.2) →
      (s.sum (fun p => p.2 - p.1) < δ) →
      s.sum (fun p => |f p.2 - f p.1|) < ε)
    (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), |deriv f x| ≤ C) :
    ∃ B > 0, ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ B * |x - y| := by sorry

/-- Key lemma: AC functions satisfy the Fundamental Theorem of Calculus. -/
theorem apm_a97A03_ftc_for_ac
    (f : ℝ → ℝ)
    (hf_ac : ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ δ > 0, ∀ (s : Finset (ℝ × ℝ)),
      (∀ p ∈ s, p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc a b ∧ p.1 ≤ p.2) →
      (s.sum (fun p => p.2 - p.1) < δ) →
      s.sum (fun p => |f p.2 - f p.1|) < ε)
    (x y : ℝ) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (hxy : x ≤ y) :
    f y - f x = ∫ t in x..y, deriv f t := by sorry

/-- Main theorem: equivalence of Lipschitz and a.e. bounded derivative for
    absolutely continuous functions on a compact interval. -/
theorem apm_a97A03_main
    (f : ℝ → ℝ)
    (hf_ac : ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ δ > 0, ∀ (s : Finset (ℝ × ℝ)),
      (∀ p ∈ s, p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc a b ∧ p.1 ≤ p.2) →
      (s.sum (fun p => p.2 - p.1) < δ) →
      s.sum (fun p => |f p.2 - f p.1|) < ε) :
    (∃ B > 0, ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ B * |x - y|) ↔
    (∃ C > 0, ∀ᵐ x ∂(volume.restrict (Set.Icc a b)),
        DifferentiableAt ℝ f x ∧ |deriv f x| ≤ C) := by sorry
```

## Mathlib Cross-References

Mathlib cross-references

**Types/structures:**
- `LipschitzWith` / `LipschitzOnWith` — Lipschitz functions with explicit constant
- `LipschitzWith.const` / `LipschitzOnWith.weaken` — manipulating Lipschitz constants
- `MeasureTheory.AbsolutelyContinuous` — abstract AC of measures
- `BoundedVariationOn` — bounded variation
- `intervalIntegral` — interval integrals
- `deriv` / `derivWithin` — pointwise derivative
- `DifferentiableAt`, `DifferentiableOn` — differentiability
- `MeasureTheory.AEStronglyMeasurable`
- `MeasureTheory.MemLp`, `eLpNorm` — for the L^∞ bound interpretation
- `MeasureTheory.volume.restrict` — restricted Lebesgue measure

**Key lemmas:**
- `LipschitzOnWith.ae_differentiableAt` / `LipschitzWith.ae_differentiable` — Rademacher in 1D: Lipschitz ⇒ a.e. differentiable
- `LipschitzOnWith.norm_deriv_le` — derivative of Lipschitz function bounded by Lipschitz constant
- `MeasureTheory.integral_eq_sub_of_hasDerivAt` / `intervalIntegral.integral_eq_sub_of_hasDerivAt` — FTC
- `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` — FTC with ordering
- `AbsolutelyContinuousOn.integral_eq` / `MeasureTheory.AbsolutelyContinuous.exists_integrable_deriv` — FTC for AC functions
- `intervalIntegral.norm_integral_le_integral_norm` — |∫ f| ≤ ∫ |f|
- `intervalIntegral.integral_const` — ∫_x^y C dt = C(y - x)
- `MeasureTheory.setIntegral_mono_ae` — monotonicity of ∫ given a.e. bound
- `intervalIntegral.integral_mono_ae` — ∫ f ≤ ∫ g if f ≤ g a.e.
- `lipschitzWith_iff_norm_sub_le` — characterization via |f(x) - f(y)| ≤ K|x - y|
- `MeasureTheory.ae_restrict_iff'` — a.e. with respect to restricted measure
- `Filter.eventuallyEq.deriv_eq` — differentiability and a.e. equality
- `HasDerivAt.deriv` — relating HasDerivAt to deriv
- `HasDerivAt.tendsto_slope` — limit of difference quotient

**Tactic hints:**
- `refine ⟨?_, ?_⟩` — split iff into two implications
- `rcases hLip with ⟨B, hB, h⟩` — destructure existential
- `filter_upwards [...]` — combine a.e. statements
- `apply intervalIntegral.norm_integral_le_of_norm_le_const_ae` — for the bounded-derivative case
- `simp [abs_sub_comm]` — handle |x - y| symmetry
- `nlinarith` — close 0 < B, 0 < C arithmetic
- `positivity` — for 0 < B, 0 < C, 0 < |x - y|
- `gcongr` — monotonicity in integrals
- `wlog hxy : x ≤ y` — reduce to ordered case
- `field_simp` — clear denominators in slope calculations
- `exact?` — search for Lipschitz/AC equivalence lemmas
- `apply Filter.Eventually.mono` — refine a.e. statements

## Current Blockers

- 4 `sorry` in `lean/Main.lean` awaiting Codex closure
- The file now checks under `import Mathlib`, but the theorem statements are still encoded against
  the raw epsilon-delta absolute continuity predicate instead of Mathlib's higher-level AC / FTC
  interfaces. That is the essential blocker: the candidate does not yet expose hypotheses in a form
  that existing `Lipschitz` and FTC lemmas can consume directly.
