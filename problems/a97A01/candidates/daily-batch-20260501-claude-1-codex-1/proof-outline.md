# Proof Outline — a97A01

_Formalization plan from claude-1, 2026-05-01._

## Theorem Statement (Lean 4)

```lean
import Mathlib

open MeasureTheory Set Filter Topology

noncomputable section

/-- The n-th Rademacher function on [0,1]: +1 on odd dyadic intervals,
    -1 on even dyadic intervals. -/
def rademacher (n : ℕ) (t : ℝ) : ℝ :=
  if t = 1 then -1
  else
    let k := ⌊t * 2^n⌋₊ + 1
    if k % 2 = 1 then 1 else -1

/-- The Rademacher function integrates to 0 over any dyadic interval at
    a strictly coarser level. -/
theorem apm_a97A01_int_dyadic_zero
    (m n : ℕ) (hmn : m < n) (j : ℕ) (hj : j < 2 ^ m) :
    ∫ t in Set.Ico (j / (2:ℝ)^m) ((j+1) / (2:ℝ)^m), rademacher n t = 0 := by sorry

/-- The Rademacher function is essentially bounded by 1. -/
theorem apm_a97A01_rademacher_bound (n : ℕ) (t : ℝ) :
    |rademacher n t| ≤ 1 := by sorry

/-- The Rademacher function is measurable. -/
theorem apm_a97A01_rademacher_measurable (n : ℕ) :
    Measurable (rademacher n) := by sorry

/-- Dyadic step functions are dense in L¹([0,1]). -/
theorem apm_a97A01_dyadic_dense_L1
    (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Icc 0 1) volume) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (s : ℝ → ℝ),
      (∀ t, t ∈ Set.Icc (0:ℝ) 1 → ∃ j : ℕ, j < 2^m ∧
        s t = s (j / (2:ℝ)^m)) ∧
      ∫ t in Set.Icc (0:ℝ) 1, |f t - s t| < ε := by sorry

/-- Main theorem: ∫ f · f_n → 0 for f ∈ L^∞([0,1]) and f_n the Rademacher functions. -/
theorem apm_a97A01_main
    (f : ℝ → ℝ) (hf_meas : AEStronglyMeasurable f (volume.restrict (Set.Icc 0 1)))
    (M : ℝ) (hf_bdd : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 1)), |f t| ≤ M) :
    Tendsto (fun n : ℕ => ∫ t in Set.Icc (0:ℝ) 1, f t * rademacher n t)
      atTop (nhds 0) := by sorry
```

## Mathlib Cross-References

Mathlib cross-references

**Types/structures:**
- `MeasureTheory.Lp` — L^p spaces
- `MeasureTheory.MemLp` — membership in L^p
- `MeasureTheory.Integrable`, `MeasureTheory.IntegrableOn`
- `MeasureTheory.SimpleFunc` — simple/step functions
- `MeasureTheory.AEStronglyMeasurable`
- `volume` — Lebesgue measure on ℝ
- `Set.Icc 0 1`, `Set.Ico (j/2^m) ((j+1)/2^m)` — dyadic intervals
- `Filter.atTop`, `Filter.Tendsto`, `nhds`
- `Nat.floor` (`⌊·⌋₊`) — for the dyadic index

**Key lemmas:**
- `MeasureTheory.integral_indicator` — integral of indicator
- `MeasureTheory.integral_add` / `MeasureTheory.integral_sub` — linearity
- `MeasureTheory.norm_integral_le_integral_norm` — |∫f| ≤ ∫|f|
- `MeasureTheory.integral_mul_le_Linfty_mul_L1` / Hölder for L^∞ × L¹
- `MeasureTheory.Memℒp.integrableOn` — L^∞ on finite measure ⊂ L¹
- `MeasureTheory.SimpleFunc.dense_range_in_L1` — simple functions dense
- `MeasureTheory.Lp.simpleFunc.denseRange` — simple functions dense in L^p
- `MeasureTheory.integrable_indicator_iff` — integrability of 1_A · f
- `MeasureTheory.integral_finset_sum` — splitting integrals over partitions
- `Real.uniformContinuous_of_continuousOn_Icc` — continuous on compact ⇒ uniformly continuous
- `ContinuousMap.dense_range_polynomial` / Stone-Weierstrass for density
- `MeasureTheory.tendsto_integral_of_L1_bound` — DCT-like result
- `Nat.lt_two_pow` / dyadic counting facts
- `intervalIntegral.integral_const` — ∫_a^b c dx = c(b-a)
- `MeasureTheory.integral_Ico_eq_integral_Ioc` — boundary point negligible

**Tactic hints:**
- `induction n with` — induction on the dyadic level for Step 2
- `nlinarith` — close 2^n - 2^m ≥ 0 type bounds
- `positivity` — for 0 < 2^n, 0 < ε, etc.
- `field_simp` — clear 2^n denominators in dyadic interval endpoints
- `ring` — algebraic identities for sums of ±1
- `simp [rademacher]` — unfold the Rademacher definition
- `gcongr` — chain norm/integral inequalities
- `filter_upwards [eventually_gt_atTop m] with n hn` — for "n large enough"
- `refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_` — reduce to ‖·‖ → 0
- `apply Filter.Tendsto.comp` — composition of limits
- `exact?` — search for L¹ density / weak-zero results

## Current Blockers

- 3 `sorry` remain in `lean/Main.lean`.
- Closed already:
  - `apm_a97A01_rademacher_bound`
  - `apm_a97A01_rademacher_measurable`
- Remaining:
  - `apm_a97A01_int_dyadic_zero`
  - `apm_a97A01_dyadic_dense_L1`
  - `apm_a97A01_main`
