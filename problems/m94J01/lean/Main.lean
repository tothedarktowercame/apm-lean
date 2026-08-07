import Mathlib

/-!
# APM m94J01

## Statement repairs

None.

## Encoding questions

Convergence in `𝓓′` and `𝓢′` is encoded in its defining weak form: convergence
after evaluation on every compactly supported smooth test function or Schwartz
function, respectively. The moving delta derivative is evaluated by the
problem's formula `(-1)^n f⁽ⁿ⁾(n)`.
-/

open Filter Set
open scoped Distributions SchwartzMap

private lemma apm_m94J01_negOnePow_not_tendsto (a : ℂ) :
    ¬ Tendsto (fun n : ℕ ↦ (-1 : ℂ) ^ n) atTop (nhds a) := by
  intro h
  have hd : Tendsto
      (fun n : ℕ ↦ (-1 : ℂ) ^ (n + 1) - (-1 : ℂ) ^ n)
      atTop (nhds 0) := by
    simpa using (h.comp (tendsto_add_atTop_nat 1)).sub h
  have hnorm := hd.norm
  have hconst : (fun n : ℕ ↦
      ‖(-1 : ℂ) ^ (n + 1) - (-1 : ℂ) ^ n‖) = fun _ ↦ (2 : ℝ) := by
    funext n
    calc
      ‖(-1 : ℂ) ^ (n + 1) - (-1 : ℂ) ^ n‖ =
          ‖-((2 : ℂ) * (-1 : ℂ) ^ n)‖ := by
            congr 1
            rw [pow_succ]
            ring
      _ = ‖(2 : ℂ) * (-1 : ℂ) ^ n‖ := norm_neg _
      _ = 2 := by rw [norm_mul, norm_pow]; norm_num
  rw [hconst] at hnorm
  have htwo : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hzero : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (nhds 0) := by
    simpa using hnorm
  have : (2 : ℝ) = 0 := tendsto_nhds_unique htwo hzero
  norm_num at this

theorem apm_m94j01 :
    (∀ φ : TestFunction (⊤ : TopologicalSpace.Opens ℝ) ℝ ⊤,
      Tendsto
        (fun n : ℕ ↦ (-1 : ℝ) ^ n * iteratedDeriv n φ (n : ℝ))
        atTop (nhds 0)) ∧
    ¬∃ T : TemperedDistribution ℝ ℂ,
      ∀ φ : 𝓢(ℝ, ℂ),
        Tendsto
          (fun n : ℕ ↦ (-1 : ℂ) ^ n * iteratedDeriv n φ (n : ℝ))
          atTop (nhds (T φ)) := by
  constructor
  · intro φ
    obtain ⟨b, hb⟩ := bddAbove_def.mp φ.hasCompactSupport.bddAbove
    have hev : ∀ᶠ n : ℕ in atTop, b < (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop b)
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    have hn_support : (n : ℝ) ∉ tsupport φ := by
      intro hmem
      exact (not_le_of_gt hn) (hb _ hmem)
    have heq : (φ : ℝ → ℝ) =ᶠ[nhds (n : ℝ)] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp hn_support
    rw [heq.iteratedDeriv_eq n, iteratedDeriv_const_zero, mul_zero]
  · /-
    Boundary (closer hop 1): `apm_m94J01_negOnePow_not_tendsto` now compiles
    the final oscillation contradiction once a Schwartz witness with
    `iteratedDeriv n φ n = 1` is available. Thus nonconvergence in the tempered-distribution dual requires an
    explicit Schwartz function whose `n`-th derivative at `n` does not
    converge after multiplication by `(-1)^n`. The standard construction is
    a locally finite sum of disjoint translated bumps
    `(x - n)^n / n! * χ (x - n)`, with `χ = 1` near zero.

    I searched the `SchwartzMap` and bump-function APIs. Completing this route
    requires constructing a smooth compactly supported plateau bump,
    packaging the infinite locally finite sum as a `SchwartzMap`, proving all
    weighted derivative seminorm bounds uniformly in the bump index, and
    calculating its varying-order derivative at each center. No compiled
    sibling supplied this high-order Schwartz interpolation construction
    within this pass.
    -/
    sorry
