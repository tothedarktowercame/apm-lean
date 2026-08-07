import Mathlib

/-!
# APM m02A01: Weak and strong convergence

## Statement repairs

None.

## Encoding questions

None. Weak convergence uses Mathlib's genuine weak topology, and the strict
counterexample is the standard unit-vector sequence in the actual Banach space
`ℓ²(ℕ, ℝ)`.
-/

open Filter

noncomputable section

def apm_m02A01_weaklyConverges {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (x : ℕ → X) (a : X) : Prop :=
  Tendsto (fun n ↦ toWeakSpace ℝ X (x n)) atTop
    (nhds (toWeakSpace ℝ X a))

abbrev apm_m02A01_l2 := lp (fun _ : ℕ ↦ ℝ) 2

def apm_m02A01_basisVector (n : ℕ) : apm_m02A01_l2 :=
  lp.single 2 n 1

theorem apm_m02a01 :
    (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
        (x : ℕ → X) (a b : X),
      apm_m02A01_weaklyConverges x a →
      apm_m02A01_weaklyConverges x b → a = b) ∧
    (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
        (x : ℕ → X) (a : X),
      Tendsto x atTop (nhds a) → apm_m02A01_weaklyConverges x a) ∧
    (apm_m02A01_weaklyConverges apm_m02A01_basisVector 0 ∧
      ¬Tendsto apm_m02A01_basisVector atTop (nhds 0)) ∧
    (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
        [FiniteDimensional ℝ X] (x : ℕ → X) (a : X),
      apm_m02A01_weaklyConverges x a ↔ Tendsto x atTop (nhds a)) := by
  constructor
  · intro X _ _ x a b ha hb
    exact (toWeakSpace ℝ X).injective (tendsto_nhds_unique ha hb)
  · constructor
    · intro X _ _ x a hx
      exact (toWeakSpaceCLM ℝ X).continuous.continuousAt.tendsto.comp hx
    · constructor
      · constructor
        · rw [apm_m02A01_weaklyConverges]
          apply (WeakBilin.tendsto_iff_forall_eval_tendsto
            (B := (topDualPairing ℝ apm_m02A01_l2).flip)
            (separatingDual_iff_injective.mp inferInstance)).2
          intro q
          let y : apm_m02A01_l2 :=
            (InnerProductSpace.toDual ℝ apm_m02A01_l2).symm q
          have hsumm : Summable (fun n : ℕ => ‖y n‖ ^ (2 : ℝ)) := by
            exact (lp.memℓp y).summable (by norm_num)
          have hsquare : Tendsto (fun n : ℕ => ‖y n‖ ^ (2 : ℝ)) atTop (nhds 0) :=
            hsumm.tendsto_atTop_zero
          have hcoordnorm : Tendsto (fun n : ℕ => ‖y n‖) atTop (nhds 0) := by
            have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
            convert hsqrt using 1
            · funext n
              simpa only [Function.comp_apply] using
                (show ‖y n‖ = Real.sqrt (‖y n‖ ^ (2 : ℝ)) by
                  rw [Real.rpow_two, Real.sqrt_sq (norm_nonneg _)])
            · simp
          have hcoord : Tendsto (fun n : ℕ => y n) atTop (nhds 0) := by
            rw [tendsto_zero_iff_norm_tendsto_zero]
            exact hcoordnorm
          convert hcoord using 1
          · funext n
            change q (apm_m02A01_basisVector n) = y n
            calc
              q (apm_m02A01_basisVector n) =
                  inner ℝ y (apm_m02A01_basisVector n) :=
                (InnerProductSpace.toDual_symm_apply).symm
              _ = y n := by
                rw [apm_m02A01_basisVector]
                rw [lp.inner_single_right]
                change (1 : ℝ) * y n = y n
                simp
          · exact congrArg nhds q.map_zero
        · intro hstrong
          have hnorm : Tendsto (fun n ↦ ‖apm_m02A01_basisVector n‖) atTop
              (nhds ‖(0 : apm_m02A01_l2)‖) :=
            continuous_norm.continuousAt.tendsto.comp hstrong
          have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 0) := by
            simpa [apm_m02A01_basisVector, lp.norm_single] using hnorm
          have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hone
          norm_num at this
      · intro X _ _ _ x a
        constructor
        · /-
          Boundary for finite-dimensional weak-to-strong convergence: Mathlib
          records that the weak topology is coarser via `toWeakSpaceCLM`, but
          does not package equality with the norm topology in finite dimension.

          Closer hop 1 tried to regard `(toWeakSpace ℝ X).symm` as a linear map
          and apply `LinearMap.continuous_of_finiteDimensional`. This route does
          not elaborate because `WeakSpace ℝ X` intentionally carries the weak
          topological-module structure rather than the normed-space structure
          expected by the `FiniteDimensional` continuity API. Transporting a
          basis and proving continuity of the inverse coordinate map therefore
          remains necessary.
          -/
          sorry
        · intro hx
          exact (toWeakSpaceCLM ℝ X).continuous.continuousAt.tendsto.comp hx
