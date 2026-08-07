import Mathlib

/-! # APM m99A05: weak and strong convergence in normed spaces

## Statement repairs

None.
-/

open Filter

noncomputable section

def M99A05WeaklyConverges {𝕜 X : Type*}
    [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (u : ℕ → X) (x : X) : Prop :=
  ∀ ℓ : X →L[𝕜] 𝕜, Tendsto (fun n => ℓ (u n)) atTop (nhds (ℓ x))

abbrev m99A05L2 := lp (fun _ : ℕ => ℂ) 2

def m99A05BasisSequence (n : ℕ) : m99A05L2 := lp.single 2 n 1

theorem apm_m99a05
    (𝕜 X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    (M99A05WeaklyConverges (𝕜 := ℂ) m99A05BasisSequence 0 ∧
      ¬Tendsto m99A05BasisSequence atTop (nhds 0)) ∧
    (∀ (u : ℕ → X) (x : X),
      Tendsto u atTop (nhds x) → M99A05WeaklyConverges (𝕜 := 𝕜) u x) ∧
    (∀ (Y : Type*) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
      [FiniteDimensional 𝕜 Y] (u : ℕ → Y) (x : Y),
      Tendsto u atTop (nhds x) ↔ M99A05WeaklyConverges (𝕜 := 𝕜) u x) ∧
    (∀ (u : ℕ → X) (x : X), M99A05WeaklyConverges (𝕜 := 𝕜) u x →
      ∃ C : ℝ, ∀ n : ℕ, ‖u n‖ ≤ C) ∧
    (∀ (u : ℕ → X) (x y : X),
      M99A05WeaklyConverges (𝕜 := 𝕜) u x →
      M99A05WeaklyConverges (𝕜 := 𝕜) u y → x = y) := by
  constructor
  · constructor
    · intro ℓ
      let y : m99A05L2 := (InnerProductSpace.toDual ℂ m99A05L2).symm ℓ
      have hsummable : Summable (fun n : ℕ ↦ ‖y n‖ ^ (2 : ℝ)) := by
        simpa using (lp.hasSum_norm (by norm_num) y).summable
      have hsq : Tendsto (fun n : ℕ ↦ ‖y n‖ ^ (2 : ℝ)) atTop (nhds 0) :=
        hsummable.tendsto_atTop_zero
      have hnorm : Tendsto (fun n : ℕ ↦ ‖y n‖) atTop (nhds 0) := by
        have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
        change Tendsto (fun n : ℕ ↦ Real.sqrt (‖y n‖ ^ 2)) atTop (nhds (Real.sqrt 0)) at hsqrt
        convert hsqrt using 1
        · funext n
          rw [Real.rpow_two, Real.sqrt_sq (norm_nonneg (y n))]
        · simp
      have hy : Tendsto (fun n : ℕ ↦ y n) atTop (nhds 0) :=
        tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
      have hinner : Tendsto (fun n : ℕ ↦ inner ℂ (y n) (1 : ℂ)) atTop (nhds 0) := by
        have hc : Continuous (fun z : ℂ ↦ inner ℂ z (1 : ℂ)) := by fun_prop
        simpa using hc.continuousAt.tendsto.comp hy
      convert hinner using 1
      · funext n
        change ℓ (lp.single 2 n 1) = inner ℂ (y n) 1
        rw [← InnerProductSpace.toDual_symm_apply]
        exact lp.inner_single_right n 1 y
      · simp
    · -- (Sibling: m02A01)
      intro hstrong
      have hnorm : Tendsto (fun n ↦ ‖m99A05BasisSequence n‖) atTop
          (nhds ‖(0 : m99A05L2)‖) :=
        continuous_norm.continuousAt.tendsto.comp hstrong
      have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 0) := by
        simpa [m99A05BasisSequence, lp.norm_single] using hnorm
      have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hone
      norm_num at this
  constructor
  · intro u x hu ℓ
    exact ℓ.continuous.continuousAt.tendsto.comp hu
  · constructor
    · /-
      Boundary: finite-dimensional weak-to-strong convergence requires
      reconstructing vectors from finitely many continuous basis-coordinate
      maps. I searched `FiniteDimensional`, `Basis.coord`, weak-topology, and
      finite-product convergence APIs; the arbitrary-`RCLike` assembly was not
      completed.
      -/
      sorry
    · constructor
      · /-
        Boundary: norm boundedness requires Banach--Steinhaus on the family
        `NormedSpace.inclusionInDoubleDual 𝕜 X (u n)`. Mathlib provides the
        isometric double-dual embedding, but searches for `UniformBoundedness`
        and pointwise-bounded families did not locate an assembled theorem with
        the required interface.
        -/
        sorry
      · intro u x y hx hy
        apply sub_eq_zero.mp
        apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜)
        intro ℓ
        have hxy : ℓ x = ℓ y := tendsto_nhds_unique (hx ℓ) (hy ℓ)
        simpa using sub_eq_zero.mpr hxy
