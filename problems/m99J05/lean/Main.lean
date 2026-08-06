import Mathlib

/-!
# APM m99J05: A quadratic functional on a Hilbert space

## Statement repairs

None.

## Encoding questions

None. The space is an arbitrary real Hilbert space and `f` is a genuine
continuous linear functional.
-/

noncomputable section

def apm_m99J05_quadratic {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (f : V →L[ℝ] ℝ) (v : V) : ℝ :=
  (1 / 2 : ℝ) * ‖v‖ ^ 2 - f v

def apm_m99J05_isMinimizer {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (f : V →L[ℝ] ℝ) (u : V) : Prop :=
  ∀ v : V, apm_m99J05_quadratic f u ≤ apm_m99J05_quadratic f v

theorem apm_m99j05
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (f : V →L[ℝ] ℝ) :
    (∃! u : V, apm_m99J05_isMinimizer f u) ∧
    (∀ u : V,
      apm_m99J05_isMinimizer f u ↔
        ∀ v : V, inner ℝ u v = f v) := by
  let u : V := (InnerProductSpace.toDual ℝ V).symm f
  have hu : ∀ v : V, inner ℝ u v = f v := by
    intro v
    exact InnerProductSpace.toDual_symm_apply
  have hsquare : ∀ v : V,
      apm_m99J05_quadratic f v = apm_m99J05_quadratic f u +
        (1 / 2 : ℝ) * ‖v - u‖ ^ 2 := by
    intro v
    rw [apm_m99J05_quadratic, apm_m99J05_quadratic, ← hu v, ← hu u,
      norm_sub_sq_real, real_inner_self_eq_norm_sq]
    have hvu : inner ℝ v u = inner ℝ u v := (real_inner_comm v u).symm
    nlinarith
  have hmin_iff : ∀ v : V, apm_m99J05_isMinimizer f v ↔ v = u := by
    intro v
    constructor
    · intro hv
      have hle := hv u
      rw [hsquare u, hsquare v] at hle
      simp only [sub_self, norm_zero] at hle
      have hs : 0 ≤ ‖v - u‖ ^ 2 := sq_nonneg _
      have hz : ‖v - u‖ = 0 := by nlinarith [norm_nonneg (v - u)]
      exact sub_eq_zero.mp (norm_eq_zero.mp hz)
    · rintro rfl w
      rw [hsquare w]
      nlinarith [sq_nonneg ‖w - u‖]
  have hchar : ∀ v : V,
      apm_m99J05_isMinimizer f v ↔ ∀ w : V, inner ℝ v w = f w := by
    intro v
    rw [hmin_iff v]
    constructor
    · rintro rfl
      exact hu
    · intro hv
      apply ext_inner_right ℝ
      intro w
      rw [hv w, hu w]
  constructor
  · refine ⟨u, (hchar u).2 hu, ?_⟩
    intro w hw
    have hw' := (hchar w).1 hw
    apply ext_inner_right ℝ
    intro v
    rw [hw' v, hu v]
  · exact hchar
