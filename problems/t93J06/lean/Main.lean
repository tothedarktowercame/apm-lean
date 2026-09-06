import Mathlib

noncomputable section

abbrev apm_t93j06_Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- A continuous tangent vector field, expressed extrinsically in the
ambient Euclidean space. -/
def apm_t93j06_NowhereZeroField (n : ℕ) : Prop :=
  ∃ v : apm_t93j06_Sphere n → EuclideanSpace ℝ (Fin n),
    Continuous v ∧
      (∀ x, inner ℝ (v x) (x : EuclideanSpace ℝ (Fin n)) = 0) ∧
      (∀ x, v x ≠ 0)

/-- Neither `S²` nor `S⁴` admits a vector field without a zero.  The two
conjuncts retain both parts of the source problem. -/
theorem apm_t93j06 :
    ¬ apm_t93j06_NowhereZeroField 3 ∧
      ¬ apm_t93j06_NowhereZeroField 5 := by
  sorry
