import Mathlib

noncomputable section

open MeasureTheory
open scoped BigOperators Real ENNReal

namespace ApmCanaries.Frames.A03J04

/-- The Euclidean space `ℝⁿ`. -/
abbrev Rn (n : ℕ) := EuclideanSpace (Fin n) ℝ

variable {μ : Measure ℝ} [SigmaFinite μ]

/-- Distribution function attached to a measurable function. -/
def distributionFunction {n : ℕ} (f : Rn n → ℝ) (α : ℝ) : ℝ≥0∞ :=
  volume {x | |f x| > α}

/-- An explicit placeholder for the dimensional constant that appears in part (c). -/
def weakL1Constant (n : ℕ) (p : ℝ) : ℝ :=
  1 / (1 - p)

/-- The weak–`L¹` control `α λ(α) ≤ M` demanded in parts (b)–(c). -/
def weakL1Control {n : ℕ} (f : Rn n → ℝ) (M : ℝ) : Prop :=
  0 ≤ M ∧ ∀ ⦃α : ℝ⦄, 0 < α → α * (distributionFunction f α).toReal ≤ M

/-- Layer-cake identity: reformulated as an inequality we will actually use.
Currently this is a placeholder theorem stating the classical formula
for nonnegative functions whose proof is not yet in Lean. -/
theorem layer_cake_le
    (f : ℝ → ℝ) (hf : Integrable f μ) (hpos : 0 ≤ f) :
    ∫ x, f x ∂μ = ∫ a in Set.Ioi (0 : ℝ), μ.real {x | f x > a} := by
  classical
  have hnonneg : 0 ≤ᵐ[μ] f := Eventually.of_forall hpos
  simpa [gt_iff_lt] using hf.integral_eq_integral_meas_lt hnonneg

/-- Part (a): the layer-cake identity on `ℝⁿ` specialized to Lebesgue measure. -/
theorem layer_cake_identity
    {n : ℕ} (f : Rn n → ℝ) (hf : Integrable f volume) :
    ∫ x, |f x| ∂volume =
      ∫ a in Set.Ioi (0 : ℝ), (distributionFunction f a).toReal := by
  classical
  -- TODO: expand `layer_cake_le` to absolute values and link the coercions
  -- between extended-real and real measures.
  sorry

/-- Part (b): weak `L¹` control implies local `Lᵖ` integrability on finite-measure sets. -/
theorem weakL1_to_localLp
    {n : ℕ} {p : ℝ} {f : Rn n → ℝ} {E : Set (Rn n)}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hE : MeasurableSet E) (hfin : volume E ≠ ∞)
    {M : ℝ} (hM : weakL1Control f M) :
    IntegrableOn (fun x => |f x| ^ p) E volume := by
  classical
  -- Skeleton: split the integral at the threshold `a := M / m(E)`
  -- using `layer_cake_identity`, then control each part by the weak bound.
  -- Remaining work: translate the combinatorics of the formal proof.
  sorry

/-- Algebraic estimate corresponding to splitting the layer-cake integral. -/
lemma weak_L1_split_bound
    {p m M : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hm : 0 < m) (hM : 0 < M) :
    let a := M / m in
    m * a ^ p + (p / (1 - p)) * M * a ^ (p - 1) =
      (1 / (1 - p)) * M ^ p * m ^ (1 - p) := by
  classical
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hden : 1 - p ≠ 0 := sub_ne_zero.mpr (ne_of_gt (sub_pos.mpr hp1))
  set a := M / m with ha
  have ha_pos : 0 < a := by
    dsimp [a]
    exact div_pos hM hm
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  have hm_nonneg : 0 ≤ m := le_of_lt hm
  have hM_def : M = a * m := by
    field_simp [ha, hm0]
  have hpow_factor :
      a * a ^ (p - 1) = a ^ p := by
    have := Real.rpow_add_one ha_ne (p - 1)
    have hsum : (p - 1) + 1 = p := by ring
    simpa [hsum, sub_eq_add_neg, mul_comm] using this.symm
  have lhs_simpl :
      m * a ^ p + (p / (1 - p)) * M * a ^ (p - 1)
        = m * a ^ p + (p / (1 - p)) * m * a ^ p := by
    simp [hM_def, hpow_factor, mul_comm, mul_left_comm, mul_assoc]
  have lhs_eval :
      m * a ^ p + (p / (1 - p)) * m * a ^ p =
        (1 / (1 - p)) * m * a ^ p := by
    field_simp [hden, mul_comm, mul_left_comm, mul_assoc]
  have hmul_pow :
      M ^ p = a ^ p * m ^ p := by
    have h := Real.mul_rpow ha_nonneg hm_nonneg (z := p)
    simpa [hM_def, mul_comm, mul_left_comm, mul_assoc] using h
  have hpow_m :
      m ^ p * m ^ (1 - p) = m := by
    have := Real.rpow_add hm p (1 - p)
    have hsum : p + (1 - p) = 1 := by ring
    simpa [hsum] using this.symm
  have lhs_total :
      m * a ^ p + (p / (1 - p)) * M * a ^ (p - 1) =
        (1 / (1 - p)) * m * a ^ p :=
    lhs_simpl.trans lhs_eval
  have rhs_eval :
      (1 / (1 - p)) * M ^ p * m ^ (1 - p) =
        (1 / (1 - p)) * m * a ^ p := by
    calc
      (1 / (1 - p)) * M ^ p * m ^ (1 - p)
          = (1 / (1 - p)) * (a ^ p * m ^ p) * m ^ (1 - p) := by
            simpa [hmul_pow]
      _ = (1 / (1 - p)) * a ^ p * (m ^ p * m ^ (1 - p)) := by
            simp [mul_comm, mul_left_comm, mul_assoc]
      _ = (1 / (1 - p)) * a ^ p * m := by simpa [hpow_m]
      _ = (1 / (1 - p)) * m * a ^ p := by
            simp [mul_comm]
  exact lhs_total.trans rhs_eval.symm

/-- Part (c): quantitative estimate once the integral in part (b) is finite. -/
theorem weakL1_integral_bound
    {n : ℕ} {p : ℝ} {f : Rn n → ℝ} {E : Set (Rn n)}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hE : MeasurableSet E) (hfin : volume E ≠ ∞)
    {M : ℝ} (hM : weakL1Control f M) :
    ∫ x in E, |f x| ^ p ∂volume ≤
      weakL1Constant n p * (volume E).toReal ^ (1 - p) * M ^ p := by
  classical
  -- Skeleton: pair `weakL1_to_localLp` with `weak_L1_split_bound` and
  -- reorganize the algebra arising from the layer-cake splitting.
  sorry

end ApmCanaries.Frames.A03J04
