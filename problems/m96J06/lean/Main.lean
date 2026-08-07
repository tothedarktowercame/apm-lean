import Mathlib

/-!
# APM m96J06: A nonlinear functional equation near zero

## Statement repairs

None.

## Encoding questions

None. The open neighborhood is the explicit sup-norm ball
`{y ∈ C([-2,2]) | ‖y‖∞ < 1/48}`. Functions are represented on `ℝ` with all
continuity, bounds, and equations restricted to the exact interval `[-2,2]`.
-/

open Set

noncomputable section

def apm_m96J06_inNeighborhood (y : ℝ → ℝ) : Prop :=
  ContinuousOn y (Icc (-2 : ℝ) 2) ∧
  ∀ t ∈ Icc (-2 : ℝ) 2, |y t| < (1 / 48 : ℝ)

def apm_m96J06_isSolution (x y : ℝ → ℝ) : Prop :=
  ContinuousOn x (Icc (-2 : ℝ) 2) ∧
  ∀ t ∈ Icc (-2 : ℝ) 2,
    x t - 2 * x 0 + x (t / 2 + 1) * x (t / 2 - 1) = y t

/-- The linearization at zero is its own inverse, even before restricting to
the continuous-function Banach space. -/
def apm_m96J06_linearPart (x : ℝ → ℝ) : ℝ → ℝ :=
  fun t ↦ x t - 2 * x 0

lemma apm_m96J06_linearPart_involutive (x : ℝ → ℝ) :
    apm_m96J06_linearPart (apm_m96J06_linearPart x) = x := by
  funext t
  simp [apm_m96J06_linearPart]
  ring

/-- Both rescaled arguments in the quadratic term remain in the domain. -/
lemma apm_m96J06_half_shift_mem {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) :
    t / 2 + 1 ∈ Icc (-2 : ℝ) 2 ∧ t / 2 - 1 ∈ Icc (-2 : ℝ) 2 := by
  constructor <;> constructor <;> linarith [ht.1, ht.2]

/-- The quadratic term preserves continuity on the restricted interval. -/
lemma apm_m96J06_quadratic_continuousOn {x : ℝ → ℝ}
    (hx : ContinuousOn x (Icc (-2 : ℝ) 2)) :
    ContinuousOn (fun t ↦ x (t / 2 + 1) * x (t / 2 - 1)) (Icc (-2 : ℝ) 2) := by
  have hp : ContinuousOn (fun t : ℝ ↦ t / 2 + 1) (Icc (-2 : ℝ) 2) :=
    ((continuous_id.div_const (2 : ℝ)).add continuous_const).continuousOn
  have hm : ContinuousOn (fun t : ℝ ↦ t / 2 - 1) (Icc (-2 : ℝ) 2) :=
    ((continuous_id.div_const (2 : ℝ)).sub continuous_const).continuousOn
  exact (hx.comp hp fun _ ht ↦ (apm_m96J06_half_shift_mem ht).1).mul
    (hx.comp hm fun _ ht ↦ (apm_m96J06_half_shift_mem ht).2)

/-- Pointwise form of the quadratic Lipschitz estimate on a sup-norm ball. -/
lemma apm_m96J06_quadratic_sub_bound
    {x z : ℝ → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hx : ∀ t ∈ Icc (-2 : ℝ) 2, |x t| ≤ r)
    (hz : ∀ t ∈ Icc (-2 : ℝ) 2, |z t| ≤ r)
    {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) :
    |x (t / 2 + 1) * x (t / 2 - 1) -
        z (t / 2 + 1) * z (t / 2 - 1)| ≤
      2 * r * max |x (t / 2 + 1) - z (t / 2 + 1)|
        |x (t / 2 - 1) - z (t / 2 - 1)| := by
  have hp := (apm_m96J06_half_shift_mem ht).1
  have hm := (apm_m96J06_half_shift_mem ht).2
  calc
    _ = |x (t / 2 + 1) * (x (t / 2 - 1) - z (t / 2 - 1)) +
        (x (t / 2 + 1) - z (t / 2 + 1)) * z (t / 2 - 1)| := by ring_nf
    _ ≤ |x (t / 2 + 1)| * |x (t / 2 - 1) - z (t / 2 - 1)| +
        |x (t / 2 + 1) - z (t / 2 + 1)| * |z (t / 2 - 1)| := by
      simpa [abs_mul] using abs_add_le
        (x (t / 2 + 1) * (x (t / 2 - 1) - z (t / 2 - 1)))
        ((x (t / 2 + 1) - z (t / 2 + 1)) * z (t / 2 - 1))
    _ ≤ r * |x (t / 2 - 1) - z (t / 2 - 1)| +
        |x (t / 2 + 1) - z (t / 2 + 1)| * r := by
      gcongr
      · exact hx _ hp
      · exact hz _ hm
    _ ≤ 2 * r * max |x (t / 2 + 1) - z (t / 2 + 1)|
        |x (t / 2 - 1) - z (t / 2 - 1)| := by
      have h1 := le_max_left |x (t / 2 + 1) - z (t / 2 + 1)|
        |x (t / 2 - 1) - z (t / 2 - 1)|
      have h2 := le_max_right |x (t / 2 + 1) - z (t / 2 + 1)|
        |x (t / 2 - 1) - z (t / 2 - 1)|
      nlinarith

abbrev apm_m96J06_interval := Icc (-2 : ℝ) 2

private def apm_m96J06_zeroPoint : apm_m96J06_interval :=
  ⟨0, by constructor <;> norm_num⟩

private def apm_m96J06_plusShift :
    C(apm_m96J06_interval, apm_m96J06_interval) where
  toFun t := ⟨t.1 / 2 + 1, (apm_m96J06_half_shift_mem t.2).1⟩
  continuous_toFun := by fun_prop

private def apm_m96J06_minusShift :
    C(apm_m96J06_interval, apm_m96J06_interval) where
  toFun t := ⟨t.1 / 2 - 1, (apm_m96J06_half_shift_mem t.2).2⟩
  continuous_toFun := by fun_prop

/-- The quadratic term bundled on `C([-2,2], ℝ)`. -/
def apm_m96J06_quadraticC
    (x : C(apm_m96J06_interval, ℝ)) : C(apm_m96J06_interval, ℝ) :=
  x.comp apm_m96J06_plusShift * x.comp apm_m96J06_minusShift

lemma apm_m96J06_quadraticC_norm_le
    (x : C(apm_m96J06_interval, ℝ)) {r : ℝ} (hr : 0 ≤ r)
    (hx : ‖x‖ ≤ r) : ‖apm_m96J06_quadraticC x‖ ≤ r ^ 2 := by
  refine (ContinuousMap.norm_le _ (sq_nonneg r)).2 ?_
  intro t
  rw [Real.norm_eq_abs, apm_m96J06_quadraticC, ContinuousMap.mul_apply,
    abs_mul]
  have hp : |x (apm_m96J06_plusShift t)| ≤ r := by
    exact (by simpa [Real.norm_eq_abs] using
      (x.norm_coe_le_norm (apm_m96J06_plusShift t)).trans hx)
  have hm : |x (apm_m96J06_minusShift t)| ≤ r := by
    exact (by simpa [Real.norm_eq_abs] using
      (x.norm_coe_le_norm (apm_m96J06_minusShift t)).trans hx)
  change |x (apm_m96J06_plusShift t)| *
      |x (apm_m96J06_minusShift t)| ≤ r ^ 2
  calc
    _ ≤ r * r := mul_le_mul hp hm (abs_nonneg _) hr
    _ = r ^ 2 := by ring

/-- The linear involution bundled on the actual Banach space `C([-2,2], ℝ)`. -/
def apm_m96J06_linearPartC
    (x : C(apm_m96J06_interval, ℝ)) : C(apm_m96J06_interval, ℝ) where
  toFun t := x t - 2 * x apm_m96J06_zeroPoint
  continuous_toFun := x.continuous.sub continuous_const

lemma apm_m96J06_linearPartC_norm_le
    (x : C(apm_m96J06_interval, ℝ)) :
    ‖apm_m96J06_linearPartC x‖ ≤ 3 * ‖x‖ := by
  refine (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (norm_nonneg x))).2 ?_
  intro t
  rw [Real.norm_eq_abs]
  calc
    |x t - 2 * x apm_m96J06_zeroPoint| ≤
        |x t| + 2 * |x apm_m96J06_zeroPoint| := by
      simpa [abs_mul] using abs_sub (x t) (2 * x apm_m96J06_zeroPoint)
    _ ≤ ‖x‖ + 2 * ‖x‖ := by
      gcongr <;> simpa [Real.norm_eq_abs] using x.norm_coe_le_norm _
    _ = 3 * ‖x‖ := by ring

lemma apm_m96J06_linearPartC_involutive
    (x : C(apm_m96J06_interval, ℝ)) :
    apm_m96J06_linearPartC (apm_m96J06_linearPartC x) = x := by
  ext t
  simp [apm_m96J06_linearPartC, apm_m96J06_zeroPoint]
  ring

/-- The same involution as a bounded linear operator, with the explicit bound
used by the contraction estimate. -/
def apm_m96J06_linearPartCLM :
    C(apm_m96J06_interval, ℝ) →L[ℝ] C(apm_m96J06_interval, ℝ) :=
  LinearMap.mkContinuous
    { toFun := apm_m96J06_linearPartC
      map_add' := by
        intro x z
        ext t
        simp [apm_m96J06_linearPartC]
        ring
      map_smul' := by
        intro c x
        ext t
        simp [apm_m96J06_linearPartC]
        ring }
    3 (by
      intro x
      exact apm_m96J06_linearPartC_norm_le x)

lemma apm_m96J06_linearPartCLM_involutive
    (x : C(apm_m96J06_interval, ℝ)) :
    apm_m96J06_linearPartCLM (apm_m96J06_linearPartCLM x) = x :=
  apm_m96J06_linearPartC_involutive x

theorem apm_m96j06 :
    ∀ y : ℝ → ℝ,
      apm_m96J06_inNeighborhood y →
        ∃ x : ℝ → ℝ,
          apm_m96J06_isSolution x y ∧
          ∀ t ∈ Icc (-2 : ℝ) 2, |x t| ≤ (1 / 12 : ℝ) := by
  /-
  PARTIAL.  `apm_m96J06_linearPart_involutive` proves that the linearization
  `x ↦ x - 2 x(0)` is algebraically its own inverse, and
  `apm_m96J06_half_shift_mem` proves that both arguments of the quadratic term
  remain in `[-2,2]`.  This pass additionally proves
  `apm_m96J06_quadratic_continuousOn`, closing preservation of the restricted
  continuous-function space, and `apm_m96J06_quadratic_sub_bound`, the
  pointwise two-radius Lipschitz estimate from which the sup-norm contraction
  bound follows.

  Closer hop 1 now bundles the actual Banach space as
  `C(Icc (-2) 2, ℝ)` and defines `apm_m96J06_linearPartCLM`.  The lemmas
  `apm_m96J06_linearPartC_norm_le` and
  `apm_m96J06_linearPartCLM_involutive` prove respectively the explicit
  operator estimate and that this bounded linear map is its own inverse.

  The remaining construction is to bundle the quadratic self-map on this
  `ContinuousMap` space, lift the supplied pointwise estimate to its sup norm,
  prove self-mapping and contraction on the closed ball, then apply
  `ContractingWith.exists_fixedPoint'` to the closed ball of radius `1/12`.
  Mathlib supplies that abstract fixed-point theorem (and sibling `t91A04`
  demonstrates its global wrapper), but searches of `LEMMA-INDEX.md`, 172
  closed artifacts, `ConstructionTargets/`, `YoungL2.lean`, and Mathlib's
  `ContinuousMap`/closed-ball fixed-point APIs found no helper assembling this
  custom nonlinear self-map and all of its ball estimates.

  Closer hop 2 bundles both half-shifts as continuous self-maps of the compact
  interval and defines `apm_m96J06_quadraticC` directly in the continuous-map
  algebra. The new estimate `apm_m96J06_quadraticC_norm_le` proves
  `‖Q(x)‖ ≤ r²` whenever `‖x‖ ≤ r`. Thus preservation of the Banach space and
  the self-map size estimate are closed. The remaining work is the difference
  estimate in the continuous-map norm, composing it with the norm-three linear
  involution, and applying the closed-ball contraction theorem with the given
  constants.
  -/
  sorry
