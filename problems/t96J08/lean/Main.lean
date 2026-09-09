import Mathlib
import ConstructionTargets.UnitDiskInverseSqrtIntegrability

/-!
# APM t96J08

## Statement repairs

None.

## Encoding questions

Mathlib does not currently bundle integration of differential forms over
oriented surfaces.  The specified upper hemisphere is therefore encoded by
its standard orientation-preserving parametrization over the closed unit disk.
The two-form itself, its exterior derivative, and exactness are encoded by
their concrete coordinate formulas, rather than by opaque placeholders.
-/

noncomputable section

open MeasureTheory

abbrev apm_t96j08_Point := EuclideanSpace ℝ (Fin 3)
abbrev apm_t96j08_DiskPoint := EuclideanSpace ℝ (Fin 2)

def apm_t96j08_omega
    (p u v : apm_t96j08_Point) : ℝ :=
  p 0 * (u 1 * v 2 - u 2 * v 1) +
  p 1 * (u 0 * v 2 - u 2 * v 0) +
  p 2 * (u 0 * v 1 - u 1 * v 0)

/-- The coordinate exterior derivative of the displayed two-form. -/
def apm_t96j08_domega
    (_p u v w : apm_t96j08_Point) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) -
  u 1 * (v 0 * w 2 - v 2 * w 0) +
  u 2 * (v 0 * w 1 - v 1 * w 0)

def apm_t96j08_IsClosed : Prop :=
  ∀ p u v w : apm_t96j08_Point, apm_t96j08_domega p u v w = 0

def apm_t96j08_dOneForm
    (η : apm_t96j08_Point → apm_t96j08_Point →L[ℝ] ℝ)
    (p u v : apm_t96j08_Point) : ℝ :=
  (fderiv ℝ (fun q => η q v) p) u -
    (fderiv ℝ (fun q => η q u) p) v

def apm_t96j08_IsExact : Prop :=
  ∃ η : apm_t96j08_Point → apm_t96j08_Point →L[ℝ] ℝ,
    ContDiff ℝ (⊤ : ℕ∞) (fun q : apm_t96j08_Point => η q) ∧
    ∀ p u v, apm_t96j08_dOneForm η p u v = apm_t96j08_omega p u v

def apm_t96j08_etaForm
    (η : apm_t96j08_Point → apm_t96j08_Point →L[ℝ] ℝ) :
    apm_t96j08_Point →
      apm_t96j08_Point [⋀^Fin 1]→L[ℝ] ℝ :=
  fun p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ _ _ (0 : Fin 1) (η p)

lemma apm_t96j08_extDeriv_etaForm_apply
    (η : apm_t96j08_Point → apm_t96j08_Point →L[ℝ] ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (p u v : apm_t96j08_Point) :
    extDeriv (apm_t96j08_etaForm η) p ![u, v] =
      apm_t96j08_dOneForm η p u v := by
  have heta : ContDiff ℝ (⊤ : ℕ∞) (apm_t96j08_etaForm η) := by
    unfold apm_t96j08_etaForm
    exact (ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := apm_t96j08_Point) (F := ℝ)
      (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp hη
  rw [extDeriv_apply (heta.differentiable (by simp) p)]
  simp [apm_t96j08_etaForm, apm_t96j08_dOneForm, Fin.removeNth, sub_eq_add_neg]

def apm_t96j08_upperHemisphere (q : apm_t96j08_DiskPoint) : apm_t96j08_Point :=
  WithLp.toLp 2 ![q 0, q 1, 1 + Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)]

def apm_t96j08_paramTangentX (q : apm_t96j08_DiskPoint) : apm_t96j08_Point :=
  WithLp.toLp 2 ![1, 0, -(q 0) / Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)]

def apm_t96j08_paramTangentY (q : apm_t96j08_DiskPoint) : apm_t96j08_Point :=
  WithLp.toLp 2 ![0, 1, -(q 1) / Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)]

/-- Reflection of the parameter disk across the diagonal. -/
def apm_t96j08_swap (q : apm_t96j08_DiskPoint) : apm_t96j08_DiskPoint :=
  WithLp.toLp 2 ![q 1, q 0]

/-- The coordinate swap as a volume-preserving linear isometry. -/
def apm_t96j08_swapEquiv :
    apm_t96j08_DiskPoint ≃ₗᵢ[ℝ] apm_t96j08_DiskPoint :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)

lemma apm_t96j08_swapEquiv_apply (q : apm_t96j08_DiskPoint) :
    apm_t96j08_swapEquiv q = apm_t96j08_swap q := by
  ext i
  fin_cases i <;>
    simp [apm_t96j08_swapEquiv, apm_t96j08_swap,
      LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

@[simp] lemma apm_t96j08_swap_zero (q : apm_t96j08_DiskPoint) :
    apm_t96j08_swap q 0 = q 1 := by
  simp [apm_t96j08_swap, Matrix.cons_val_zero]

@[simp] lemma apm_t96j08_swap_one (q : apm_t96j08_DiskPoint) :
    apm_t96j08_swap q 1 = q 0 := by
  simp [apm_t96j08_swap, Matrix.cons_val_one]

lemma apm_t96j08_singularTerm_swap (q : apm_t96j08_DiskPoint) :
    ((apm_t96j08_swap q 0) ^ 2 - (apm_t96j08_swap q 1) ^ 2) /
        Real.sqrt
          (1 - (apm_t96j08_swap q 0) ^ 2 - (apm_t96j08_swap q 1) ^ 2) =
      -(((q 0) ^ 2 - (q 1) ^ 2) /
        Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)) := by
  simp
  ring_nf

def apm_t96j08_hemisphereIntegral : ℝ :=
  ∫ q : apm_t96j08_DiskPoint in Metric.closedBall 0 1,
    apm_t96j08_omega (apm_t96j08_upperHemisphere q)
      (apm_t96j08_paramTangentX q) (apm_t96j08_paramTangentY q)

lemma apm_t96j08_pullback_eq (q : apm_t96j08_DiskPoint) :
    apm_t96j08_omega (apm_t96j08_upperHemisphere q)
        (apm_t96j08_paramTangentX q) (apm_t96j08_paramTangentY q) =
      1 + Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2) +
        ((q 0) ^ 2 - (q 1) ^ 2) /
          Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2) := by
  simp [apm_t96j08_omega, apm_t96j08_upperHemisphere,
    apm_t96j08_paramTangentX, apm_t96j08_paramTangentY,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  ring

lemma apm_t96j08_integral_singularTerm_eq_zero :
    (∫ q : apm_t96j08_DiskPoint in Metric.closedBall 0 1,
      ((q 0) ^ 2 - (q 1) ^ 2) /
        Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)) = 0 := by
  let g : apm_t96j08_DiskPoint → ℝ := fun q ↦
    ((q 0) ^ 2 - (q 1) ^ 2) /
      Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)
  have hpre : apm_t96j08_swapEquiv ⁻¹' Metric.closedBall 0 1 =
      Metric.closedBall (0 : apm_t96j08_DiskPoint) 1 := by
    ext q
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      LinearIsometryEquiv.norm_map]
  have h := apm_t96j08_swapEquiv.measurePreserving.setIntegral_preimage_emb
    apm_t96j08_swapEquiv.toMeasurableEquiv.measurableEmbedding g
    (Metric.closedBall (0 : apm_t96j08_DiskPoint) 1)
  rw [hpre] at h
  have hswap : ∀ q, g (apm_t96j08_swapEquiv q) = -g q := by
    intro q
    rw [apm_t96j08_swapEquiv_apply]
    exact apm_t96j08_singularTerm_swap q
  simp_rw [hswap, MeasureTheory.integral_neg] at h
  change (∫ q : apm_t96j08_DiskPoint in Metric.closedBall 0 1, g q) = 0
  linarith

/-- The coordinate exterior derivative is nonzero on the standard oriented
basis. This is the direct obstruction to closedness. -/
lemma apm_t96j08_not_isClosed : ¬apm_t96j08_IsClosed := by
  intro h
  have hh := h 0 (WithLp.toLp 2 ![1, 0, 0])
    (WithLp.toLp 2 ![0, 1, 0]) (WithLp.toLp 2 ![0, 0, 1])
  norm_num [apm_t96j08_domega, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at hh


open Metric Real Set
open scoped Interval
def radialSqrt (r : ℝ) := Real.sqrt (1-r^2)
lemma radialSqrt_eq_rpow {r : ℝ} (_hr : 0 ≤ 1-r^2) : radialSqrt r = (1-r^2)^((1/2:ℝ)) := by simp [radialSqrt, Real.sqrt_eq_rpow]
lemma radialSqrt_eq_zero_of_one_le {r : ℝ} (hr : 1 ≤ r) : radialSqrt r = 0 := by
  exact Real.sqrt_eq_zero'.mpr (by nlinarith)
lemma intervalIntegrable_mul_radialSqrt : IntervalIntegrable (fun r : ℝ => r * radialSqrt r) volume 0 1 := by
  apply Continuous.intervalIntegrable
  unfold radialSqrt
  fun_prop
abbrev E2 := EuclideanSpace ℝ (Fin 2)
theorem integral_zero_one_mul_radialSqrt :
    (∫ r in (0 : ℝ)..1, r * radialSqrt r) = 1 / 3 := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := (0 : ℝ)) (b := 1)
    (f := fun r : ℝ => 1 - r ^ 2) (f' := fun r : ℝ => -2 * r)
    (g := fun u : ℝ => u ^ ((1 / 2 : ℝ)))
    (by fun_prop)
    (fun r _ => by
      simpa [mul_comm] using
        (hasDerivAt_const r 1).sub ((hasDerivAt_id r).pow 2))
    (fun r hr => by norm_num at hr ⊢; linarith)
  have hrpow : (∫ u in (0 : ℝ)..1, u ^ ((1 / 2 : ℝ))) = 2 / 3 := by
    rw [integral_rpow]
    · norm_num
    · left
      norm_num
  have hreverse : (∫ u in (1 : ℝ)..0, u ^ ((1 / 2 : ℝ))) = -(2 / 3) := by
    rw [intervalIntegral.integral_symm, hrpow]
  dsimp only [Function.comp_apply] at hsub
  norm_num only [zero_pow, one_pow, sub_zero] at hsub
  change (∫ r in (0 : ℝ)..1,
      (1 - r ^ 2) ^ ((1 / 2 : ℝ)) * (-2 * r)) =
        ∫ u in (1 : ℝ)..0, u ^ ((1 / 2 : ℝ)) at hsub
  rw [hreverse] at hsub
  have hscale :
      (∫ r in (0 : ℝ)..1,
        (1 - r ^ 2) ^ ((1 / 2 : ℝ)) * (-2 * r)) =
        -2 * ∫ r in (0 : ℝ)..1, r * radialSqrt r := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    norm_num at hr
    change (1 - r ^ 2) ^ ((1 / 2 : ℝ)) * (-2 * r) =
      -2 * (r * radialSqrt r)
    rw [radialSqrt_eq_rpow (by nlinarith)]
    ring
  rw [hscale] at hsub
  linarith

theorem integral_Ioi_mul_radialSqrt :
    (∫ r in Ioi (0 : ℝ), r * radialSqrt r) = 1 / 3 := by
  have htail : IntegrableOn (fun r : ℝ => r * radialSqrt r) (Ioi 1) := by
    apply integrableOn_zero.congr_fun
    · intro r hr
      simp [radialSqrt_eq_zero_of_one_le hr.le]
    · exact measurableSet_Ioi
  have hsplit := intervalIntegral.integral_interval_add_Ioi'
    (a := (0 : ℝ)) (b := 1) intervalIntegrable_mul_radialSqrt htail
  rw [integral_zero_one_mul_radialSqrt] at hsplit
  have hzero : (∫ r in Ioi (1 : ℝ), r * radialSqrt r) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simp [radialSqrt_eq_zero_of_one_le hr.le]
  rw [hzero, add_zero] at hsplit
  exact hsplit.symm

theorem integral_radialSqrt_euclidean :
    (∫ q : E2, radialSqrt ‖q‖) = 2 * Real.pi / 3 := by
  rw [MeasureTheory.integral_fun_norm_addHaar (volume : Measure E2) radialSqrt]
  simp only [E2, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSubDiff,
    nsmul_eq_mul, smul_eq_mul]
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_two]
  norm_num
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi)]
  rw [integral_Ioi_mul_radialSqrt]
  ring


lemma norm_sq_coords (q : E2) : ‖q‖^2 = (q 0)^2 + (q 1)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_succ]

theorem apm_t96J08_bridge_radialDiskIntegral :
    (∫ q : apm_t96j08_DiskPoint in Metric.closedBall 0 1,
      Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)) = 2 * Real.pi / 3 := by
  rw [← integral_indicator measurableSet_closedBall]
  have heq : (Metric.closedBall (0 : E2) 1).indicator
      (fun q => Real.sqrt (1-(q 0)^2-(q 1)^2)) = (fun q : E2 => radialSqrt ‖q‖) := by
    funext q
    by_cases hq : q ∈ Metric.closedBall (0 : E2) 1
    · rw [indicator_of_mem hq, radialSqrt, norm_sq_coords]
      congr 1; ring
    · rw [indicator_of_notMem hq, radialSqrt_eq_zero_of_one_le]
      simp only [Metric.mem_closedBall, dist_zero_right] at hq
      exact (lt_of_not_ge hq).le
  rw [heq, integral_radialSqrt_euclidean]

lemma diagnostic_direction (a : apm_t96j08_Point → ℝ) (x w : apm_t96j08_Point)
    (c : ℝ) (ha : DifferentiableAt ℝ a x)
    (hline : ∀ t : ℝ, a (x + t • w) = a x + c * t) :
    fderiv ℝ a x w = c := by
  have hpath : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
    simpa only [Pi.add_apply, id_eq, zero_add, one_smul] using (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const w)
  have ha' : HasFDerivAt a (fderiv ℝ a x) (x + (0 : ℝ) • w) := by
    simpa using ha.hasFDerivAt
  have hd := ha'.comp_hasDerivAt 0 hpath
  have he : (fun t : ℝ => a (x + t • w)) = fun t => a x + c * t := funext hline
  change HasDerivAt (fun t : ℝ => a (x + t • w)) (fderiv ℝ a x w) 0 at hd
  rw [he] at hd
  have hc : HasDerivAt (fun t : ℝ => a x + c * t) c 0 := by
    simpa only [Pi.add_apply, id_eq, zero_add, mul_one] using (hasDerivAt_const (0 : ℝ) (a x)).add ((hasDerivAt_id (0 : ℝ)).const_mul c)
  exact hd.unique hc

lemma diagnostic_coordinate (j : Fin 3) : fderiv ℝ (fun y : apm_t96j08_Point => y j) 0 (EuclideanSpace.single j 1) = 1 := by
  apply diagnostic_direction
  · fun_prop
  · intro t; simp

lemma diagnostic_not_exact : ¬apm_t96j08_IsExact := by
  rintro ⟨η, hη, heval⟩
  let ω := extDeriv (apm_t96j08_etaForm η)
  have hw : ∀ p v, ω p v = apm_t96j08_omega p (v 0) (v 1) := by
    intro p v
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hv]
    exact (apm_t96j08_extDeriv_etaForm_apply η hη p (v 0) (v 1)).trans (heval p (v 0) (v 1))
  have hs : ContDiff ℝ (⊤ : ℕ∞) ω := by
    have he : ω = fun p => p 0 • ω (EuclideanSpace.single 0 1) +
        p 1 • ω (EuclideanSpace.single 1 1) + p 2 • ω (EuclideanSpace.single 2 1) := by
      funext p; ext v
      simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      rw [hw, hw, hw, hw]
      simp [apm_t96j08_omega]
    rw [he]
    fun_prop
  have hd : extDeriv ω 0 (fun i => EuclideanSpace.single i (1 : ℝ)) = 1 := by
    rw [extDeriv_apply (hs.differentiable (by simp) 0)]
    change (∑ j : Fin 3, (-1 : ℤ) ^ (j : ℕ) •
      fderiv ℝ (fun y => ω y (j.removeNth (fun i => EuclideanSpace.single i (1 : ℝ)))) 0
        (EuclideanSpace.single j 1)) = 1
    rw [Fin.sum_univ_three]
    simp_rw [show ∀ v, (fun y => ω y v) = fun y => apm_t96j08_omega y (v 0) (v 1) from fun v => funext (fun y => hw y v)]
    simp only [Fin.removeNth]
    have hfin : Fin.succAbove (2 : Fin 3) (1 : Fin 2) = 1 := rfl
    simp only [apm_t96j08_omega, hfin]
    simp
    change fderiv ℝ (fun y : apm_t96j08_Point => y 0) 0 (EuclideanSpace.single 0 1) +
      -fderiv ℝ (fun y : apm_t96j08_Point => y 1) 0 (EuclideanSpace.single 1 1) +
      fderiv ℝ (fun y : apm_t96j08_Point => y 2) 0 (EuclideanSpace.single 2 1) = 1
    rw [diagnostic_coordinate, diagnostic_coordinate, diagnostic_coordinate]
    norm_num
  have heta : ContDiff ℝ (⊤ : ℕ∞) (apm_t96j08_etaForm η) := by
    unfold apm_t96j08_etaForm
    exact (ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := apm_t96j08_Point) (F := ℝ)
      (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp hη
  have hz : extDeriv ω = 0 := extDeriv_extDeriv heta (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  rw [hz] at hd
  norm_num at hd

lemma diagnostic_singular_integrable : IntegrableOn
    (fun q : E2 => ((q 0)^2-(q 1)^2)/Real.sqrt (1-(q 0)^2-(q 1)^2))
    (Metric.closedBall 0 1) := by
  have h := ConstructionTargets.UnitDiskInverseSqrtIntegrability.integrable_radialInverseSqrt_euclidean.integrableOn
    (s := Metric.closedBall (0 : E2) 1)
  have hc : ContinuousOn (fun q : E2 => (q 0)^2-(q 1)^2) (Metric.closedBall 0 1) := by fun_prop
  have hm := h.mul_continuousOn hc (isCompact_closedBall (0 : E2) 1)
  apply hm.congr_fun _ measurableSet_closedBall
  intro q _
  simp only [ConstructionTargets.UnitDiskInverseSqrtIntegrability.radialInverseSqrt, norm_sq_coords]
  rw [show 1-((q 0)^2+(q 1)^2) = 1-(q 0)^2-(q 1)^2 by ring]
  simp [div_eq_mul_inv, mul_comm]

lemma diagnostic_hemisphere : apm_t96j08_hemisphereIntegral = 5 * Real.pi / 3 := by
  have hs : IntegrableOn (fun q : E2 => Real.sqrt (1-(q 0)^2-(q 1)^2)) (Metric.closedBall 0 1) :=
    (by fun_prop : Continuous (fun q : E2 => Real.sqrt (1-(q 0)^2-(q 1)^2))).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hc : IntegrableOn (fun _ : E2 => (1 : ℝ)) (Metric.closedBall 0 1) :=
    continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  unfold apm_t96j08_hemisphereIntegral
  simp_rw [apm_t96j08_pullback_eq]
  have hadd := integral_add (hc.add hs) diagnostic_singular_integrable
  simp only [Pi.add_apply] at hadd
  rw [hadd, integral_add hc hs,
    apm_t96J08_bridge_radialDiskIntegral, apm_t96j08_integral_singularTerm_eq_zero]
  simp only [integral_const, smul_eq_mul, mul_one, add_zero]
  rw [measureReal_def, Measure.restrict_apply_univ, EuclideanSpace.volume_closedBall_fin_two]
  norm_num
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi)]
  ring

theorem apm_t96j08 :
    ¬apm_t96j08_IsClosed ∧
    ¬apm_t96j08_IsExact ∧
    apm_t96j08_hemisphereIntegral = 5 * Real.pi / 3 := by
  exact ⟨apm_t96j08_not_isClosed, diagnostic_not_exact, diagnostic_hemisphere⟩

#print axioms apm_t96J08_bridge_radialDiskIntegral
#print axioms apm_t96j08
