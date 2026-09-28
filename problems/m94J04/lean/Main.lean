import Mathlib

/-!
# APM m94J04

## Statement repairs

The printed cases `f=y` if `x>0` and `f=x` if `z<0` overlap on
`{x>0,z<0}` and leave `{x≤0,z≥0}` undefined. Following the intended
single-interface computation, the second condition is repaired to `x≤0`.
Thus the jump is across the plane `x=0`.

## Encoding questions

The distributional identity is stated against every compactly supported smooth
vector test function on `ℝ³`. The left side is the weak curl pairing and the
right side is the regular distribution represented by `(0,0,-1_{x>0})`.
-/

open MeasureTheory
open scoped Distributions

abbrev apm_m94J04_E := EuclideanSpace ℝ (Fin 3)

/-- Coordinate vector in `ℝ³`. -/
noncomputable def apm_m94J04_basis (i : Fin 3) : apm_m94J04_E :=
  EuclideanSpace.single i 1

/-- The repaired scalar field from the problem. -/
noncomputable def apm_m94J04_f (p : apm_m94J04_E) : ℝ :=
  if 0 < p 0 then p 1 else p 0

lemma apm_m94J04_f_of_pos {p : apm_m94J04_E} (hp : 0 < p 0) :
    apm_m94J04_f p = p 1 := by
  simp [apm_m94J04_f, hp]

lemma apm_m94J04_f_of_nonpos {p : apm_m94J04_E} (hp : p 0 ≤ 0) :
    apm_m94J04_f p = p 0 := by
  simp [apm_m94J04_f, not_lt.mpr hp]

/-- The vector field `u=f e₁`. -/
noncomputable def apm_m94J04_u (p : apm_m94J04_E) : apm_m94J04_E :=
  apm_m94J04_f p • apm_m94J04_basis 0

/-- Classical curl of a smooth vector-valued test function. -/
noncomputable def apm_m94J04_curlTest
    (φ : apm_m94J04_E → apm_m94J04_E) (p : apm_m94J04_E) : apm_m94J04_E :=
  (fderiv ℝ (fun q ↦ φ q 2) p (apm_m94J04_basis 1) -
      fderiv ℝ (fun q ↦ φ q 1) p (apm_m94J04_basis 2)) • apm_m94J04_basis 0 +
  (fderiv ℝ (fun q ↦ φ q 0) p (apm_m94J04_basis 2) -
      fderiv ℝ (fun q ↦ φ q 2) p (apm_m94J04_basis 0)) • apm_m94J04_basis 1 +
  (fderiv ℝ (fun q ↦ φ q 1) p (apm_m94J04_basis 0) -
      fderiv ℝ (fun q ↦ φ q 0) p (apm_m94J04_basis 1)) • apm_m94J04_basis 2

/-- The regular field representing the claimed distributional curl. -/
noncomputable def apm_m94J04_curlValue (p : apm_m94J04_E) : apm_m94J04_E :=
  (if 0 < p 0 then (-1 : ℝ) else 0) • apm_m94J04_basis 2

/-- Coordinate reduction of the weak-curl integrand. -/
lemma apm_m94J04_inner_u_curlTest
    (φ : apm_m94J04_E → apm_m94J04_E) (p : apm_m94J04_E) :
    inner ℝ (apm_m94J04_u p) (apm_m94J04_curlTest φ p) =
      apm_m94J04_f p *
        (fderiv ℝ (fun q ↦ φ q 2) p (apm_m94J04_basis 1) -
          fderiv ℝ (fun q ↦ φ q 1) p (apm_m94J04_basis 2)) := by
  rw [apm_m94J04_u, apm_m94J04_curlTest, inner_smul_left]
  simp [apm_m94J04_basis, inner_add_right, inner_smul_right,
    PiLp.inner_apply, Fin.sum_univ_succ]

/-- Coordinate reduction of the claimed regular curl. -/
lemma apm_m94J04_inner_curlValue
    (φ : apm_m94J04_E → apm_m94J04_E) (p : apm_m94J04_E) :
    inner ℝ (apm_m94J04_curlValue p) (φ p) =
      (if 0 < p 0 then -φ p 2 else 0) := by
  have hone (x : ℝ) : inner ℝ 1 x = x := by
    rw [show x = x • (1 : ℝ) by simp, real_inner_smul_right]
    norm_num
  rw [apm_m94J04_curlValue]
  split_ifs <;>
    simp [apm_m94J04_basis, PiLp.inner_apply, Fin.sum_univ_succ, hone]

/-- Restricting a test-function coordinate to an affine coordinate line turns
the ambient `fderiv` evaluation into the ordinary one-dimensional derivative.
This is the analytic identity required after the coordinate measure split. -/
lemma apm_m94J04_slice_hasDerivAt
    (φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E)
      apm_m94J04_E ⊤)
    (p : apm_m94J04_E) (i j : Fin 3) (r : ℝ) :
    HasDerivAt (fun s : ℝ ↦ φ (p + s • apm_m94J04_basis i) j)
      (fderiv ℝ (fun q ↦ φ q j) (p + r • apm_m94J04_basis i)
        (apm_m94J04_basis i)) r := by
  have hφ : Differentiable ℝ (φ : apm_m94J04_E → apm_m94J04_E) :=
    φ.contDiff.differentiable (by simp)
  have hcoord : Differentiable ℝ (fun q : apm_m94J04_E ↦ φ q j) := by
    fun_prop
  have hline : HasDerivAt (fun s : ℝ ↦ p + s • apm_m94J04_basis i)
      (apm_m94J04_basis i) r :=
    by simpa using
      ((hasDerivAt_id r).smul_const (apm_m94J04_basis i)).const_add p
  exact hcoord.differentiableAt.hasFDerivAt.comp_hasDerivAt r hline

/-- Every affine coordinate-line parametrization is an isometry.  In
particular it is a proper embedding, which is the geometric input needed to
pull compact test-function support back to one-dimensional slices. -/
lemma apm_m94J04_sliceLine_isometry (p : apm_m94J04_E) (i : Fin 3) :
    Isometry (fun s : ℝ ↦ p + s • apm_m94J04_basis i) := by
  rw [isometry_iff_dist_eq]
  intro s t
  rw [dist_eq_norm, dist_eq_norm]
  simp only [add_sub_add_left_eq_sub, ← sub_smul]
  rw [norm_smul]
  simp [apm_m94J04_basis, Real.norm_eq_abs]

lemma apm_m94J04_integral_toLp (g : apm_m94J04_E → ℝ) :
    ∫ p, g p ∂volume = ∫ v : Fin 3 → ℝ, g (WithLp.toLp 2 v) ∂volume := by
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]

lemma apm_m94J04_integral_split_coordinate
    (g : apm_m94J04_E → ℝ) (hg : Integrable g volume) (i : Fin 3) :
    ∫ p, g p ∂volume =
      ∫ q : Fin 2 → ℝ, ∫ r : ℝ,
        g (WithLp.toLp 2 (Fin.insertNth i r q)) ∂volume ∂volume := by
  let e : ℝ × (Fin 2 → ℝ) ≃ᵐ (Fin 3 → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm
  have he : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm _
  have hraw : Integrable (fun v : Fin 3 → ℝ => g (WithLp.toLp 2 v)) volume := by
    simpa only [Function.comp_apply] using
      ((PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
        (MeasurableEquiv.toLp 2 _).measurableEmbedding).2 hg
  calc
    ∫ p, g p ∂volume = ∫ v : Fin 3 → ℝ, g (WithLp.toLp 2 v) ∂volume :=
      apm_m94J04_integral_toLp g
    _ = ∫ z : ℝ × (Fin 2 → ℝ), g (WithLp.toLp 2 (e z)) ∂volume :=
      (he.integral_comp' (fun v : Fin 3 → ℝ => g (WithLp.toLp 2 v))).symm
    _ = ∫ q : Fin 2 → ℝ, ∫ r : ℝ,
        g (WithLp.toLp 2 (Fin.insertNth i r q)) ∂volume ∂volume := by
      rw [Measure.volume_eq_prod, integral_prod_symm]
      · simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
        rfl
      · exact (he.integrable_comp_emb e.measurableEmbedding).2 hraw

lemma apm_m94J04_component_integrable
    (φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E)
      apm_m94J04_E ⊤) (j : Fin 3) :
    Integrable (fun p => φ p j) volume := by
  apply Continuous.integrable_of_hasCompactSupport
  · fun_prop
  · simpa only [Function.comp_apply] using
      φ.hasCompactSupport.comp_left (g := fun v : apm_m94J04_E => v j) (by simp)

lemma apm_m94J04_directionalDerivative_integrable
    (φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E)
      apm_m94J04_E ⊤) (i j : Fin 3) :
    Integrable
      (fun p => fderiv ℝ (fun q => φ q j) p (apm_m94J04_basis i)) volume := by
  have hcont : Continuous
      (fun p => fderiv ℝ (fun q => φ q j) p (apm_m94J04_basis i)) := by
    have hφ := φ.contDiff
    have hφ' : ContDiff ℝ 1
        (φ : apm_m94J04_E → apm_m94J04_E) := hφ.of_le (by simp)
    have hcd : ContDiff ℝ 1
        (fun q : apm_m94J04_E => φ q j) := by
      fun_prop
    have hd := (hcd.fderiv_right (m := 0) (by norm_num)).continuous
    simpa only [ContinuousLinearMap.apply_apply] using
      (((ContinuousLinearMap.apply ℝ ℝ) (apm_m94J04_basis i)).continuous.comp hd)
  apply hcont.integrable_of_hasCompactSupport
  have hs : HasCompactSupport (fun q : apm_m94J04_E => φ q j) := by
    simpa only [Function.comp_apply] using
      φ.hasCompactSupport.comp_left (g := fun v : apm_m94J04_E => v j) (by simp)
  exact hs.fderiv_apply ℝ (apm_m94J04_basis i)

lemma apm_m94J04_slice_hasCompactSupport
    (φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E)
      apm_m94J04_E ⊤)
    (p : apm_m94J04_E) (i j : Fin 3) :
    HasCompactSupport (fun s : ℝ => φ (p + s • apm_m94J04_basis i) j) := by
  let line : ℝ → apm_m94J04_E := fun s => p + s • apm_m94J04_basis i
  have hproper : IsProperMap line :=
    (apm_m94J04_sliceLine_isometry p i).isClosedEmbedding.isProperMap
  let K : Set ℝ := line ⁻¹' tsupport (φ : apm_m94J04_E → apm_m94J04_E)
  apply HasCompactSupport.intro (K := K)
  · exact hproper.isCompact_preimage φ.hasCompactSupport.isCompact
  · intro s hs
    have hnmem : line s ∉ Function.support
        (φ : apm_m94J04_E → apm_m94J04_E) := by
      intro hm
      exact hs (subset_tsupport _ hm)
    have hz : φ (line s) = 0 := by
      simpa only [Function.mem_support, not_not] using hnmem
    simpa [line] using congrArg (fun v : apm_m94J04_E => v j) hz

lemma apm_m94J04_slice_contDiff_one
    (φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E)
      apm_m94J04_E ⊤)
    (p : apm_m94J04_E) (i j : Fin 3) :
    ContDiff ℝ 1 (fun s : ℝ => φ (p + s • apm_m94J04_basis i) j) := by
  have hφ : ContDiff ℝ 1
      (φ : apm_m94J04_E → apm_m94J04_E) := φ.contDiff.of_le (by simp)
  fun_prop

lemma apm_m94J04_integral_id_mul_fderiv
    (h : ℝ → ℝ) (hcd : ContDiff ℝ 1 h) (hcs : HasCompactSupport h) :
    ∫ r, r * fderiv ℝ h r 1 ∂volume = -∫ r, h r ∂volume := by
  have hh : Integrable h volume :=
    hcd.continuous.integrable_of_hasCompactSupport hcs
  have hdcont : Continuous (fun r => fderiv ℝ h r 1) := by
    have hd := (hcd.fderiv_right (m := 0) (by norm_num)).continuous
    simpa only [ContinuousLinearMap.one_apply] using
      (((ContinuousLinearMap.apply ℝ ℝ) 1).continuous.comp hd)
  have hdcs : HasCompactSupport (fun r => fderiv ℝ h r 1) :=
    hcs.fderiv_apply ℝ 1
  have hderiv : Integrable (fun r => fderiv ℝ h r 1) volume :=
    hdcont.integrable_of_hasCompactSupport hdcs
  have hidderiv : Integrable (fun r => r * fderiv ℝ h r 1) volume := by
    apply (continuous_id.mul hdcont).integrable_of_hasCompactSupport
    exact hdcs.mul_left
  have hidh : Integrable (fun r => r * h r) volume := by
    apply (continuous_id.mul hcd.continuous).integrable_of_hasCompactSupport
    exact hcs.mul_left
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun r : ℝ => r) (g := h) (v := (1 : ℝ))
    (by simpa using hh) hidderiv hidh
    (fun _ _ => differentiableAt_id) (fun _ _ => hcd.differentiable (by norm_num) |>.differentiableAt)
  simpa using hibp

lemma apm_m94J04_integral_fderiv_eq_zero
    (h : ℝ → ℝ) (hcd : ContDiff ℝ 1 h) (hcs : HasCompactSupport h) :
    ∫ r, fderiv ℝ h r 1 ∂volume = 0 := by
  have hh : Integrable h volume :=
    hcd.continuous.integrable_of_hasCompactSupport hcs
  have hdcont : Continuous (fun r => fderiv ℝ h r 1) := by
    have hd := (hcd.fderiv_right (m := 0) (by norm_num)).continuous
    simpa only [ContinuousLinearMap.one_apply] using
      (((ContinuousLinearMap.apply ℝ ℝ) 1).continuous.comp hd)
  have hdcs : HasCompactSupport (fun r => fderiv ℝ h r 1) :=
    hcs.fderiv_apply ℝ 1
  have hderiv : Integrable (fun r => fderiv ℝ h r 1) volume :=
    hdcont.integrable_of_hasCompactSupport hdcs
  have honeh : Integrable (fun r : ℝ => (1 : ℝ) * h r) volume := by simpa using hh
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : ℝ => (1 : ℝ)) (g := h) (v := (1 : ℝ))
    (by simpa using hh) (by simpa using hderiv) honeh
    (fun _ _ => differentiableAt_const (c := (1 : ℝ)))
    (fun _ _ => hcd.differentiable (by norm_num) |>.differentiableAt)
  simpa using hibp

lemma apm_m94J04_toLp_insertNth_eq_line
    (i : Fin 3) (q : Fin 2 → ℝ) (r : ℝ) :
    WithLp.toLp 2 (Fin.insertNth i r q) =
      WithLp.toLp 2 (Fin.insertNth i 0 q) + r • apm_m94J04_basis i := by
  apply PiLp.ext
  intro j
  by_cases hji : j = i
  · subst j
    simp [apm_m94J04_basis]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    simp [apm_m94J04_basis, Fin.succAbove_ne]

lemma apm_m94J04_insertNth_fderiv
    (φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E)
      apm_m94J04_E ⊤)
    (i j : Fin 3) (q : Fin 2 → ℝ) (r : ℝ) :
    fderiv ℝ (fun s : ℝ => φ (WithLp.toLp 2 (Fin.insertNth i s q)) j) r 1 =
      fderiv ℝ (fun p => φ p j) (WithLp.toLp 2 (Fin.insertNth i r q))
        (apm_m94J04_basis i) := by
  let p : apm_m94J04_E := WithLp.toLp 2 (Fin.insertNth i 0 q)
  have heq : (fun s : ℝ => φ (WithLp.toLp 2 (Fin.insertNth i s q)) j) =
      (fun s : ℝ => φ (p + s • apm_m94J04_basis i) j) := by
    funext s
    rw [apm_m94J04_toLp_insertNth_eq_line]
  rw [heq, fderiv_apply_one_eq_deriv]
  have hd := (apm_m94J04_slice_hasDerivAt φ p i j r).deriv
  have hp : p + r • apm_m94J04_basis i =
      WithLp.toLp 2 (Fin.insertNth i r q) := by
    exact (apm_m94J04_toLp_insertNth_eq_line i q r).symm
  rw [hp] at hd
  exact hd

lemma apm_m94J04_insertNth_slice_contDiff_one
    (φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E)
      apm_m94J04_E ⊤) (i j : Fin 3) (q : Fin 2 → ℝ) :
    ContDiff ℝ 1 (fun s : ℝ => φ (WithLp.toLp 2 (Fin.insertNth i s q)) j) := by
  let p : apm_m94J04_E := WithLp.toLp 2 (Fin.insertNth i 0 q)
  have heq : (fun s : ℝ => φ (WithLp.toLp 2 (Fin.insertNth i s q)) j) =
      (fun s : ℝ => φ (p + s • apm_m94J04_basis i) j) := by
    funext s
    rw [apm_m94J04_toLp_insertNth_eq_line]
  rw [heq]
  exact apm_m94J04_slice_contDiff_one φ p i j

lemma apm_m94J04_insertNth_slice_hasCompactSupport
    (φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E)
      apm_m94J04_E ⊤) (i j : Fin 3) (q : Fin 2 → ℝ) :
    HasCompactSupport
      (fun s : ℝ => φ (WithLp.toLp 2 (Fin.insertNth i s q)) j) := by
  let p : apm_m94J04_E := WithLp.toLp 2 (Fin.insertNth i 0 q)
  have heq : (fun s : ℝ => φ (WithLp.toLp 2 (Fin.insertNth i s q)) j) =
      (fun s : ℝ => φ (p + s • apm_m94J04_basis i) j) := by
    funext s
    rw [apm_m94J04_toLp_insertNth_eq_line]
  rw [heq]
  exact apm_m94J04_slice_hasCompactSupport φ p i j

lemma apm_m94J04_insertNth_integral_id_mul_directionalDerivative
    (φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E)
      apm_m94J04_E ⊤) (i j : Fin 3) (q : Fin 2 → ℝ) :
    ∫ r : ℝ, r *
        fderiv ℝ (fun p => φ p j) (WithLp.toLp 2 (Fin.insertNth i r q))
          (apm_m94J04_basis i) ∂volume =
      -∫ r : ℝ, φ (WithLp.toLp 2 (Fin.insertNth i r q)) j ∂volume := by
  simp_rw [← apm_m94J04_insertNth_fderiv φ i j q]
  exact apm_m94J04_integral_id_mul_fderiv _
    (apm_m94J04_insertNth_slice_contDiff_one φ i j q)
    (apm_m94J04_insertNth_slice_hasCompactSupport φ i j q)

lemma apm_m94J04_insertNth_integral_directionalDerivative_eq_zero
    (φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E)
      apm_m94J04_E ⊤) (i j : Fin 3) (q : Fin 2 → ℝ) :
    ∫ r : ℝ,
        fderiv ℝ (fun p => φ p j) (WithLp.toLp 2 (Fin.insertNth i r q))
          (apm_m94J04_basis i) ∂volume = 0 := by
  simp_rw [← apm_m94J04_insertNth_fderiv φ i j q]
  exact apm_m94J04_integral_fderiv_eq_zero _
    (apm_m94J04_insertNth_slice_contDiff_one φ i j q)
    (apm_m94J04_insertNth_slice_hasCompactSupport φ i j q)

lemma apm_m94J04_norm_f_le (p : apm_m94J04_E) :
    ‖apm_m94J04_f p‖ ≤ ‖p‖ := by
  unfold apm_m94J04_f
  split_ifs
  · exact PiLp.norm_apply_le p 1
  · exact PiLp.norm_apply_le p 0

lemma apm_m94J04_f_aestronglyMeasurable :
    AEStronglyMeasurable apm_m94J04_f volume := by
  apply Measurable.aestronglyMeasurable
  unfold apm_m94J04_f
  apply Measurable.ite
  · exact measurableSet_lt measurable_const (by fun_prop)
  · fun_prop
  · fun_prop

lemma apm_m94J04_f_mul_directionalDerivative_integrable
    (φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E)
      apm_m94J04_E ⊤) (i j : Fin 3) :
    Integrable (fun p => apm_m94J04_f p *
      fderiv ℝ (fun q => φ q j) p (apm_m94J04_basis i)) volume := by
  let d : apm_m94J04_E → ℝ := fun p =>
    fderiv ℝ (fun q => φ q j) p (apm_m94J04_basis i)
  have hdint : Integrable d volume :=
    apm_m94J04_directionalDerivative_integrable φ i j
  have hcoordcs : HasCompactSupport (fun q : apm_m94J04_E => φ q j) := by
    simpa only [Function.comp_apply] using
      φ.hasCompactSupport.comp_left (g := fun v : apm_m94J04_E => v j) (by simp)
  have hdcs : HasCompactSupport d :=
    hcoordcs.fderiv_apply ℝ (apm_m94J04_basis i)
  rcases hdcs.isCompact.isBounded.subset_closedBall 0 with ⟨R, hR⟩
  apply Integrable.mono' (hdint.norm.const_mul R)
  · exact apm_m94J04_f_aestronglyMeasurable.mul hdint.aestronglyMeasurable
  · filter_upwards [] with p
    by_cases hp : p ∈ tsupport d
    · have hpR : ‖p‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hR hp
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul
        ((apm_m94J04_norm_f_le p).trans hpR) le_rfl (norm_nonneg _)
          ((norm_nonneg p).trans hpR)
    · have hdp : d p = 0 := by
        by_contra hn
        exact hp (subset_tsupport d hn)
      simp [d, hdp]

lemma apm_m94J04_curlRhs_integrable
    (φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E)
      apm_m94J04_E ⊤) :
    Integrable (fun p => if 0 < p 0 then -φ p 2 else 0) volume := by
  apply Integrable.mono' (apm_m94J04_component_integrable φ 2).norm
  · apply Measurable.aestronglyMeasurable
    apply Measurable.ite
    · exact measurableSet_lt measurable_const (by fun_prop)
    · fun_prop
    · fun_prop
  · filter_upwards [] with p
    split_ifs <;> simp

/-- Why this unblocks `apm_m94j04`: after the two compiled coordinate-inner-
product reductions, this is exactly the remaining scalar equality.  Its proof
is the missing Euclidean-volume coordinate transport, Fubini decomposition,
and compactly-supported one-dimensional integration by parts. -/
theorem apm_m94J04_bridge_1
    (φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E)
      apm_m94J04_E ⊤) :
    ∫ p, apm_m94J04_f p *
        (fderiv ℝ (fun q ↦ φ q 2) p (apm_m94J04_basis 1) -
          fderiv ℝ (fun q ↦ φ q 1) p (apm_m94J04_basis 2)) ∂volume =
      ∫ p, (if 0 < p 0 then -φ p 2 else 0) ∂volume := by
  let A : apm_m94J04_E → ℝ := fun p => apm_m94J04_f p *
    fderiv ℝ (fun q => φ q 2) p (apm_m94J04_basis 1)
  let B : apm_m94J04_E → ℝ := fun p => apm_m94J04_f p *
    fderiv ℝ (fun q => φ q 1) p (apm_m94J04_basis 2)
  let R : apm_m94J04_E → ℝ := fun p => if 0 < p 0 then -φ p 2 else 0
  have hA : Integrable A volume :=
    apm_m94J04_f_mul_directionalDerivative_integrable φ 1 2
  have hB : Integrable B volume :=
    apm_m94J04_f_mul_directionalDerivative_integrable φ 2 1
  have hR : Integrable R volume := apm_m94J04_curlRhs_integrable φ
  have hBfiber (q : Fin 2 → ℝ) :
      ∫ r : ℝ, B (WithLp.toLp 2 (Fin.insertNth (2 : Fin 3) r q)) ∂volume = 0 := by
    have hf (r : ℝ) :
        apm_m94J04_f (WithLp.toLp 2 (Fin.insertNth (2 : Fin 3) r q)) =
          apm_m94J04_f (WithLp.toLp 2 (Fin.insertNth (2 : Fin 3) 0 q)) := by
      rw [apm_m94J04_toLp_insertNth_eq_line]
      simp [apm_m94J04_f, apm_m94J04_basis]
    simp_rw [B, hf]
    rw [integral_const_mul]
    simp [apm_m94J04_insertNth_integral_directionalDerivative_eq_zero φ 2 1 q]
  have hAfiber (q : Fin 2 → ℝ) :
      ∫ r : ℝ, A (WithLp.toLp 2 (Fin.insertNth (1 : Fin 3) r q)) ∂volume =
        ∫ r : ℝ, R (WithLp.toLp 2 (Fin.insertNth (1 : Fin 3) r q)) ∂volume := by
    let p₀ : apm_m94J04_E := WithLp.toLp 2 (Fin.insertNth (1 : Fin 3) 0 q)
    by_cases hx : 0 < p₀ 0
    · have hf (r : ℝ) :
          apm_m94J04_f (WithLp.toLp 2 (Fin.insertNth (1 : Fin 3) r q)) = r := by
        rw [apm_m94J04_toLp_insertNth_eq_line]
        simp [apm_m94J04_f, apm_m94J04_basis, hx, p₀]
      have hRv (r : ℝ) :
          R (WithLp.toLp 2 (Fin.insertNth (1 : Fin 3) r q)) =
            -φ (WithLp.toLp 2 (Fin.insertNth (1 : Fin 3) r q)) 2 := by
        rw [apm_m94J04_toLp_insertNth_eq_line]
        simp [R, apm_m94J04_basis, hx, p₀]
      simp_rw [A, hf, hRv]
      rw [integral_neg]
      exact apm_m94J04_insertNth_integral_id_mul_directionalDerivative φ 1 2 q
    · have hf (r : ℝ) :
          apm_m94J04_f (WithLp.toLp 2 (Fin.insertNth (1 : Fin 3) r q)) = p₀ 0 := by
        rw [apm_m94J04_toLp_insertNth_eq_line]
        simp [apm_m94J04_f, apm_m94J04_basis, hx, p₀]
      have hRv (r : ℝ) :
          R (WithLp.toLp 2 (Fin.insertNth (1 : Fin 3) r q)) = 0 := by
        rw [apm_m94J04_toLp_insertNth_eq_line]
        simp [R, apm_m94J04_basis, hx, p₀]
      simp_rw [A, hf, hRv]
      rw [integral_const_mul]
      simp [apm_m94J04_insertNth_integral_directionalDerivative_eq_zero φ 1 2 q]
  rw [show (fun p => apm_m94J04_f p *
      (fderiv ℝ (fun q ↦ φ q 2) p (apm_m94J04_basis 1) -
        fderiv ℝ (fun q ↦ φ q 1) p (apm_m94J04_basis 2))) =
      (fun p => A p - B p) by funext p; simp [A, B, mul_sub]]
  change ∫ p, A p - B p ∂volume = ∫ p, R p ∂volume
  rw [integral_sub hA hB, apm_m94J04_integral_split_coordinate A hA 1,
    apm_m94J04_integral_split_coordinate B hB 2,
    apm_m94J04_integral_split_coordinate R hR 1]
  simp_rw [hBfiber, integral_zero, sub_zero, hAfiber]

theorem apm_m94j04 :
    ∀ φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E)
      apm_m94J04_E ⊤,
      ∫ p, inner ℝ (apm_m94J04_u p) (apm_m94J04_curlTest φ p) ∂volume =
        ∫ p, inner ℝ (apm_m94J04_curlValue p) (φ p) ∂volume := by
  intro φ
  simp_rw [apm_m94J04_inner_u_curlTest, apm_m94J04_inner_curlValue]
  /-
  PASS-1 boundary (Codex): the Euclidean basis and inner-product algebra is
  now completely discharged by the two proved helpers above. The remaining
  scalar identity is fiberwise `∫ y * ∂y φ₂ = -∫ φ₂` on `x > 0`, together
  with `∫ x * ∂y φ₂ = 0` and the analogous z-derivative integral on `x ≤ 0`.

  APIs searched: `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`,
  `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`, `integral_prod`,
  `volume_pi`, `MeasurePreserving.piFinSuccAbove`, and the one-dimensional
  `intervalIntegral.integral_deriv_of_contDiffOn_Icc`. The global
  line-derivative integration-by-parts lemmas have differentiability
  hypotheses on `tsupport` in the whole ambient
  space, so they cannot be applied directly to the coefficient
  `if 0 < x then y else x`, which is not differentiable on `x = 0`.

  `TestFunction.contDiff`, `TestFunction.hasCompactSupport`, and
  `Continuous.integrable_of_hasCompactSupport` provide the local smoothness
  and integrability ingredients. I additionally searched `LEMMA-INDEX.md`
  (1037 indexed helpers) and all 170 currently closed artifacts. The nearest
  Fubini examples (`a94J04`, `a02J01`, and
  `ConstructionTargets.YoungConvolution`) establish product-integral patterns,
  but none transports Euclidean `volume` through the coordinate split while
  identifying the slice derivative. The unresolved bridge is therefore to use
  `volume_pi`, split `Fin 3` around coordinate 1 (and coordinate 2), transport
  compact support and `fderiv` to each real slice, apply one-dimensional
  integration by parts, and reassemble with `MeasureTheory.integral_prod`.

  Closer hop 1 proves the coefficient branch normal forms
  `apm_m94J04_f_of_pos` and `apm_m94J04_f_of_nonpos`. A renewed source search
  finds `EuclideanSpace.volume_preserving_measurableEquiv_toLp` (used in
  solved artifact `a01A01`) as the missing first transport from the `WithLp`
  Euclidean representation to the raw coordinate function space. After that,
  `MeasurePreserving.piFinSuccAbove` and `volume_pi` can isolate a coordinate.
  The general `MeasureTheory.Integral.DivergenceTheorem` was inspected but is
  not directly applicable because the scalar coefficient is discontinuous at
  `x = 0`; the line-derivative integration-by-parts theorem has the same
  ambient differentiability obstruction.

  No `LEMMA-INDEX.md`, `ConstructionTargets/`, sibling, or git-history result
  packages the composite `WithLp → Pi → coordinate × complement` measure
  equivalence together with the sliced `fderiv` identity. That transport and
  its compact-support/integrability consequences remain the precise live
  bridge. The frozen statement was left unchanged.

  CLOSER HOP 2 (partial). The sliced derivative identity is now fully compiled
  as `apm_m94J04_slice_hasDerivAt`. For every test function, base point,
  coordinate direction, component, and real line parameter, it proves that
  the ordinary derivative of
  `s ↦ φ (p + s • eᵢ) j` is exactly
  `fderiv ℝ (fun q ↦ φ q j) (p + r • eᵢ) eᵢ`. The proof extracts global
  differentiability from `TestFunction.contDiff`, composes it with the affine
  line's explicit derivative, and therefore closes the analytic identification
  that hop 1 left inside the coordinate transport.

  A renewed inspection of `MeasureTheory.Integral.Pi`, the torus-integral use
  of `volume_preserving_piFinSuccAbove`, `a01A01`, `a94J04`, `a02J01`, and the
  divergence-theorem source found no packaged theorem simultaneously
  transporting the compact support of these affine slices and rewriting the
  Euclidean integral. The remaining bridge is now measure-theoretic: compose
  `volume_preserving_measurableEquiv_toLp` with the coordinate split, derive
  compact support/integrability for almost every slice, apply one-dimensional
  integration by parts using the compiled derivative identity, and reassemble
  by Fubini. The frozen statement remains unchanged.

  Closer hop 3 goes beyond the analytic slice identity by proving
  `apm_m94J04_sliceLine_isometry`: every affine coordinate slice is an
  isometric embedding of `ℝ` into `ℝ³`. This isolates the compact-support
  transport as a compact-preimage consequence of properness, rather than a
  coordinate norm estimate that must be reproved for each slice. A renewed
  search of proper-map/compact-support and product-integral APIs found no
  theorem combining that pullback with the two successive volume-preserving
  coordinate equivalences and Fubini. Those measure transports and the final
  one-dimensional integration-by-parts assembly remain open without adding
  an unproved assertion.
  -/
  exact apm_m94J04_bridge_1 φ
