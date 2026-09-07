import Mathlib

/-!
# APM m02A03 — logarithmic fundamental solution in the Euclidean plane

The plane is encoded as `EuclideanSpace ℝ (Fin 2)`.  Thus the norm in the
logarithmic kernel is the Euclidean norm, while the Laplacian is the sum of
the two second coordinate derivatives.

## Statement repairs

The former encoding used `ℝ × ℝ`, whose Mathlib product norm is the sup norm.
It has been replaced by `EuclideanSpace ℝ (Fin 2)`, as required for the
two-dimensional Newtonian potential.

The printed Laplacian contains the typographical fragment `∂²_{x₁} += ∂²_{x₂}`;
this is read as the sum of the two second partial derivatives.

## Encoding questions

None.
-/

open MeasureTheory

abbrev APMM02A03Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def apm_m02a03_kernel
    (y x : APMM02A03Plane) : ℝ :=
  (1 / (2 * Real.pi)) * Real.log ‖x - y‖

noncomputable def apm_m02a03_laplacian
    (φ : APMM02A03Plane → ℝ) (x : APMM02A03Plane) : ℝ :=
  ∑ i : Fin 2,
    deriv
      (fun t => deriv
        (fun s => φ (x + (s - x i) • EuclideanSpace.single i 1)) t)
      (x i)

lemma apm_m02a03_hasDerivAt_coordinateLine
    (φ : APMM02A03Plane → ℝ) (hφ : Differentiable ℝ φ)
    (x : APMM02A03Plane) (i : Fin 2) (t : ℝ) :
    HasDerivAt
      (fun s => φ (x + (s - x i) • EuclideanSpace.single i 1))
      (fderiv ℝ φ (x + (t - x i) • EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1)) t := by
  have hline : HasDerivAt
      (fun s : ℝ => x + (s - x i) • EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) t := by
    convert (hasDerivAt_const t x).add
      ((hasDerivAt_id t).sub_const (x i) |>.smul_const
        (EuclideanSpace.single i 1)) using 1
    all_goals simp
  simpa [Function.comp_def] using
    hφ.differentiableAt.hasFDerivAt.comp_hasDerivAt t hline

lemma apm_m02a03_deriv_coordinateLine
    (φ : APMM02A03Plane → ℝ) (hφ : Differentiable ℝ φ)
    (x : APMM02A03Plane) (i : Fin 2) (t : ℝ) :
    deriv (fun s => φ (x + (s - x i) • EuclideanSpace.single i 1)) t =
      fderiv ℝ φ (x + (t - x i) • EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1) :=
  (apm_m02a03_hasDerivAt_coordinateLine φ hφ x i t).deriv

lemma apm_m02a03_first_coordinate_deriv_at
    (φ : APMM02A03Plane → ℝ) (hφ : Differentiable ℝ φ)
    (x : APMM02A03Plane) (i : Fin 2) :
    deriv (fun s => φ (x + (s - x i) • EuclideanSpace.single i 1)) (x i) =
      fderiv ℝ φ x (EuclideanSpace.single i 1) := by
  simpa using apm_m02a03_deriv_coordinateLine φ hφ x i (x i)

lemma apm_m02a03_second_coordinate_deriv_at
    (φ : APMM02A03Plane → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (x : APMM02A03Plane) (i : Fin 2) :
    deriv
      (fun t => deriv
        (fun s => φ (x + (s - x i) • EuclideanSpace.single i 1)) t)
      (x i) =
      fderiv ℝ
        (fun q => fderiv ℝ φ q (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
  have hφdiff : Differentiable ℝ φ :=
    (contDiff_infty_iff_fderiv.mp hφ).1
  rw [show (fun t => deriv
      (fun s => φ (x + (s - x i) • EuclideanSpace.single i 1)) t) =
      (fun t => fderiv ℝ φ
        (x + (t - x i) • EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1)) by
    funext t
    exact apm_m02a03_deriv_coordinateLine φ hφdiff x i t]
  let D : APMM02A03Plane → ℝ :=
    fun q => fderiv ℝ φ q (EuclideanSpace.single i 1)
  have hfderivDiff : Differentiable ℝ (fderiv ℝ φ) :=
    (contDiff_infty_iff_fderiv.mp hφ).2.differentiable (by simp)
  have hDdiff : Differentiable ℝ D := by
    exact hfderivDiff.clm_apply (differentiable_const _)
  simpa [D] using apm_m02a03_first_coordinate_deriv_at D hDdiff x i

lemma apm_m02a03_second_coordinate_eq_iteratedFDeriv
    (φ : APMM02A03Plane → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (x : APMM02A03Plane) (i : Fin 2) :
    deriv
      (fun t => deriv
        (fun s => φ (x + (s - x i) • EuclideanSpace.single i 1)) t)
      (x i) =
      iteratedFDeriv ℝ 2 φ x
        ![EuclideanSpace.single i 1, EuclideanSpace.single i 1] := by
  rw [apm_m02a03_second_coordinate_deriv_at φ hφ x i]
  have hfderivDiff : Differentiable ℝ (fderiv ℝ φ) :=
    (contDiff_infty_iff_fderiv.mp hφ).2.differentiable (by simp)
  rw [fderiv_clm_apply hfderivDiff.differentiableAt
    (differentiable_const _).differentiableAt]
  simp [iteratedFDeriv_two_apply]

lemma apm_m02a03_laplacian_eq_mathlib
    (φ : APMM02A03Plane → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (x : APMM02A03Plane) :
    apm_m02a03_laplacian φ x = Laplacian.laplacian φ x := by
  calc
    apm_m02a03_laplacian φ x =
        ∑ i : Fin 2, iteratedFDeriv ℝ 2 φ x
          ![(EuclideanSpace.basisFun (Fin 2) ℝ) i,
            (EuclideanSpace.basisFun (Fin 2) ℝ) i] := by
      rw [apm_m02a03_laplacian]
      apply Finset.sum_congr rfl
      intro i _
      rw [apm_m02a03_second_coordinate_eq_iteratedFDeriv φ hφ x i]
      congr 1
      funext j
      fin_cases j <;> simp
    _ = Laplacian.laplacian φ x :=
      (congrFun
        (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
          (EuclideanSpace.basisFun (Fin 2) ℝ)) x).symm

/-- The only singularity of the planar logarithmic kernel is mild enough for
local integration.  This is the scalar analytic input needed before the
distributional Green identity. -/
lemma apm_m02a03_log_norm_locallyIntegrable :
    LocallyIntegrable
      (fun x : APMM02A03Plane => Real.log ‖x‖) volume := by
  rw [MeasureTheory.locallyIntegrable_iff]
  intro K hK
  obtain ⟨r, hKr⟩ := (Metric.isBounded_iff_subset_ball 0).mp hK.isBounded
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_right r 1)
  have hKR : K ⊆ Metric.ball 0 R :=
    hKr.trans (Metric.ball_subset_ball (le_max_left r 1))
  let g : ℝ → ℝ := fun r => if r < R then Real.log r else 0
  have hg : Integrable (fun x : APMM02A03Plane => g ‖x‖) volume := by
    rw [MeasureTheory.integrable_fun_norm_addHaar]
    simp only [APMM02A03Plane, finrank_euclideanSpace, Fintype.card_fin,
      Nat.reduceSubDiff, smul_eq_mul]
    have hlog : IntervalIntegrable (fun r : ℝ => r * Real.log r) volume 0 R :=
      (intervalIntegral.intervalIntegrable_log' (a := 0) (b := R)).continuousOn_mul
        continuousOn_id
    have hIoc : IntegrableOn (fun r : ℝ => r * Real.log r) (Set.Ioc 0 R) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mp hlog
    have hIoo : IntegrableOn (fun r : ℝ => r * Real.log r) (Set.Ioo 0 R) :=
      hIoc.mono_set Set.Ioo_subset_Ioc_self
    have hind : Integrable
        ((Set.Ioo 0 R).indicator (fun r => r * Real.log r)) :=
      hIoo.integrable_indicator measurableSet_Ioo
    refine (hind.restrict).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    by_cases hrR : r < R
    · simp [g, hr0, hrR]
    · simp [g, hr0, hrR]
  rw [IntegrableOn]
  refine hg.restrict.congr ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  have hxR : ‖x‖ < R := by simpa [Metric.mem_ball] using hKR hx
  simp [g, hxR]

lemma apm_m02a03_kernel_locallyIntegrable (y : APMM02A03Plane) :
    LocallyIntegrable (apm_m02a03_kernel y) volume := by
  have hshift : LocallyIntegrable
      (fun x : APMM02A03Plane => Real.log ‖x - y‖) volume := by
    let e : APMM02A03Plane ≃ₜ APMM02A03Plane := Homeomorph.addRight (-y)
    have hm : Measure.map e volume = volume := by
      simpa [e] using (map_add_right_eq_self volume (-y))
    have h := (locallyIntegrable_map_homeomorph e).mp
      (show LocallyIntegrable (fun x : APMM02A03Plane => Real.log ‖x‖)
          (Measure.map e volume) by simpa [hm] using apm_m02a03_log_norm_locallyIntegrable)
    simpa [e, sub_eq_add_neg, Function.comp_def] using h
  convert hshift.smul (1 / (2 * Real.pi)) using 1

/-- Multiplication by a continuous compactly supported test quantity turns
the locally integrable kernel into an integrable function.  In particular,
once continuity and support transport for the encoded Laplacian are exposed,
the integral in the theorem is a genuine Bochner integral. -/
lemma apm_m02a03_kernel_mul_integrable
    (y : APMM02A03Plane) (g : APMM02A03Plane → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => apm_m02a03_kernel y x * g x) volume := by
  apply (integrableOn_iff_integrable_of_support_subset
    (s := tsupport g) (fun x hx => subset_tsupport g (fun hzero => hx (by simp [hzero])))).mp
  exact (apm_m02a03_kernel_locallyIntegrable y).integrableOn_isCompact hgc
    |>.mul_continuousOn hg.continuousOn hgc

/-- Smooth compactly supported test functions in the frozen statement have
the canonical Schwartz-space presentation used by Mathlib's distributional
Laplacian API. -/
noncomputable def apm_m02a03_testToSchwartz
    (φ : APMM02A03Plane → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) : SchwartzMap APMM02A03Plane ℝ :=
  hφc.toSchwartzMap (hφ.of_le (by simp))

@[simp] lemma apm_m02a03_testToSchwartz_apply
    (φ : APMM02A03Plane → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) (x : APMM02A03Plane) :
    apm_m02a03_testToSchwartz φ hφ hφc x = φ x := rfl

lemma apm_m02a03_laplacian_continuous
    (φ : APMM02A03Plane → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    Continuous (apm_m02a03_laplacian φ) := by
  let ψ := apm_m02a03_testToSchwartz φ hφ hφc
  have hψ : Continuous (fun x => Laplacian.laplacian φ x) := by
    convert (Laplacian.laplacian ψ).continuous using 1
    funext x
    rw [SchwartzMap.laplacian_apply]
    rfl
  convert hψ using 1
  funext x
  exact apm_m02a03_laplacian_eq_mathlib φ hφ x

lemma apm_m02a03_laplacian_hasCompactSupport
    (φ : APMM02A03Plane → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    HasCompactSupport (apm_m02a03_laplacian φ) := by
  have hstd : HasCompactSupport (fun x => Laplacian.laplacian φ x) := by
    apply (hφc.iteratedFDeriv (𝕜 := ℝ) 2).mono
    intro x hx hzero
    apply hx
    dsimp only
    calc
      Laplacian.laplacian φ x =
          ∑ i : Fin 2, iteratedFDeriv ℝ 2 φ x
            ![(EuclideanSpace.basisFun (Fin 2) ℝ) i,
              (EuclideanSpace.basisFun (Fin 2) ℝ) i] :=
        congrFun
          (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
            (EuclideanSpace.basisFun (Fin 2) ℝ)) x
      _ = 0 := by rw [hzero]; simp
  apply hstd.mono
  intro x hx hzero
  exact hx ((apm_m02a03_laplacian_eq_mathlib φ hφ x).trans hzero)

lemma apm_m02a03_integrand_integrable
    (y : APMM02A03Plane) (φ : APMM02A03Plane → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    Integrable
      (fun x => apm_m02a03_kernel y x * apm_m02a03_laplacian φ x)
      volume :=
  apm_m02a03_kernel_mul_integrable y _
    (apm_m02a03_laplacian_continuous φ hφ hφc)
    (apm_m02a03_laplacian_hasCompactSupport φ hφ hφc)

/-- Smooth regularization of the logarithmic kernel.  Its Laplacian is the
standard approximate identity used to avoid a punctured-domain boundary. -/
noncomputable def apm_m02a03_regularizedKernel
    (ε : ℝ) (x : APMM02A03Plane) : ℝ :=
  (1 / (4 * Real.pi)) * Real.log (‖x‖ ^ 2 + ε ^ 2)

lemma apm_m02a03_regularizedKernel_contDiff
    {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (apm_m02a03_regularizedKernel ε) := by
  apply contDiff_const.mul
  apply ContDiff.log ((contDiff_norm_sq ℝ).add contDiff_const)
  intro x
  positivity

lemma apm_m02a03_regularizedKernel_tendsto
    {x : APMM02A03Plane} (hx : x ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => apm_m02a03_regularizedKernel ε x)
      (nhds 0) (nhds ((1 / (2 * Real.pi)) * Real.log ‖x‖)) := by
  have hnorm : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have harg : Filter.Tendsto (fun ε : ℝ => ‖x‖ ^ 2 + ε ^ 2)
      (nhds 0) (nhds (‖x‖ ^ 2)) := by
    have hid : Filter.Tendsto (fun ε : ℝ => ε) (nhds 0) (nhds 0) :=
      Filter.tendsto_id
    convert tendsto_const_nhds.add (hid.pow 2) using 1
    all_goals norm_num
  have hlog : Filter.Tendsto (fun ε : ℝ => Real.log (‖x‖ ^ 2 + ε ^ 2))
      (nhds 0) (nhds (Real.log (‖x‖ ^ 2))) :=
    (Real.continuousAt_log hnorm).tendsto.comp harg
  have ht := hlog.const_mul (1 / (4 * Real.pi))
  convert ht using 1
  congr 1
  rw [Real.log_pow]
  ring

lemma apm_m02a03_norm_sq_coordinateLine
    (x : APMM02A03Plane) (i : Fin 2) (s : ℝ) :
    ‖x + (s - x i) • EuclideanSpace.single i 1‖ ^ 2 =
      ‖x‖ ^ 2 - (x i) ^ 2 + s ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  fin_cases i <;> simp [Fin.sum_univ_two]
  all_goals ring

lemma apm_m02a03_regularizedKernel_coordinateLine
    (ε : ℝ) (x : APMM02A03Plane) (i : Fin 2) (s : ℝ) :
    apm_m02a03_regularizedKernel ε
        (x + (s - x i) • EuclideanSpace.single i 1) =
      (1 / (4 * Real.pi)) *
        Real.log (‖x‖ ^ 2 - (x i) ^ 2 + ε ^ 2 + s ^ 2) := by
  rw [apm_m02a03_regularizedKernel, apm_m02a03_norm_sq_coordinateLine]
  congr 2
  ring

lemma apm_m02a03_regularized_coordinate_argument_pos
    {ε : ℝ} (hε : ε ≠ 0) (x : APMM02A03Plane) (i : Fin 2) (s : ℝ) :
    0 < ‖x‖ ^ 2 - (x i) ^ 2 + ε ^ 2 + s ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  fin_cases i <;> simp [Fin.sum_univ_two]
  all_goals positivity

lemma apm_m02a03_hasDerivAt_log_quadratic
    {A c s : ℝ} (hA : 0 < A) :
    HasDerivAt (fun u => c * Real.log (A + u ^ 2))
      (c * (2 * s / (A + s ^ 2))) s := by
  have hq : HasDerivAt (fun u : ℝ => A + u ^ 2) (2 * s) s := by
    convert (hasDerivAt_const s A).add (hasDerivAt_id s |>.pow 2) using 1
    all_goals simp [id, mul_comm]
  convert HasDerivAt.const_mul c (hq.log (by positivity)) using 1

lemma apm_m02a03_hasSecondDerivAt_log_quadratic
    {A c s : ℝ} (hA : 0 < A) :
    HasDerivAt
      (fun u => deriv (fun v => c * Real.log (A + v ^ 2)) u)
      (c * (2 * (A - s ^ 2) / (A + s ^ 2) ^ 2)) s := by
  have hfirst : (fun u => deriv (fun v => c * Real.log (A + v ^ 2)) u) =
      fun u => c * (2 * u / (A + u ^ 2)) := by
    funext u
    exact (apm_m02a03_hasDerivAt_log_quadratic (c := c) (s := u) hA).deriv
  rw [hfirst]
  have hn : HasDerivAt (fun u : ℝ => 2 * u) 2 s := by
    simpa [id] using HasDerivAt.const_mul 2 (hasDerivAt_id s)
  have hd : HasDerivAt (fun u : ℝ => A + u ^ 2) (2 * s) s := by
    convert (hasDerivAt_const s A).add (hasDerivAt_id s |>.pow 2) using 1
    all_goals simp [id, mul_comm]
  convert HasDerivAt.const_mul c (hn.div hd (by positivity)) using 1
  field_simp
  ring

lemma apm_m02a03_regularizedKernel_second_coordinate
    {ε : ℝ} (hε : ε ≠ 0) (x : APMM02A03Plane) (i : Fin 2) :
    deriv
      (fun t => deriv
        (fun s => apm_m02a03_regularizedKernel ε
          (x + (s - x i) • EuclideanSpace.single i 1)) t)
      (x i) =
      (1 / (4 * Real.pi)) *
        (2 * (‖x‖ ^ 2 - 2 * (x i) ^ 2 + ε ^ 2) /
          (‖x‖ ^ 2 + ε ^ 2) ^ 2) := by
  let A := ‖x‖ ^ 2 - (x i) ^ 2 + ε ^ 2
  have hA : 0 < A := by
    simpa [A, add_assoc] using
      apm_m02a03_regularized_coordinate_argument_pos hε x i 0
  have hline :
      (fun s => apm_m02a03_regularizedKernel ε
        (x + (s - x i) • EuclideanSpace.single i 1)) =
      (fun s => (1 / (4 * Real.pi)) * Real.log (A + s ^ 2)) := by
    funext s
    simpa [A, add_assoc, add_left_comm, add_comm] using
      apm_m02a03_regularizedKernel_coordinateLine ε x i s
  rw [hline]
  convert (apm_m02a03_hasSecondDerivAt_log_quadratic
    (A := A) (c := 1 / (4 * Real.pi)) (s := x i) hA).deriv using 1 <;>
    dsimp [A] <;> congr 3 <;> ring

lemma apm_m02a03_regularizedKernel_laplacian
    {ε : ℝ} (hε : ε ≠ 0) (x : APMM02A03Plane) :
    apm_m02a03_laplacian (apm_m02a03_regularizedKernel ε) x =
      ε ^ 2 / (Real.pi * (‖x‖ ^ 2 + ε ^ 2) ^ 2) := by
  rw [apm_m02a03_laplacian]
  simp_rw [apm_m02a03_regularizedKernel_second_coordinate hε x]
  rw [Fin.sum_univ_two, PiLp.norm_sq_eq_of_L2]
  rw [Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

lemma apm_m02a03_contDiff_directional_fderiv
    (f : APMM02A03Plane → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : APMM02A03Plane) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => fderiv ℝ f x v) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma apm_m02a03_directional_fderiv_hasCompactSupport
    (f : APMM02A03Plane → ℝ) (hf : HasCompactSupport f)
    (v : APMM02A03Plane) :
    HasCompactSupport (fun x => fderiv ℝ f x v) := by
  apply (hf.fderiv ℝ).mono
  intro x hx hzero
  exact hx (by simpa using congrArg (fun L => L v) hzero)

lemma apm_m02a03_continuous_mul_integrable
    (f g : APMM02A03Plane → ℝ) (hf : Continuous f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => f x * g x) volume := by
  exact (hf.mul hg).integrable_of_hasCompactSupport hgc.mul_left

/-- Two integrations by parts in one coordinate.  Compact support is needed
only on the test function; the other smooth factor may grow at infinity. -/
lemma apm_m02a03_integral_mul_second_directional_eq
    (f g : APMM02A03Plane → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) (v : APMM02A03Plane) :
    (∫ x, f x * fderiv ℝ (fun q => fderiv ℝ g q v) x v) =
      ∫ x, fderiv ℝ (fun q => fderiv ℝ f q v) x v * g x := by
  let df : APMM02A03Plane → ℝ := fun x => fderiv ℝ f x v
  let dg : APMM02A03Plane → ℝ := fun x => fderiv ℝ g x v
  have hdf := apm_m02a03_contDiff_directional_fderiv f hf v
  have hdg := apm_m02a03_contDiff_directional_fderiv g hg v
  have hddf := apm_m02a03_contDiff_directional_fderiv df hdf v
  have hddg := apm_m02a03_contDiff_directional_fderiv dg hdg v
  have hdgc := apm_m02a03_directional_fderiv_hasCompactSupport g hgc v
  have hfg : Integrable (fun x => f x * g x) volume :=
    apm_m02a03_continuous_mul_integrable f g hf.continuous hg.continuous hgc
  have hfdg : Integrable (fun x => f x * dg x) volume :=
    apm_m02a03_continuous_mul_integrable f dg hf.continuous hdg.continuous hdgc
  have hdfg : Integrable (fun x => df x * g x) volume :=
    apm_m02a03_continuous_mul_integrable df g hdf.continuous hg.continuous hgc
  have hdfdg : Integrable (fun x => df x * dg x) volume :=
    apm_m02a03_continuous_mul_integrable df dg hdf.continuous hdg.continuous hdgc
  have hfddg : Integrable (fun x => f x * fderiv ℝ dg x v) volume :=
    apm_m02a03_continuous_mul_integrable f _ hf.continuous
      hddg.continuous
      (apm_m02a03_directional_fderiv_hasCompactSupport dg hdgc v)
  have hddfg : Integrable (fun x => fderiv ℝ df x v * g x) volume :=
    apm_m02a03_continuous_mul_integrable _ g
      hddf.continuous
      hg.continuous hgc
  have hfirst := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := f) (g := dg) (v := v) hdfdg hfddg hfdg
    (fun _ _ => (hf.differentiable (by simp)).differentiableAt)
    (fun _ _ => (hdg.differentiable (by simp)).differentiableAt)
  have hsecond := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := df) (g := g) (v := v) hddfg hdfdg hdfg
    (fun _ _ => (hdf.differentiable (by simp)).differentiableAt)
    (fun _ _ => (hg.differentiable (by simp)).differentiableAt)
  dsimp [df, dg] at hfirst hsecond ⊢
  rw [hfirst, hsecond]
  simp

lemma apm_m02a03_second_directional_eq_iteratedFDeriv
    (f : APMM02A03Plane → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (x v : APMM02A03Plane) :
    fderiv ℝ (fun q => fderiv ℝ f q v) x v =
      iteratedFDeriv ℝ 2 f x ![v, v] := by
  have hfd : Differentiable ℝ (fderiv ℝ f) :=
    (contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp)
  rw [fderiv_clm_apply hfd.differentiableAt
    (differentiable_const _).differentiableAt]
  simp [iteratedFDeriv_two_apply]

/-- Self-adjointness of the Laplacian when the right factor is a smooth
compactly supported test function. -/
lemma apm_m02a03_integral_mul_laplacian_eq
    (f g : APMM02A03Plane → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) :
    (∫ x, f x * apm_m02a03_laplacian g x) =
      ∫ x, apm_m02a03_laplacian f x * g x := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hleft (i : Fin 2) : Integrable
      (fun x => f x * fderiv ℝ (fun q => fderiv ℝ g q (b i)) x (b i)) volume := by
    apply apm_m02a03_continuous_mul_integrable f _ hf.continuous
    · exact (apm_m02a03_contDiff_directional_fderiv
        _ (apm_m02a03_contDiff_directional_fderiv g hg (b i)) (b i)).continuous
    · exact apm_m02a03_directional_fderiv_hasCompactSupport _
        (apm_m02a03_directional_fderiv_hasCompactSupport g hgc (b i)) (b i)
  have hright (i : Fin 2) : Integrable
      (fun x => fderiv ℝ (fun q => fderiv ℝ f q (b i)) x (b i) * g x) volume := by
    apply apm_m02a03_continuous_mul_integrable _ g
    · exact (apm_m02a03_contDiff_directional_fderiv
        _ (apm_m02a03_contDiff_directional_fderiv f hf (b i)) (b i)).continuous
    · exact hg.continuous
    · exact hgc
  calc
    (∫ x, f x * apm_m02a03_laplacian g x) =
        ∫ x, ∑ i : Fin 2,
          f x * fderiv ℝ (fun q => fderiv ℝ g q (b i)) x (b i) := by
      congr 1
      funext x
      rw [apm_m02a03_laplacian_eq_mathlib g hg x]
      calc
        f x * Laplacian.laplacian g x =
            f x * ∑ i : Fin 2, iteratedFDeriv ℝ 2 g x ![b i, b i] :=
          congrArg (fun z => f x * z)
            (congrFun
              (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g b) x)
        _ = _ := by
          simp_rw [← apm_m02a03_second_directional_eq_iteratedFDeriv g hg]
          rw [Finset.mul_sum]
    _ = ∑ i : Fin 2, ∫ x,
          f x * fderiv ℝ (fun q => fderiv ℝ g q (b i)) x (b i) := by
      exact MeasureTheory.integral_finset_sum Finset.univ
        (fun i _ => hleft i)
    _ = ∑ i : Fin 2, ∫ x,
          fderiv ℝ (fun q => fderiv ℝ f q (b i)) x (b i) * g x := by
      apply Finset.sum_congr rfl
      intro i _
      exact apm_m02a03_integral_mul_second_directional_eq f g hf hg hgc (b i)
    _ = ∫ x, ∑ i : Fin 2,
          fderiv ℝ (fun q => fderiv ℝ f q (b i)) x (b i) * g x := by
      symm
      exact MeasureTheory.integral_finset_sum Finset.univ
        (fun i _ => hright i)
    _ = ∫ x, apm_m02a03_laplacian f x * g x := by
      congr 1
      funext x
      rw [apm_m02a03_laplacian_eq_mathlib f hf x]
      calc
        (∑ i : Fin 2,
            fderiv ℝ (fun q => fderiv ℝ f q (b i)) x (b i) * g x) =
            (∑ i : Fin 2, iteratedFDeriv ℝ 2 f x ![b i, b i]) * g x := by
          simp_rw [← apm_m02a03_second_directional_eq_iteratedFDeriv f hf]
          rw [Finset.sum_mul]
        _ = Laplacian.laplacian f x * g x :=
          congrArg (fun z => z * g x)
            (congrFun
              (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f b) x).symm

lemma apm_m02a03_regularizedKernel_green_identity
    {ε : ℝ} (hε : ε ≠ 0) (φ : APMM02A03Plane → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    (∫ x, apm_m02a03_regularizedKernel ε x *
        apm_m02a03_laplacian φ x) =
      ∫ x, (ε ^ 2 / (Real.pi * (‖x‖ ^ 2 + ε ^ 2) ^ 2)) * φ x := by
  rw [apm_m02a03_integral_mul_laplacian_eq
    (apm_m02a03_regularizedKernel ε) φ
    (apm_m02a03_regularizedKernel_contDiff hε) hφ hφc]
  congr 1
  funext x
  rw [apm_m02a03_regularizedKernel_laplacian hε x]

noncomputable def apm_m02a03_regularizedKernelAt
    (ε : ℝ) (y x : APMM02A03Plane) : ℝ :=
  apm_m02a03_regularizedKernel ε (x - y)

lemma apm_m02a03_regularizedKernelAt_contDiff
    {ε : ℝ} (hε : ε ≠ 0) (y : APMM02A03Plane) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (apm_m02a03_regularizedKernelAt ε y) := by
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x => apm_m02a03_regularizedKernel ε (x - y))
  exact (apm_m02a03_regularizedKernel_contDiff hε).comp
    (contDiff_id.sub contDiff_const)

lemma apm_m02a03_regularizedKernelAt_laplacian
    {ε : ℝ} (hε : ε ≠ 0) (y x : APMM02A03Plane) :
    apm_m02a03_laplacian (apm_m02a03_regularizedKernelAt ε y) x =
      ε ^ 2 / (Real.pi * (‖x - y‖ ^ 2 + ε ^ 2) ^ 2) := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  rw [apm_m02a03_laplacian_eq_mathlib _
    (apm_m02a03_regularizedKernelAt_contDiff hε y) x]
  calc
    Laplacian.laplacian (apm_m02a03_regularizedKernelAt ε y) x =
        ∑ i : Fin 2, iteratedFDeriv ℝ 2
          (apm_m02a03_regularizedKernelAt ε y) x ![b i, b i] :=
      congrFun
        (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
          (apm_m02a03_regularizedKernelAt ε y) b) x
    _ = ∑ i : Fin 2, iteratedFDeriv ℝ 2
          (apm_m02a03_regularizedKernel ε) (x - y) ![b i, b i] := by
      apply Finset.sum_congr rfl
      intro i _
      change iteratedFDeriv ℝ 2
          (fun z => apm_m02a03_regularizedKernel ε (z - y)) x ![b i, b i] = _
      exact congrArg (fun L => L ![b i, b i])
        (iteratedFDeriv_comp_sub (𝕜 := ℝ)
          (f := apm_m02a03_regularizedKernel ε) 2 y x)
    _ = Laplacian.laplacian (apm_m02a03_regularizedKernel ε) (x - y) :=
      (congrFun
        (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
          (apm_m02a03_regularizedKernel ε) b) (x - y)).symm
    _ = apm_m02a03_laplacian (apm_m02a03_regularizedKernel ε) (x - y) :=
      (apm_m02a03_laplacian_eq_mathlib _
        (apm_m02a03_regularizedKernel_contDiff hε) (x - y)).symm
    _ = _ := apm_m02a03_regularizedKernel_laplacian hε (x - y)

lemma apm_m02a03_regularizedKernelAt_green_identity
    {ε : ℝ} (hε : ε ≠ 0) (y : APMM02A03Plane)
    (φ : APMM02A03Plane → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    (∫ x, apm_m02a03_regularizedKernelAt ε y x *
        apm_m02a03_laplacian φ x) =
      ∫ x, (ε ^ 2 / (Real.pi * (‖x - y‖ ^ 2 + ε ^ 2) ^ 2)) * φ x := by
  rw [apm_m02a03_integral_mul_laplacian_eq
    (apm_m02a03_regularizedKernelAt ε y) φ
    (apm_m02a03_regularizedKernelAt_contDiff hε y) hφ hφc]
  congr 1
  funext x
  rw [apm_m02a03_regularizedKernelAt_laplacian hε y x]

/-- The fixed mass-one profile whose dilates are the Laplacians of the
regularized logarithmic kernels. -/
noncomputable def apm_m02a03_peakProfile (x : APMM02A03Plane) : ℝ :=
  1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)

lemma apm_m02a03_peakProfile_nonneg (x : APMM02A03Plane) :
    0 ≤ apm_m02a03_peakProfile x := by
  dsimp [apm_m02a03_peakProfile]
  positivity

lemma apm_m02a03_peakProfile_scale
    {c : ℝ} (hc : 0 < c) (y x : APMM02A03Plane) :
    c ^ 2 * apm_m02a03_peakProfile (c • (y - x)) =
      (c⁻¹) ^ 2 /
        (Real.pi * (‖x - y‖ ^ 2 + (c⁻¹) ^ 2) ^ 2) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [apm_m02a03_peakProfile, norm_smul, Real.norm_eq_abs,
    abs_of_pos hc, norm_sub_rev]
  field_simp
  ring

lemma apm_m02a03_peakProfile_radial_integral :
    (∫ r in Set.Ioi (0 : ℝ),
      r * (1 / (Real.pi * (1 + r ^ 2) ^ 2))) = 1 / (2 * Real.pi) := by
  let F : ℝ → ℝ := fun r => -1 / (2 * Real.pi * (1 + r ^ 2))
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hderiv : ∀ r ∈ Set.Ici (0 : ℝ),
      HasDerivAt F (r * (1 / (Real.pi * (1 + r ^ 2) ^ 2))) r := by
    intro r _
    have hD : HasDerivAt (fun s : ℝ => 2 * Real.pi * (1 + s ^ 2))
        (2 * Real.pi * (2 * r)) r := by
      convert (hasDerivAt_const r (2 * Real.pi)).mul
        ((hasDerivAt_const r 1).add (hasDerivAt_id r |>.pow 2)) using 1
      all_goals simp [id]
    dsimp only [F]
    convert (hasDerivAt_const r (-1)).div hD (by positivity) using 1
    field_simp
    ring
  have hnonneg : ∀ r ∈ Set.Ioi (0 : ℝ),
      0 ≤ r * (1 / (Real.pi * (1 + r ^ 2) ^ 2)) := by
    intro r hr
    exact mul_nonneg hr.le (by positivity)
  have hdenom : Filter.Tendsto (fun r : ℝ => 2 * Real.pi * (1 + r ^ 2))
      Filter.atTop Filter.atTop := by
    have hsq : Filter.Tendsto (fun r : ℝ => r ^ 2) Filter.atTop Filter.atTop := by
      simpa [pow_two] using
        (Filter.tendsto_id : Filter.Tendsto (fun r : ℝ => r)
          Filter.atTop Filter.atTop).atTop_mul_atTop₀ Filter.tendsto_id
    have hadd : Filter.Tendsto (fun r : ℝ => 1 + r ^ 2)
        Filter.atTop Filter.atTop := by
      simpa [add_comm] using
        Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ) hsq
    exact hadd.const_mul_atTop (mul_pos (by norm_num) Real.pi_pos)
  have hlim : Filter.Tendsto F Filter.atTop (nhds 0) := by
    exact hdenom.const_div_atTop (-1)
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnonneg hlim]
  dsimp [F]
  field_simp
  ring

lemma apm_m02a03_peakProfile_integral :
    ∫ x : APMM02A03Plane, apm_m02a03_peakProfile x = 1 := by
  change (∫ x : APMM02A03Plane,
    (fun r : ℝ => 1 / (Real.pi * (1 + r ^ 2) ^ 2)) ‖x‖) = 1
  calc
    _ = Module.finrank ℝ APMM02A03Plane •
        (volume : Measure APMM02A03Plane).real (Metric.ball 0 1) •
        ∫ r in Set.Ioi (0 : ℝ), r ^ (Module.finrank ℝ APMM02A03Plane - 1) •
          (1 / (Real.pi * (1 + r ^ 2) ^ 2)) :=
      MeasureTheory.integral_fun_norm_addHaar
        (volume : Measure APMM02A03Plane)
        (fun r : ℝ => 1 / (Real.pi * (1 + r ^ 2) ^ 2))
    _ = 1 := by
      simp only [APMM02A03Plane, finrank_euclideanSpace, Fintype.card_fin,
        Nat.reduceSubDiff, pow_one, smul_eq_mul]
      rw [apm_m02a03_peakProfile_radial_integral]
      simp [MeasureTheory.Measure.real, Real.pi_pos.le]

lemma apm_m02a03_peakProfile_integrable :
    Integrable apm_m02a03_peakProfile volume :=
  integrable_of_integral_eq_one apm_m02a03_peakProfile_integral

lemma apm_m02a03_peakProfile_weighted_tendsto :
    Filter.Tendsto
      (fun x : APMM02A03Plane => ‖x‖ ^ 2 * apm_m02a03_peakProfile x)
      (Bornology.cobounded APMM02A03Plane) (nhds 0) := by
  have hsq : Filter.Tendsto (fun r : ℝ => r ^ 2)
      Filter.atTop Filter.atTop := by
    simpa [pow_two] using
      (Filter.tendsto_id : Filter.Tendsto (fun r : ℝ => r)
        Filter.atTop Filter.atTop).atTop_mul_atTop₀ Filter.tendsto_id
  have hinv : Filter.Tendsto (fun r : ℝ => 1 / r ^ 2)
      Filter.atTop (nhds 0) := hsq.const_div_atTop 1
  have hden : Filter.Tendsto (fun r : ℝ => (1 + 1 / r ^ 2) ^ 2)
      Filter.atTop (nhds 1) := by
    convert (tendsto_const_nhds.add hinv).pow 2 using 1 <;> norm_num
  have hscalar : Filter.Tendsto
      (fun r : ℝ => r ^ 2 * (1 / (Real.pi * (1 + r ^ 2) ^ 2)))
      Filter.atTop (nhds 0) := by
    have hrewritten : Filter.Tendsto
        (fun r : ℝ => (1 / Real.pi) * ((1 / r ^ 2) / (1 + 1 / r ^ 2) ^ 2))
        Filter.atTop (nhds 0) := by
      convert tendsto_const_nhds.mul (hinv.div hden (by norm_num)) using 1
      norm_num
    apply hrewritten.congr'
    filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with r hr
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
    ring
  simpa only [apm_m02a03_peakProfile, Metric.cobounded_eq_cocompact] using
    hscalar.comp (tendsto_norm_cocompact_atTop (E := APMM02A03Plane))

set_option maxHeartbeats 800000 in
lemma apm_m02a03_peakProfile_tendsto_integral
    (φ : APMM02A03Plane → ℝ) (y : APMM02A03Plane)
    (hφi : Integrable φ volume) (hφy : ContinuousAt φ y) :
    Filter.Tendsto
      (fun c : ℝ => ∫ x,
        (c ^ 2 * apm_m02a03_peakProfile (c • (y - x))) * φ x)
      Filter.atTop (nhds (φ y)) := by
  have hdecay : Filter.Tendsto
      (fun x : APMM02A03Plane =>
        ‖x‖ ^ Module.finrank ℝ APMM02A03Plane * apm_m02a03_peakProfile x)
      (Bornology.cobounded APMM02A03Plane) (nhds 0) := by
    simpa only [APMM02A03Plane, finrank_euclideanSpace, Fintype.card_fin] using
      apm_m02a03_peakProfile_weighted_tendsto
  simpa only [APMM02A03Plane, finrank_euclideanSpace, Fintype.card_fin,
    smul_eq_mul] using
    (tendsto_integral_comp_smul_smul_of_integrable'
      apm_m02a03_peakProfile_nonneg apm_m02a03_peakProfile_integral
      hdecay hφi hφy)

lemma apm_m02a03_regularized_density_tendsto
    (φ : APMM02A03Plane → ℝ) (y : APMM02A03Plane)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Filter.Tendsto
      (fun c : ℝ => ∫ x,
        ((c⁻¹) ^ 2 /
          (Real.pi * (‖x - y‖ ^ 2 + (c⁻¹) ^ 2) ^ 2)) * φ x)
      Filter.atTop (nhds (φ y)) := by
  have hpeak := apm_m02a03_peakProfile_tendsto_integral φ y
    (hφ.integrable_of_hasCompactSupport hφc) hφ.continuousAt
  apply hpeak.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with c hc
  apply integral_congr_ae
  filter_upwards [] with x
  rw [apm_m02a03_peakProfile_scale hc y x]

lemma apm_m02a03_abs_log_sq_add_sq_le
    {r ε : ℝ} (hr : 0 < r) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |Real.log (r ^ 2 + ε ^ 2)| ≤
      2 * |Real.log r| + Real.log 2 := by
  have harg : 0 < r ^ 2 + ε ^ 2 := by positivity
  have hεsq : ε ^ 2 ≤ 1 := by nlinarith
  by_cases hr1 : r ≤ 1
  · have hrsq : r ^ 2 ≤ 1 := by nlinarith
    have hu : Real.log (r ^ 2 + ε ^ 2) ≤ Real.log 2 :=
      Real.log_le_log harg (by nlinarith)
    have hl : 2 * Real.log r ≤ Real.log (r ^ 2 + ε ^ 2) := by
      have hl' : Real.log (r ^ 2) ≤ Real.log (r ^ 2 + ε ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith [sq_nonneg ε])
      rw [Real.log_pow] at hl'
      norm_num at hl' ⊢
      exact hl'
    rw [abs_le]
    constructor
    · have ha := neg_abs_le (Real.log r)
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    · have ha := abs_nonneg (Real.log r)
      linarith
  · have hr1' : 1 ≤ r := le_of_not_ge hr1
    have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1'
    have harg1 : 1 ≤ r ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg ε]
    rw [abs_of_nonneg (Real.log_nonneg harg1), abs_of_nonneg hlogr]
    have hu : Real.log (r ^ 2 + ε ^ 2) ≤ Real.log (2 * r ^ 2) :=
      Real.log_le_log harg (by nlinarith)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hu
    convert hu using 1 <;> ring

noncomputable def apm_m02a03_logPairingBound
    (y : APMM02A03Plane) (g : APMM02A03Plane → ℝ)
    (x : APMM02A03Plane) : ℝ :=
  |apm_m02a03_kernel y x * g x| +
    (Real.log 2 / (4 * Real.pi)) * |g x|

lemma apm_m02a03_logPairingBound_integrable
    (y : APMM02A03Plane) (g : APMM02A03Plane → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (apm_m02a03_logPairingBound y g) volume := by
  apply Integrable.add
  · exact (apm_m02a03_kernel_mul_integrable y g hg hgc).norm
  · exact (hg.integrable_of_hasCompactSupport hgc).norm.const_mul _

lemma apm_m02a03_regularizedKernelAt_mul_norm_le_bound
    {c : ℝ} (hc : 1 ≤ c) {x y : APMM02A03Plane} (hxy : x ≠ y)
    (g : APMM02A03Plane → ℝ) :
    ‖apm_m02a03_regularizedKernelAt c⁻¹ y x * g x‖ ≤
      apm_m02a03_logPairingBound y g x := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hε0 : 0 ≤ c⁻¹ := (inv_pos.mpr hc0).le
  have hε1 : c⁻¹ ≤ 1 := (inv_le_one₀ hc0).mpr hc
  have hlog := apm_m02a03_abs_log_sq_add_sq_le hr hε0 hε1
  rw [Real.norm_eq_abs, abs_mul]
  unfold apm_m02a03_regularizedKernelAt apm_m02a03_regularizedKernel
  unfold apm_m02a03_logPairingBound apm_m02a03_kernel
  rw [abs_mul, abs_mul, abs_mul]
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [abs_of_pos (by positivity : 0 < 1 / (4 * Real.pi)),
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  have hg0 : 0 ≤ |g x| := abs_nonneg _
  calc
    1 / (4 * Real.pi) * |Real.log (‖x - y‖ ^ 2 + c⁻¹ ^ 2)| * |g x| ≤
        1 / (4 * Real.pi) *
          (2 * |Real.log ‖x - y‖| + Real.log 2) * |g x| := by
      gcongr
    _ = 1 / (2 * Real.pi) * |Real.log ‖x - y‖| * |g x| +
        Real.log 2 / (4 * Real.pi) * |g x| := by
      field_simp
      ring

lemma apm_m02a03_regularizedKernelAt_pairing_tendsto
    (y : APMM02A03Plane) (g : APMM02A03Plane → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Filter.Tendsto
      (fun c : ℝ => ∫ x,
        apm_m02a03_regularizedKernelAt c⁻¹ y x * g x)
      Filter.atTop (nhds (∫ x, apm_m02a03_kernel y x * g x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (apm_m02a03_logPairingBound y g)
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with c hc
    exact ((apm_m02a03_regularizedKernelAt_contDiff
      (inv_ne_zero hc.ne') y).continuous.mul hg).aestronglyMeasurable
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with c hc
    have hne : ∀ᵐ x : APMM02A03Plane ∂volume, x ≠ y := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with x hxy
    exact apm_m02a03_regularizedKernelAt_mul_norm_le_bound hc hxy g
  · exact apm_m02a03_logPairingBound_integrable y g hg hgc
  · have hne : ∀ᵐ x : APMM02A03Plane ∂volume, x ≠ y := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with x hxy
    have hk := (apm_m02a03_regularizedKernel_tendsto
      (x := x - y) (sub_ne_zero.mpr hxy)).comp
      (tendsto_inv_atTop_zero : Filter.Tendsto (fun c : ℝ => c⁻¹)
        Filter.atTop (nhds 0))
    simpa [apm_m02a03_regularizedKernelAt, apm_m02a03_kernel] using
      hk.mul_const (g x)

theorem apm_m02a03 (y : APMM02A03Plane) :
    LocallyIntegrable (apm_m02a03_kernel y) volume ∧
    ∀ φ : APMM02A03Plane → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      (∫ x, apm_m02a03_kernel y x * apm_m02a03_laplacian φ x) = φ y := by
  refine ⟨apm_m02a03_kernel_locallyIntegrable y, ?_⟩
  intro φ hφ hφc
  have hleft := apm_m02a03_regularizedKernelAt_pairing_tendsto y
    (apm_m02a03_laplacian φ)
    (apm_m02a03_laplacian_continuous φ hφ hφc)
    (apm_m02a03_laplacian_hasCompactSupport φ hφ hφc)
  have hright := apm_m02a03_regularized_density_tendsto φ y
    hφ.continuous hφc
  have heq : ∀ᶠ c : ℝ in Filter.atTop,
      (∫ x, apm_m02a03_regularizedKernelAt c⁻¹ y x *
        apm_m02a03_laplacian φ x) =
      ∫ x, ((c⁻¹) ^ 2 /
        (Real.pi * (‖x - y‖ ^ 2 + (c⁻¹) ^ 2) ^ 2)) * φ x := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with c hc
    exact apm_m02a03_regularizedKernelAt_green_identity
      (inv_ne_zero hc.ne') y φ hφ hφc
  have hleft' : Filter.Tendsto
      (fun c : ℝ => ∫ x,
        apm_m02a03_regularizedKernelAt c⁻¹ y x *
          apm_m02a03_laplacian φ x)
      Filter.atTop (nhds (φ y)) :=
    hright.congr' (heq.mono fun _ h => h.symm)
  exact tendsto_nhds_unique hleft hleft'
