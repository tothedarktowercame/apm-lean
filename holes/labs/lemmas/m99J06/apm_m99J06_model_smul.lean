import Mathlib

/-!
# APM m99J06: Galerkin approximation in `H¹₀(0,1)`

## Statement repairs

The former model stored weak derivatives as literal functions even though its
inner product observed them only almost everywhere, making the hypothesized
structure inconsistent. Weak derivatives are now elements of Mathlib's `L²`
space, which quotients functions by almost-everywhere equality. Thus changing a
derivative on a singleton no longer creates a distinct representative.

Part (d) is stated faithfully for the full Galerkin sequence.  Galerkin
orthogonality identifies `uₙ` with the orthogonal projection of the unique
weak solution onto `V n`; nestedness and density then give norm convergence,
and hence weak convergence, of the entire sequence.

## Encoding questions

None. `H¹₀(0,1)` is represented by absolutely continuous functions with an
`L²` weak derivative and zero endpoint trace. The derivative is an `L²`
equivalence class, so all identities have the correct almost-everywhere
semantics.
-/

open Filter MeasureTheory Set

noncomputable section

abbrev apm_m99J06_intervalMeasure : Measure ℝ :=
  volume.restrict (Icc 0 1)

abbrev apm_m99J06_L2 :=
  Lp ℝ 2 apm_m99J06_intervalMeasure

def apm_m99J06_isH01Pair (u : ℝ → ℝ) (du : apm_m99J06_L2) : Prop :=
  AbsolutelyContinuousOnInterval u 0 1 ∧
  MemLp u 2 apm_m99J06_intervalMeasure ∧
  (∃ duRep : ℝ → ℝ,
    ∃ hdu : MemLp duRep 2 apm_m99J06_intervalMeasure,
      hdu.toLp duRep = du ∧
      ∀ᵐ x ∂apm_m99J06_intervalMeasure, HasDerivAt u (duRep x) x) ∧
  u 0 = 0 ∧ u 1 = 0

structure apm_m99J06_H01Model (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] where
  val : H → ℝ → ℝ
  weakDeriv : H → apm_m99J06_L2
  represents : ∀ u : H, apm_m99J06_isH01Pair (val u) (weakDeriv u)
  realizes : ∀ (u : ℝ → ℝ) (du : apm_m99J06_L2),
    apm_m99J06_isH01Pair u du →
      ∃ w : H, val w = u ∧ weakDeriv w = du
  inner_eq : ∀ u v : H,
    inner ℝ u v = ∫ x in Icc (0 : ℝ) 1,
      val u x * val v x + weakDeriv u x * weakDeriv v x

def apm_m99J06_weakSolution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (u : H) : Prop :=
  ∀ v : H, inner ℝ u v = ∫ x in Icc (0 : ℝ) 1, f x * M.val v x

def apm_m99J06_strongSolution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (u : H) : Prop :=
  ∃ du ddu : ℝ → ℝ,
    ∃ hdu : MemLp du 2 apm_m99J06_intervalMeasure,
    ∃ hddu : MemLp ddu 2 apm_m99J06_intervalMeasure,
      hdu.toLp du = M.weakDeriv u ∧
      AbsolutelyContinuousOnInterval du 0 1 ∧
      (∀ᵐ x ∂apm_m99J06_intervalMeasure, HasDerivAt du (ddu x) x) ∧
      (∀ᵐ x ∂apm_m99J06_intervalMeasure, M.val u x - ddu x = f x)

def apm_m99J06_galerkinEquation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (V : Submodule ℝ H) (u : V) : Prop :=
  ∀ v : V, inner ℝ (u : H) (v : H) =
    ∫ x in Icc (0 : ℝ) 1, f x * M.val (v : H) x

lemma apm_m99J06_isH01Pair_zero :
    apm_m99J06_isH01Pair (fun _ : ℝ ↦ 0) (0 : apm_m99J06_L2) := by
  refine ⟨?_, MemLp.zero, ?_, rfl, rfl⟩
  · rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    refine ⟨1, zero_lt_one, ?_⟩
    intro E _ _
    simpa using hε
  · refine ⟨(fun _ : ℝ ↦ 0), MemLp.zero, ?_, ?_⟩
    · simp
    · filter_upwards with x
      simpa using (hasDerivAt_const x (0 : ℝ))

lemma apm_m99J06_model_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H) :
    M.val 0 = (fun _ : ℝ ↦ 0) ∧ M.weakDeriv 0 = 0 := by
  obtain ⟨w, hwv, hwd⟩ := M.realizes (fun _ : ℝ ↦ 0) 0 apm_m99J06_isH01Pair_zero
  have hi : inner ℝ w w = 0 := by
    rw [M.inner_eq, hwv, hwd]
    apply MeasureTheory.integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℝ 2 apm_m99J06_intervalMeasure] with x hx
    have hx' : (0 : apm_m99J06_L2) x = 0 := by simpa using hx
    rw [hx']
    norm_num
  have hw0 : w = 0 := inner_self_eq_zero.mp hi
  subst w
  exact ⟨hwv, hwd⟩

lemma apm_m99J06_isH01Pair_add
    {u v : ℝ → ℝ} {du dv : apm_m99J06_L2}
    (hu : apm_m99J06_isH01Pair u du)
    (hv : apm_m99J06_isH01Pair v dv) :
    apm_m99J06_isH01Pair (u + v) (du + dv) := by
  rcases hu with ⟨huac, huLp, ⟨duRep, hduRep, hduto, huderiv⟩, hu0, hu1⟩
  rcases hv with ⟨hvac, hvLp, ⟨dvRep, hdvRep, hdvto, hvderiv⟩, hv0, hv1⟩
  refine ⟨huac.add hvac, huLp.add hvLp, ?_, ?_, ?_⟩
  · refine ⟨duRep + dvRep, hduRep.add hdvRep, ?_, ?_⟩
    · change (hduRep.add hdvRep).toLp (duRep + dvRep) = du + dv
      rw [hduRep.toLp_add hdvRep, hduto, hdvto]
    · filter_upwards [huderiv, hvderiv] with x hux hvx
      simpa only [Pi.add_apply] using hux.add hvx
  · simp only [Pi.add_apply, hu0, hv0, add_zero]
  · simp only [Pi.add_apply, hu1, hv1, add_zero]

lemma apm_m99J06_isH01Pair_smul
    {u : ℝ → ℝ} {du : apm_m99J06_L2}
    (hu : apm_m99J06_isH01Pair u du) (c : ℝ) :
    apm_m99J06_isH01Pair (c • u) (c • du) := by
  rcases hu with ⟨huac, huLp, ⟨duRep, hduRep, hduto, huderiv⟩, hu0, hu1⟩
  refine ⟨huac.const_smul c, huLp.const_smul c, ?_, ?_, ?_⟩
  · refine ⟨c • duRep, hduRep.const_smul c, ?_, ?_⟩
    · change (hduRep.const_smul c).toLp (c • duRep) = c • du
      rw [hduRep.toLp_const_smul c, hduto]
    · filter_upwards [huderiv] with x hx
      simpa only [Pi.smul_apply, smul_eq_mul] using hx.const_smul c
  · simp only [Pi.smul_apply, smul_eq_mul, hu0, mul_zero]
  · simp only [Pi.smul_apply, smul_eq_mul, hu1, mul_zero]

lemma apm_m99J06_integrable_inner_components {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : apm_m99J06_H01Model H) (u v : H) :
    Integrable (M.val u * M.val v) apm_m99J06_intervalMeasure ∧
    Integrable (fun x ↦ M.weakDeriv u x * M.weakDeriv v x)
      apm_m99J06_intervalMeasure := by
  constructor
  · exact (M.represents u).2.1.integrable_mul (M.represents v).2.1
  · simpa only [Pi.mul_apply] using
      (Lp.memLp (M.weakDeriv u)).integrable_mul (Lp.memLp (M.weakDeriv v))

lemma apm_m99J06_model_add {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H) (u v : H) :
    M.val (u + v) = M.val u + M.val v ∧
      M.weakDeriv (u + v) = M.weakDeriv u + M.weakDeriv v := by
  obtain ⟨w, hwv, hwd⟩ := M.realizes (M.val u + M.val v)
    (M.weakDeriv u + M.weakDeriv v)
    (apm_m99J06_isH01Pair_add (M.represents u) (M.represents v))
  have hw : w = u + v := by
    apply ext_inner_right ℝ
    intro z
    rw [M.inner_eq, hwv, hwd, inner_add_left, M.inner_eq, M.inner_eq]
    have huz := apm_m99J06_integrable_inner_components M u z
    have hvz := apm_m99J06_integrable_inner_components M v z
    have huz' : Integrable (fun x ↦
        M.val u x * M.val z x + M.weakDeriv u x * M.weakDeriv z x)
        apm_m99J06_intervalMeasure := by
      exact (huz.1.add huz.2)
    have hvz' : Integrable (fun x ↦
        M.val v x * M.val z x + M.weakDeriv v x * M.weakDeriv z x)
        apm_m99J06_intervalMeasure := by
      exact (hvz.1.add hvz.2)
    change (∫ x, (M.val u x + M.val v x) * M.val z x +
        (M.weakDeriv u + M.weakDeriv v) x * M.weakDeriv z x
          ∂apm_m99J06_intervalMeasure) =
      (∫ x, M.val u x * M.val z x + M.weakDeriv u x * M.weakDeriv z x
          ∂apm_m99J06_intervalMeasure) +
      ∫ x, M.val v x * M.val z x + M.weakDeriv v x * M.weakDeriv z x
          ∂apm_m99J06_intervalMeasure
    rw [← MeasureTheory.integral_add huz' hvz']
    apply MeasureTheory.integral_congr_ae
    filter_upwards [Lp.coeFn_add (M.weakDeriv u) (M.weakDeriv v)] with x hx
    change ((M.val u x + M.val v x) * M.val z x +
        (M.weakDeriv u + M.weakDeriv v) x * M.weakDeriv z x) = _
    rw [hx]
    simp only [Pi.add_apply]
    ring
  subst w
  exact ⟨hwv, hwd⟩

/-- A represented function together with its `L²` weak derivative uniquely
determines the Hilbert-space element. -/
lemma apm_m99J06_model_ext {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H) {u v : H}
    (hval : M.val u = M.val v) (hderiv : M.weakDeriv u = M.weakDeriv v) :
    u = v := by
  apply ext_inner_right ℝ
  intro w
  rw [M.inner_eq, M.inner_eq, hval, hderiv]

/-- The realization supplied by the model is unique. -/
lemma apm_m99J06_realizes_unique {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H)
    {u : ℝ → ℝ} {du : apm_m99J06_L2} (h : apm_m99J06_isH01Pair u du)
    {w₁ w₂ : H}
    (h₁ : M.val w₁ = u ∧ M.weakDeriv w₁ = du)
    (h₂ : M.val w₂ = u ∧ M.weakDeriv w₂ = du) : w₁ = w₂ := by
  apply apm_m99J06_model_ext M
  · exact h₁.1.trans h₂.1.symm
  · exact h₁.2.trans h₂.2.symm

/-- Galerkin solutions are unique on every subspace; this uses only the
coercivity of the ambient inner product. -/
lemma apm_m99J06_galerkin_unique {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (V : Submodule ℝ H) {u w : V}
    (hu : apm_m99J06_galerkinEquation M f V u)
    (hw : apm_m99J06_galerkinEquation M f V w) : u = w := by
  apply Subtype.ext
  have hz' := hw (u - w)
  have hinner : inner ℝ ((u : H) - (w : H)) ((u : H) - (w : H)) = 0 := by
    rw [inner_sub_left]
    simpa using sub_eq_zero.mpr ((hu (u - w)).trans hz'.symm)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hinner)

/-! ### Split of `apm_m99J06_weak_iff_strong` (claude-14, 2026-10-13, after a partial round-2 attempt)
Mathlib supplies the analysis: `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul`,
`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`,
`IntervalIntegrable.ae_hasDerivAt_integral`. The three lemmas below are parallel:
`weak_to_strong` takes the du Bois-Reymond lemma as a hypothesis. -/

/-- Strong ⇒ weak: integrate `ddu * v` by parts; the boundary term vanishes since `v 0 = v 1 = 0`. -/
theorem apm_m99J06_strong_to_weak
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : apm_m99J06_H01Model H) (f : ℝ → ℝ) (u : H)
    (hu : apm_m99J06_strongSolution M f u) :
    apm_m99J06_weakSolution M f u := by
  rcases hu with ⟨du, ddu, hdu, hddu, hduto, hduac, hduderiv, heqn⟩
  intro v
  rcases M.represents v with ⟨hvac, hvLp, ⟨dv, hdv, hdvto, hvderiv⟩, hv0, hv1⟩
  have hdu_deriv : ∀ᵐ x ∂apm_m99J06_intervalMeasure,
      deriv du x = ddu x := by
    filter_upwards [hduderiv] with x hx
    exact hx.deriv
  have hv_deriv : ∀ᵐ x ∂apm_m99J06_intervalMeasure,
      deriv (M.val v) x = dv x := by
    filter_upwards [hvderiv] with x hx
    exact hx.deriv
  have hud_coe : ∀ᵐ x ∂apm_m99J06_intervalMeasure,
      M.weakDeriv u x = du x := by
    have hcoe := hdu.coeFn_toLp
    rw [hduto] at hcoe
    exact hcoe
  have hvd_coe : ∀ᵐ x ∂apm_m99J06_intervalMeasure,
      M.weakDeriv v x = dv x := by
    have hcoe := hdv.coeFn_toLp
    rw [hdvto] at hcoe
    exact hcoe
  have hibp := hduac.integral_mul_deriv_eq_deriv_mul hvac
  rw [intervalIntegral.integral_of_le zero_le_one,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc] at hibp
  rw [intervalIntegral.integral_of_le zero_le_one,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc] at hibp
  have hibp' : (∫ x in Icc (0 : ℝ) 1, du x * dv x) =
      -(∫ x in Icc (0 : ℝ) 1, ddu x * M.val v x) := by
    calc
      (∫ x in Icc (0 : ℝ) 1, du x * dv x) =
          ∫ x in Icc (0 : ℝ) 1, du x * deriv (M.val v) x := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [hv_deriv] with x hx
            rw [hx]
      _ = du 1 * M.val v 1 - du 0 * M.val v 0 -
          ∫ x in Icc (0 : ℝ) 1, deriv du x * M.val v x := hibp
      _ = -(∫ x in Icc (0 : ℝ) 1, ddu x * M.val v x) := by
            rw [hv0, hv1]
            simp only [mul_zero, sub_zero, zero_sub]
            congr 1
            apply MeasureTheory.integral_congr_ae
            filter_upwards [hdu_deriv] with x hx
            rw [hx]
  rw [M.inner_eq]
  have hweak : (∫ x in Icc (0 : ℝ) 1,
      M.weakDeriv u x * M.weakDeriv v x) =
      -(∫ x in Icc (0 : ℝ) 1, ddu x * M.val v x) := by
    rw [← hibp']
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hud_coe, hvd_coe] with x hux hvx
    rw [hux, hvx]
  have huv := apm_m99J06_integrable_inner_components M u v
  change (∫ x, (M.val u * M.val v) x +
      (fun x ↦ M.weakDeriv u x * M.weakDeriv v x) x
        ∂apm_m99J06_intervalMeasure) = _
  rw [MeasureTheory.integral_add huv.1 huv.2, hweak]
  rw [← sub_eq_add_neg]
  change (∫ x, (M.val u * M.val v) x ∂apm_m99J06_intervalMeasure) -
      (∫ x, (ddu * M.val v) x ∂apm_m99J06_intervalMeasure) =
      ∫ x, (f * M.val v) x ∂apm_m99J06_intervalMeasure
  rw [← MeasureTheory.integral_sub huv.1
    (hddu.integrable_mul hvLp)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [heqn] with x hx
  simp only [Pi.mul_apply]
  rw [← hx]
  ring

/-- du Bois-Reymond for the model: if `∫ g w' = ∫ h w` for every `w`, then `g = c − ∫₀ˣ h` a.e.
Test with `w` realizing `x ↦ ∫₀ˣ (g + G − mean)`, `G x = ∫₀ˣ h`. -/
lemma apm_m99J06_du_bois_reymond_aux_memLp_of_continuousOn
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    MemLp f 2 apm_m99J06_intervalMeasure := by
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hf.norm)
  apply MemLp.of_bound (hf.aestronglyMeasurable measurableSet_Icc) C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC ‖f x‖ ⟨x, hx, rfl⟩

theorem apm_m99J06_du_bois_reymond
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : apm_m99J06_H01Model H) (g h : ℝ → ℝ)
    (hg : MemLp g 2 apm_m99J06_intervalMeasure) (hh : MemLp h 2 apm_m99J06_intervalMeasure)
    (hw : ∀ w : H, ∫ x in Icc (0 : ℝ) 1, g x * M.weakDeriv w x =
      ∫ x in Icc (0 : ℝ) 1, h x * M.val w x) :
    ∃ c : ℝ, ∀ᵐ x ∂apm_m99J06_intervalMeasure, g x = c - ∫ t in (0 : ℝ)..x, h t := by
  have hhInt : IntervalIntegrable h volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
    exact hh.integrable (by norm_num)
  let G : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, h t
  have hGac : AbsolutelyContinuousOnInterval G 0 1 := by
    exact hhInt.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hGmem : MemLp G 2 apm_m99J06_intervalMeasure :=
    apm_m99J06_du_bois_reymond_aux_memLp_of_continuousOn G (by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hGac.continuousOn)
  let c : ℝ := ∫ x in (0 : ℝ)..1, g x + G x
  let q : ℝ → ℝ := fun x ↦ g x + G x - c
  have hqmem : MemLp q 2 apm_m99J06_intervalMeasure := by
    exact (hg.add hGmem).sub (memLp_const c)
  have hqInt : IntervalIntegrable q volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
    exact hqmem.integrable (by norm_num)
  have hqzero : ∫ x in (0 : ℝ)..1, q x = 0 := by
    rw [show q = fun x ↦ (g x + G x) - c by rfl]
    rw [intervalIntegral.integral_sub]
    · simp [c]
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
      exact (hg.add hGmem).integrable (by norm_num)
    · exact intervalIntegrable_const
  let W : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, q t
  have hWac : AbsolutelyContinuousOnInterval W 0 1 :=
    hqInt.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hWmem : MemLp W 2 apm_m99J06_intervalMeasure :=
    apm_m99J06_du_bois_reymond_aux_memLp_of_continuousOn W (by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hWac.continuousOn)
  have hqderiv_vol : ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → HasDerivAt W (q x) x := by
    filter_upwards [hqInt.ae_hasDerivAt_integral] with x hx
    intro hxI
    exact hx (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hxI)
      0 (by simp [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)])
  have hqderiv : ∀ᵐ x ∂apm_m99J06_intervalMeasure, HasDerivAt W (q x) x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae hqderiv_vol] with x hx hd
    exact hd hx
  have hWpair : apm_m99J06_isH01Pair W (hqmem.toLp q) := by
    refine ⟨hWac, hWmem, ⟨q, hqmem, rfl, hqderiv⟩, ?_, ?_⟩
    · simp [W]
    · simpa [W] using hqzero
  obtain ⟨w, hwval, hwderiv⟩ := M.realizes W (hqmem.toLp q) hWpair
  have heq := hw w
  rw [hwval, hwderiv] at heq
  have heq' : (∫ x in Icc (0 : ℝ) 1, g x * q x) =
      ∫ x in Icc (0 : ℝ) 1, h x * W x := by
    rw [← heq]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hqmem.coeFn_toLp] with x hx
    rw [hx]
  have hGderiv : ∀ᵐ x ∂apm_m99J06_intervalMeasure,
      HasDerivAt G (h x) x := by
    have hdvol : ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → HasDerivAt G (h x) x := by
      filter_upwards [hhInt.ae_hasDerivAt_integral] with x hx
      intro hxI
      exact hx (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hxI)
        0 (by simp [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)])
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae hdvol] with x hx hd
    exact hd hx
  have hibp : (∫ x in Icc (0 : ℝ) 1, h x * W x) =
      -∫ x in Icc (0 : ℝ) 1, G x * q x := by
    have hparts := hGac.integral_mul_deriv_eq_deriv_mul hWac
    have hderG : ∀ᵐ x ∂apm_m99J06_intervalMeasure, deriv G x = h x :=
      hGderiv.mono fun x hx ↦ hx.deriv
    have hderW : ∀ᵐ x ∂apm_m99J06_intervalMeasure, deriv W x = q x :=
      hqderiv.mono fun x hx ↦ hx.deriv
    rw [show G 0 = 0 by simp [G], show W 0 = 0 by simp [W],
      show W 1 = 0 by simpa [W] using hqzero] at hparts
    simp only [mul_zero, sub_zero, zero_mul, zero_sub] at hparts
    rw [intervalIntegral.integral_of_le (by norm_num),
      ← integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by norm_num),
      ← integral_Icc_eq_integral_Ioc] at hparts
    have heqW : (fun x ↦ G x * deriv W x) =ᵐ[apm_m99J06_intervalMeasure]
        fun x ↦ G x * q x := hderW.mono fun x hx ↦ by
      change G x * deriv W x = G x * q x
      rw [hx]
    have heqG : (fun x ↦ deriv G x * W x) =ᵐ[apm_m99J06_intervalMeasure]
        fun x ↦ h x * W x := hderG.mono fun x hx ↦ by
      change deriv G x * W x = h x * W x
      rw [hx]
    rw [MeasureTheory.integral_congr_ae heqW,
      MeasureTheory.integral_congr_ae heqG] at hparts
    linarith [hparts]
  have hsqzero : ∫ x in Icc (0 : ℝ) 1, q x ^ 2 = 0 := by
    rw [show (fun x ↦ q x ^ 2) = fun x ↦ (g x + G x - c) * q x by
      funext x; simp [q]; ring]
    have hgq := heq'
    rw [hibp] at hgq
    have hGq : Integrable (fun x ↦ G x * q x) apm_m99J06_intervalMeasure :=
      hGmem.integrable_mul hqmem
    have hgqInt : Integrable (fun x ↦ g x * q x) apm_m99J06_intervalMeasure :=
      hg.integrable_mul hqmem
    have halg : (fun x ↦ (g x + G x - c) * q x) =
        (fun x ↦ g x * q x) + (fun x ↦ G x * q x) - fun x ↦ c * q x := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [halg]
    change (∫ x, (g x * q x + G x * q x) - c * q x
      ∂apm_m99J06_intervalMeasure) = 0
    have hqi : ∫ x in Icc (0 : ℝ) 1, q x = 0 := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num)]
      exact hqzero
    calc
      (∫ x, g x * q x + G x * q x - c * q x
          ∂apm_m99J06_intervalMeasure) =
          (∫ x, g x * q x + G x * q x
            ∂apm_m99J06_intervalMeasure) -
          ∫ x, c * q x ∂apm_m99J06_intervalMeasure :=
        MeasureTheory.integral_sub (hgqInt.add hGq)
          ((hqmem.integrable (by norm_num)).const_mul c)
      _ = ((∫ x, g x * q x ∂apm_m99J06_intervalMeasure) +
          ∫ x, G x * q x ∂apm_m99J06_intervalMeasure) -
          c * ∫ x, q x ∂apm_m99J06_intervalMeasure := by
        rw [MeasureTheory.integral_add hgqInt hGq,
          MeasureTheory.integral_const_mul]
      _ = 0 := by rw [hgq, hqi]; ring
  refine ⟨c, ?_⟩
  have hsqae : (fun x ↦ q x ^ 2) =ᵐ[apm_m99J06_intervalMeasure] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg (q x))
      (by simpa only [Pi.mul_apply, pow_two] using hqmem.integrable_mul hqmem)).mp
        (by simpa [pow_two] using hsqzero)
  have hqae : q =ᵐ[apm_m99J06_intervalMeasure] 0 := by
    filter_upwards [hsqae] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    exact sq_eq_zero_iff.mp hx
  filter_upwards [hqae] with x hx
  dsimp [q] at hx
  linarith

/-- Weak ⇒ strong, given du Bois-Reymond: with `h = f − u`, `u' = c + ∫₀ˣ (u − f)` is an absolutely
continuous representative with derivative `u − f` a.e. -/
theorem apm_m99J06_weak_to_strong
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : apm_m99J06_H01Model H) (f : ℝ → ℝ)
    (hf : MemLp f 2 apm_m99J06_intervalMeasure)
    (hDBR : ∀ g h : ℝ → ℝ, MemLp g 2 apm_m99J06_intervalMeasure →
      MemLp h 2 apm_m99J06_intervalMeasure →
      (∀ w : H, ∫ x in Icc (0 : ℝ) 1, g x * M.weakDeriv w x =
        ∫ x in Icc (0 : ℝ) 1, h x * M.val w x) →
      ∃ c : ℝ, ∀ᵐ x ∂apm_m99J06_intervalMeasure, g x = c - ∫ t in (0 : ℝ)..x, h t)
    (u : H) (hu : apm_m99J06_weakSolution M f u) :
    apm_m99J06_strongSolution M f u := by
  rcases (M.represents u).2.2.1 with ⟨g, hg, hglp, hgderiv⟩
  have huLp : MemLp (M.val u) 2 apm_m99J06_intervalMeasure :=
    (M.represents u).2.1
  let h : ℝ → ℝ := fun x ↦ f x - M.val u x
  have hh : MemLp h 2 apm_m99J06_intervalMeasure := by
    exact hf.sub huLp
  have htest : ∀ w : H,
      ∫ x in Icc (0 : ℝ) 1, g x * M.weakDeriv w x =
        ∫ x in Icc (0 : ℝ) 1, h x * M.val w x := by
    intro w
    have hi := M.inner_eq u w
    rw [hu w] at hi
    have huv := apm_m99J06_integrable_inner_components M u w
    have hfv : Integrable (fun x ↦ f x * M.val w x)
        apm_m99J06_intervalMeasure := hf.integrable_mul (M.represents w).2.1
    have huv0 : Integrable (fun x ↦ M.val u x * M.val w x)
        apm_m99J06_intervalMeasure := huv.1
    rw [← hglp] at hi huv
    have hdint : Integrable (fun x ↦ (hg.toLp g) x * M.weakDeriv w x)
        apm_m99J06_intervalMeasure := huv.2
    rw [MeasureTheory.integral_add huv0 hdint] at hi
    have hgi : (∫ x, g x * M.weakDeriv w x ∂apm_m99J06_intervalMeasure) =
        ∫ x, (hg.toLp g) x * M.weakDeriv w x ∂apm_m99J06_intervalMeasure := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hg.coeFn_toLp] with x hx
      rw [hx]
    calc
      (∫ x in Icc (0 : ℝ) 1, g x * M.weakDeriv w x) =
          ∫ x in Icc (0 : ℝ) 1, (hg.toLp g) x * M.weakDeriv w x := hgi
      _ =
          (∫ x in Icc (0 : ℝ) 1, f x * M.val w x) -
            ∫ x in Icc (0 : ℝ) 1, M.val u x * M.val w x := by
        linarith
      _ = ∫ x in Icc (0 : ℝ) 1, h x * M.val w x := by
        rw [← MeasureTheory.integral_sub hfv huv0]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        dsimp [h]
        ring
  obtain ⟨c, hc⟩ := hDBR g h hg hh htest
  let G : ℝ → ℝ := fun x ↦ c - ∫ t in (0 : ℝ)..x, h t
  have hGg : G =ᵐ[apm_m99J06_intervalMeasure] g := by
    filter_upwards [hc] with x hx
    exact hx.symm
  have hG : MemLp G 2 apm_m99J06_intervalMeasure :=
    hg.ae_eq hGg.symm
  have hint : IntervalIntegrable h volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
    exact hh.integrable (by norm_num)
  have hGac : AbsolutelyContinuousOnInterval G 0 1 := by
    have hbase : AbsolutelyContinuousOnInterval
        (fun x ↦ ∫ t in (0 : ℝ)..x, h t) 0 1 :=
      hint.absolutelyContinuousOnInterval_intervalIntegral (by simp)
    rw [absolutelyContinuousOnInterval_iff] at hbase ⊢
    simpa only [G, Real.dist_eq, sub_sub_sub_cancel_left, abs_neg, abs_sub_comm] using hbase
  let ddu : ℝ → ℝ := fun x ↦ M.val u x - f x
  have hddu : MemLp ddu 2 apm_m99J06_intervalMeasure := huLp.sub hf
  have hGderiv : ∀ᵐ x ∂apm_m99J06_intervalMeasure,
      HasDerivAt G (ddu x) x := by
    have hd := hint.ae_hasDerivAt_integral
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae hd] with x hx hdx
    have hi := hdx (by simpa using hx) 0 (by simp)
    simpa [G, ddu, h] using (hasDerivAt_const x c).sub hi
  refine ⟨G, ddu, hG, hddu, ?_, hGac, hGderiv, ?_⟩
  · exact (MemLp.toLp_congr hG hg hGg).trans hglp
  · filter_upwards with x
    simp [ddu]

theorem apm_m99J06_weak_iff_strong
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : apm_m99J06_H01Model H) (f : ℝ → ℝ)
    (hf : MemLp f 2 apm_m99J06_intervalMeasure) :
    ∀ u : H, apm_m99J06_weakSolution M f u ↔
      apm_m99J06_strongSolution M f u := by
  intro u
  exact ⟨apm_m99J06_weak_to_strong M f hf
      (fun g h hg hh hw ↦ apm_m99J06_du_bois_reymond M g h hg hh hw) u,
    apm_m99J06_strong_to_weak M f u⟩

/-! ### Split of `apm_m99J06_riesz_on_complete_submodule` (claude-14, 2026-10-13, after a partial
round-2 attempt). The three lemmas are parallel: each takes what it needs as a hypothesis. -/

/-- The model is homogeneous: realize `c • val v` (`apm_m99J06_isH01Pair_smul`) and compare
inner products against every `z` through `inner_eq`. -/
-- BEGIN SEAT AREA
theorem apm_m99J06_model_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : apm_m99J06_H01Model H) (c : ℝ) (v : H) :
    M.val (c • v) = c • M.val v ∧ M.weakDeriv (c • v) = c • M.weakDeriv v := by
  obtain ⟨w, hwv, hwd⟩ := M.realizes (c • M.val v) (c • M.weakDeriv v)
    (apm_m99J06_isH01Pair_smul (M.represents v) c)
  have hw : w = c • v := by
    apply ext_inner_right ℝ
    intro z
    rw [M.inner_eq, hwv, hwd, inner_smul_left, M.inner_eq]
    have hvz := apm_m99J06_integrable_inner_components M v z
    have hvz' : Integrable (fun x ↦
        M.val v x * M.val z x + M.weakDeriv v x * M.weakDeriv z x)
        apm_m99J06_intervalMeasure := hvz.1.add hvz.2
    change (∫ x, (c • M.val v) x * M.val z x +
        (c • M.weakDeriv v) x * M.weakDeriv z x
          ∂apm_m99J06_intervalMeasure) =
      c * ∫ x, M.val v x * M.val z x +
        M.weakDeriv v x * M.weakDeriv z x
          ∂apm_m99J06_intervalMeasure
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [Lp.coeFn_smul c (M.weakDeriv v)] with x hx
    change (c * M.val v x) * M.val z x +
      (c • M.weakDeriv v) x * M.weakDeriv z x =
      c * (M.val v x * M.val z x + M.weakDeriv v x * M.weakDeriv z x)
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  subst w
  exact ⟨hwv, hwd⟩
-- END SEAT AREA

/-- `v ↦ val v` is a bounded linear map into `L²(0,1)`: `‖val v‖₂² ≤ ∫ (val v)² + (v')² = ‖v‖²`. -/
theorem apm_m99J06_val_clm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : apm_m99J06_H01Model H)
    (hsmul : ∀ (c : ℝ) (v : H), M.val (c • v) = c • M.val v ∧
      M.weakDeriv (c • v) = c • M.weakDeriv v) :
    ∃ L : H →L[ℝ] apm_m99J06_L2, ∀ v : H,
      (L v : ℝ → ℝ) =ᵐ[apm_m99J06_intervalMeasure] M.val v := by
  sorry

/-- Riesz on a complete submodule, given the bounded map: the forcing functional is
`v ↦ ⟪hf.toLp f, L v⟫_{L²}`; represent it with `InnerProductSpace.toDual ℝ V`, uniqueness from
`apm_m99J06_galerkin_unique`. -/
theorem apm_m99J06_riesz_of_val_clm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (hf : MemLp f 2 apm_m99J06_intervalMeasure)
    (hL : ∃ L : H →L[ℝ] apm_m99J06_L2, ∀ v : H,
      (L v : ℝ → ℝ) =ᵐ[apm_m99J06_intervalMeasure] M.val v)
    (V : Submodule ℝ H) [CompleteSpace V] :
    ∃! u : V, apm_m99J06_galerkinEquation M f V u := by
  sorry

/-- Shared Riesz-representation bridge for both the ambient weak problem and
finite-dimensional Galerkin problems. -/
theorem apm_m99J06_riesz_on_complete_submodule
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (hf : MemLp f 2 apm_m99J06_intervalMeasure)
    (V : Submodule ℝ H) [CompleteSpace V] :
    ∃! u : V, apm_m99J06_galerkinEquation M f V u := by
  exact apm_m99J06_riesz_of_val_clm M f hf
    (apm_m99J06_val_clm M (fun c v ↦ apm_m99J06_model_smul M c v)) V

theorem apm_m99J06_galerkin_exists_unique
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (hf : MemLp f 2 apm_m99J06_intervalMeasure)
    (V : Submodule ℝ H) [FiniteDimensional ℝ V] :
    ∃! u : V, apm_m99J06_galerkinEquation M f V u := by
  exact apm_m99J06_riesz_on_complete_submodule M f hf V

theorem apm_m99J06_galerkin_norm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (hf : MemLp f 2 apm_m99J06_intervalMeasure)
    (V : Submodule ℝ H) (u : V)
    (hu : apm_m99J06_galerkinEquation M f V u) :
    ‖(u : H)‖ ≤ (eLpNorm f 2 apm_m99J06_intervalMeasure).toReal := by
  sorry

theorem apm_m99J06_weakSolution_exists_unique
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (hf : MemLp f 2 apm_m99J06_intervalMeasure) :
    ∃! u : H, apm_m99J06_weakSolution M f u := by
  letI : IsClosed ((⊤ : Submodule ℝ H) : Set H) := isClosed_univ
  obtain ⟨u, hu, huniq⟩ :=
    apm_m99J06_riesz_on_complete_submodule M f hf (⊤ : Submodule ℝ H)
  refine ⟨u, ?_, ?_⟩
  · intro v
    exact hu ⟨v, trivial⟩
  · intro w hw
    have hsub : (⟨w, trivial⟩ : (⊤ : Submodule ℝ H)) = u := by
      apply huniq
      intro v
      exact hw v
    exact congrArg Subtype.val hsub

theorem apm_m99J06_galerkin_eq_starProjection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (V : Submodule ℝ H) [FiniteDimensional ℝ V]
    (u : H) (hu : apm_m99J06_weakSolution M f u)
    (uV : V) (huV : apm_m99J06_galerkinEquation M f V uV) :
    (uV : H) = V.starProjection u := by
  sorry

theorem apm_m99J06_starProjection_convergence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (V : ℕ → Submodule ℝ H) [∀ n, FiniteDimensional ℝ (V n)]
    (hnested : ∀ n : ℕ, V n ≤ V (n + 1))
    (hdense : Dense (⋃ n : ℕ, (V n : Set H)))
    (uSeq : ∀ n : ℕ, V n)
    (u : H) (hproj : ∀ n, (uSeq n : H) = (V n).starProjection u) :
    Tendsto (fun n ↦ (uSeq n : H)) atTop (nhds u) ∧
      Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n : H)) atTop
        (nhds (toWeakSpace ℝ H u)) := by
  sorry

theorem apm_m99j06
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (M : apm_m99J06_H01Model H)
    (f : ℝ → ℝ) (hf : MemLp f 2 apm_m99J06_intervalMeasure) :
    (∀ u : H,
      apm_m99J06_weakSolution M f u ↔
        apm_m99J06_strongSolution M f u) ∧
    (∀ V : ℕ → Submodule ℝ H,
      (∀ n : ℕ, FiniteDimensional ℝ (V n)) →
      (∀ n : ℕ, V n ≤ V (n + 1)) →
      Dense (⋃ n : ℕ, (V n : Set H)) →
        (∀ n : ℕ, ∃! u : V n, apm_m99J06_galerkinEquation M f (V n) u) ∧
        ∀ uSeq : ∀ n : ℕ, V n,
          (∀ n, apm_m99J06_galerkinEquation M f (V n) (uSeq n)) →
          (∀ n, ‖(uSeq n : H)‖ ≤ (eLpNorm f 2 apm_m99J06_intervalMeasure).toReal) ∧
          ∃ u : H,
            Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n : H)) atTop
              (nhds (toWeakSpace ℝ H u)) ∧
            apm_m99J06_weakSolution M f u) := by
  refine ⟨apm_m99J06_weak_iff_strong M f hf, ?_⟩
  intro V hfinite hnested hdense
  letI (n : ℕ) : FiniteDimensional ℝ (V n) := hfinite n
  refine ⟨fun n ↦ apm_m99J06_galerkin_exists_unique M f hf (V n), ?_⟩
  intro uSeq heq
  have hbound : ∀ n,
      ‖(uSeq n : H)‖ ≤ (eLpNorm f 2 apm_m99J06_intervalMeasure).toReal :=
    fun n ↦ apm_m99J06_galerkin_norm_le M f hf (V n) (uSeq n) (heq n)
  obtain ⟨u, hu, _⟩ := apm_m99J06_weakSolution_exists_unique M f hf
  have hproj : ∀ n, (uSeq n : H) = (V n).starProjection u := fun n ↦
    apm_m99J06_galerkin_eq_starProjection M f (V n) u hu (uSeq n) (heq n)
  have hconv :=
    apm_m99J06_starProjection_convergence V hnested hdense uSeq u hproj
  exact ⟨hbound, u, hconv.2, hu⟩

#print axioms apm_m99j06
