import Mathlib

open Filter Asymptotics
open scoped Topology

/-!
# APM m94A01 — five-point Laplacian error

## Statement repairs

Continuity of the fourth derivatives gives a local bound, not a uniform global
constant on `ℝ²`.  The claimed estimate is therefore stated locally at each
point for sufficiently small `h`.
-/
noncomputable def apm_m94a01_T (u : ℝ × ℝ → ℝ) (h x y : ℝ) : ℝ :=
  (u (x+h,y)+u (x-h,y)+u (x,y+h)+u (x,y-h)-4*u (x,y))/h^2

noncomputable def apm_m94a01_laplacian (u : ℝ × ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (deriv fun s => u (s,y)) x + deriv (deriv fun s => u (x,s)) y

lemma apm_m94a01_taylor4_isLittleO
    (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (x : ℝ) :
    (fun h : ℝ ↦ f (x + h) -
      (f x + h * iteratedDeriv 1 f x + h ^ 2 / 2 * iteratedDeriv 2 f x +
        h ^ 3 / 6 * iteratedDeriv 3 f x + h ^ 4 / 24 * iteratedDeriv 4 f x))
      =o[nhds 0] (fun h : ℝ ↦ h ^ 4) := by
  have ht : Tendsto (fun h : ℝ ↦ x + h) (nhds 0) (nhds x) := by
    simpa using (tendsto_const_nhds.add tendsto_id :
      Tendsto (fun h : ℝ ↦ x + h) (nhds 0) (nhds (x + 0)))
  have h := (taylor_isLittleO_univ hf (x₀ := x)).comp_tendsto ht
  convert h using 1
  · funext z
    simp [taylor_within_apply, iteratedDerivWithin_univ]
    ring
  · funext z
    simp

lemma apm_m94a01_centered2_isBigO
    (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (x : ℝ) :
    (fun h : ℝ ↦ f (x + h) + f (x - h) - 2 * f x -
      h ^ 2 * iteratedDeriv 2 f x) =O[nhds 0] (fun h : ℝ ↦ h ^ 4) := by
  have hp := apm_m94a01_taylor4_isLittleO f hf x
  have ht : Tendsto (fun h : ℝ ↦ -h) (nhds 0) (nhds 0) := by
    simpa using (tendsto_id.neg : Tendsto (fun h : ℝ ↦ -h) (nhds 0) (nhds (-0)))
  have hm0 := (apm_m94a01_taylor4_isLittleO f hf x).comp_tendsto ht
  have hm :
      (fun h : ℝ ↦ f (x - h) -
        (f x + (-h) * iteratedDeriv 1 f x +
          (-h) ^ 2 / 2 * iteratedDeriv 2 f x +
          (-h) ^ 3 / 6 * iteratedDeriv 3 f x +
          (-h) ^ 4 / 24 * iteratedDeriv 4 f x))
        =o[nhds 0] (fun h : ℝ ↦ h ^ 4) := by
    convert hm0 using 1 <;> funext h <;> simp <;> ring
  have hs := (hp.add hm).isBigO
  have hterm :
      (fun h : ℝ ↦ h ^ 4 / 12 * iteratedDeriv 4 f x)
        =O[nhds 0] (fun h : ℝ ↦ h ^ 4) := by
    convert (isBigO_refl (fun h : ℝ ↦ h ^ 4) (nhds 0)).const_mul_left
      (iteratedDeriv 4 f x / 12) using 1
    funext h
    ring
  convert hs.add hterm using 1
  funext h
  ring

lemma apm_m94a01_contDiff_slice_fst
    (u : ℝ × ℝ → ℝ) (hu : ContDiff ℝ 4 u) (y : ℝ) :
    ContDiff ℝ 4 (fun s : ℝ => u (s, y)) := by
  exact hu.comp (contDiff_id.prodMk contDiff_const)

lemma apm_m94a01_contDiff_slice_snd
    (u : ℝ × ℝ → ℝ) (hu : ContDiff ℝ 4 u) (x : ℝ) :
    ContDiff ℝ 4 (fun s : ℝ => u (x, s)) := by
  exact hu.comp (contDiff_const.prodMk contDiff_id)

lemma apm_m94a01_iteratedDeriv_two (f : ℝ → ℝ) :
    iteratedDeriv 2 f = deriv (deriv f) := by
  calc
    iteratedDeriv 2 f = iteratedDeriv (1 + 1) f := by norm_num
    _ = deriv (iteratedDeriv 1 f) := iteratedDeriv_succ
    _ = deriv (deriv f) := by rw [iteratedDeriv_one]

theorem apm_m94a01_of_contDiff_slices (u : ℝ × ℝ → ℝ)
    (hux : ∀ y : ℝ, ContDiff ℝ 4 (fun s : ℝ => u (s, y)))
    (huy : ∀ x : ℝ, ContDiff ℝ 4 (fun s : ℝ => u (x, s))) :
    ∀ x y : ℝ, ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ h : ℝ, 0 < |h| → |h| < δ →
        |apm_m94a01_laplacian u x y - apm_m94a01_T u h x y| ≤ C*h^2 := by
  /-
  CLOSER HOP 1 (partial). The reusable one-dimensional analytic core is now
  compiled. `apm_m94a01_taylor4_isLittleO` uses
  `taylor_isLittleO_univ`, and `apm_m94a01_centered2_isBigO` composes with
  negation, cancels the odd terms, and proves the exact central-difference
  remainder is `O(h^4)`.

  The remaining boundary applies this estimate separately
  to the coordinate slices `s ↦ u (s, y)` and `s ↦ u (x, s)`, adds the
  `+h` and `-h` formulas to cancel odd terms, and divides the combined
  fourth-order remainder by `h ^ 2`.

  The earlier search of Mathlib's Taylor APIs `taylor_mean_remainder_bound`,
  `exists_taylor_mean_remainder_bound`, and
  `taylor_mean_remainder_lagrange_iteratedDeriv`. They provide the needed
  interval-wise estimates, but I did not complete the bridge from
  `ContDiff ℝ 4 u` to `ContDiffOn` for both coordinate slices, rewrite the
  `taylorWithinEval` coefficients as the nested `deriv` expressions used by
  `apm_m94a01_laplacian`, or combine the two locally chosen derivative bounds
  into the exact `C, δ` conclusion after division by nonzero `h ^ 2`. No
  compiled sibling supplied this slice-Taylor normalization within this pass.
  Renewed inspection found the completed `m93J01` helper pattern above; the
  live bridge is now only the two coordinate-slice `ContDiff` facts, rewriting
  `iteratedDeriv 2` as the nested `deriv` in the frozen Laplacian, and
  converting the combined `O(h^4)` estimate after division by `h^2` into the
  explicit local `C, δ` inequality.

  Closer hop 2 closes that bridge. The two slice lemmas compose `hu` with the
  coordinate embeddings, `apm_m94a01_iteratedDeriv_two` performs the exact
  Laplacian normalization, and `IsBigO.exists_nonneg` supplies one common
  constant and neighborhood for the sum of the two centered remainders.
  `Metric.eventually_nhds_iff` extracts `δ`; division by `h²` is justified by
  `0 < |h|`, and the remaining expression is polynomial normalization.
  -/
  intro x y
  let fx : ℝ → ℝ := fun s => u (s, y)
  let fy : ℝ → ℝ := fun s => u (x, s)
  have hfx : ContDiff ℝ 4 fx := hux y
  have hfy : ContDiff ℝ 4 fy := huy x
  have hO := (apm_m94a01_centered2_isBigO fx hfx x).add
    (apm_m94a01_centered2_isBigO fy hfy y)
  rcases hO.exists_nonneg with ⟨C, hC, hOC⟩
  have hev := hOC.bound
  rw [Metric.eventually_nhds_iff] at hev
  rcases hev with ⟨δ, hδ, hbound⟩
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro h hhpos hhδ
  have hh : h ≠ 0 := by
    intro hz
    simp [hz] at hhpos
  have hb := hbound (show dist h (0 : ℝ) < δ by
    simpa [Real.dist_eq] using hhδ)
  have hrewrite : apm_m94a01_laplacian u x y - apm_m94a01_T u h x y =
      -((fx (x + h) + fx (x - h) - 2 * fx x - h ^ 2 * iteratedDeriv 2 fx x) +
        (fy (y + h) + fy (y - h) - 2 * fy y - h ^ 2 * iteratedDeriv 2 fy y)) /
        h ^ 2 := by
    simp only [apm_m94a01_laplacian, apm_m94a01_T, fx, fy,
      apm_m94a01_iteratedDeriv_two]
    field_simp
    ring
  rw [hrewrite, abs_div, abs_neg, abs_sq]
  rw [div_le_iff₀ (sq_pos_of_ne_zero hh)]
  calc
    _ ≤ C * |h| ^ 4 := by simpa only [Real.norm_eq_abs, abs_pow] using hb
    _ = C * h ^ 2 * h ^ 2 := by
      rw [show |h| ^ 4 = (|h| ^ 2) ^ 2 by ring, sq_abs]
      ring

theorem apm_m94a01_contDiff (u : ℝ × ℝ → ℝ)
    (hu : ContDiff ℝ 4 u) :
    ∀ x y : ℝ, ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ h : ℝ, 0 < |h| → |h| < δ →
        |apm_m94a01_laplacian u x y - apm_m94a01_T u h x y| ≤ C*h^2 := by
  apply apm_m94a01_of_contDiff_slices u
  · exact fun y => apm_m94a01_contDiff_slice_fst u hu y
  · exact fun x => apm_m94a01_contDiff_slice_snd u hu x

lemma apm_m94a01_centered2_bound
    (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (x t M : ℝ)
    (ht : 0 < t) (hM : ∀ z : ℝ, |z - x| ≤ t → |iteratedDeriv 4 f z| ≤ M) :
    |f (x + t) + f (x - t) - 2 * f x - t ^ 2 * iteratedDeriv 2 f x| ≤
      M * t ^ 4 / 12 := by
  obtain ⟨zp, hzp, hp⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 3) (show x < x + t by linarith)
      hf.contDiffOn
  obtain ⟨wm, hwm, hm⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := fun s => f (-s)) (n := 3)
      (show -x < -x + t by linarith) (hf.comp (by fun_prop)).contDiffOn
  let zm := -wm
  have hzp' : |zp - x| ≤ t := by
    rw [abs_of_nonneg (sub_nonneg.mpr hzp.1.le)]
    linarith [hzp.2]
  have hzm' : |zm - x| ≤ t := by
    dsimp [zm]
    rw [show -wm - x = -(wm - -x) by ring, abs_neg,
      abs_of_nonneg (sub_nonneg.mpr hwm.1.le)]
    linarith [hwm.2]
  have hp' : f (x + t) =
      f x + t * iteratedDeriv 1 f x + t ^ 2 / 2 * iteratedDeriv 2 f x +
        t ^ 3 / 6 * iteratedDeriv 3 f x + iteratedDeriv 4 f zp * t ^ 4 / 24 := by
    rw [taylor_within_apply] at hp
    have hu := uniqueDiffOn_Icc (show x < x + t by linarith)
    have h0 := iteratedDerivWithin_eq_iteratedDeriv (n := 0) hu
      (hf.contDiffAt.of_le (by norm_num)) ⟨le_rfl, le_add_of_nonneg_right ht.le⟩
    have h1 := iteratedDerivWithin_eq_iteratedDeriv (n := 1) hu
      (hf.contDiffAt.of_le (by norm_num)) ⟨le_rfl, le_add_of_nonneg_right ht.le⟩
    have h2 := iteratedDerivWithin_eq_iteratedDeriv (n := 2) hu
      (hf.contDiffAt.of_le (by norm_num)) ⟨le_rfl, le_add_of_nonneg_right ht.le⟩
    have h3 := iteratedDerivWithin_eq_iteratedDeriv (n := 3) hu
      (hf.contDiffAt.of_le (by norm_num)) ⟨le_rfl, le_add_of_nonneg_right ht.le⟩
    norm_num [Finset.sum_range_succ, h0, h1, h2, h3] at hp ⊢
    linarith
  have hm' : f (x - t) =
      f x - t * iteratedDeriv 1 f x + t ^ 2 / 2 * iteratedDeriv 2 f x -
        t ^ 3 / 6 * iteratedDeriv 3 f x + iteratedDeriv 4 f zm * t ^ 4 / 24 := by
    rw [taylor_within_apply] at hm
    let g : ℝ → ℝ := fun s => f (-s)
    have hg : ContDiff ℝ 4 g := hf.comp (by fun_prop)
    have hu := uniqueDiffOn_Icc (show -x < -x + t by linarith)
    have hbase : -x ∈ Set.Icc (-x) (-x + t) :=
      ⟨le_rfl, le_add_of_nonneg_right ht.le⟩
    have h0 := iteratedDerivWithin_eq_iteratedDeriv (n := 0) hu
      (hg.contDiffAt.of_le (by norm_num)) hbase
    have h1 := iteratedDerivWithin_eq_iteratedDeriv (n := 1) hu
      (hg.contDiffAt.of_le (by norm_num)) hbase
    have h2 := iteratedDerivWithin_eq_iteratedDeriv (n := 2) hu
      (hg.contDiffAt.of_le (by norm_num)) hbase
    have h3 := iteratedDerivWithin_eq_iteratedDeriv (n := 3) hu
      (hg.contDiffAt.of_le (by norm_num)) hbase
    norm_num [Finset.sum_range_succ, h0, h1, h2, h3, g, iteratedDeriv_comp_neg] at hm ⊢
    dsimp [zm]
    rw [show x - t = -t + x by ring]
    linear_combination hm
  rw [hp', hm']
  have hsum : |iteratedDeriv 4 f zp + iteratedDeriv 4 f zm| ≤ 2 * M := by
    calc
      _ ≤ |iteratedDeriv 4 f zp| + |iteratedDeriv 4 f zm| := abs_add_le _ _
      _ ≤ M + M := add_le_add (hM zp hzp') (hM zm hzm')
      _ = 2 * M := by ring
  rw [show f x + t * iteratedDeriv 1 f x + t ^ 2 / 2 * iteratedDeriv 2 f x +
        t ^ 3 / 6 * iteratedDeriv 3 f x + iteratedDeriv 4 f zp * t ^ 4 / 24 +
        (f x - t * iteratedDeriv 1 f x + t ^ 2 / 2 * iteratedDeriv 2 f x -
          t ^ 3 / 6 * iteratedDeriv 3 f x + iteratedDeriv 4 f zm * t ^ 4 / 24) -
        2 * f x - t ^ 2 * iteratedDeriv 2 f x =
      (iteratedDeriv 4 f zp + iteratedDeriv 4 f zm) * t ^ 4 / 24 by ring]
  rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 24), abs_pow,
    abs_of_pos ht]
  nlinarith [hsum, sq_nonneg (t ^ 2)]

theorem apm_m94a01 (u : ℝ × ℝ → ℝ)
    (hux : ∀ y : ℝ, ContDiff ℝ 4 (fun s : ℝ => u (s, y)))
    (huy : ∀ x : ℝ, ContDiff ℝ 4 (fun s : ℝ => u (x, s)))
    (hux4 : Continuous (fun p : ℝ × ℝ =>
      iteratedDeriv 4 (fun s : ℝ => u (s, p.2)) p.1))
    (huy4 : Continuous (fun p : ℝ × ℝ =>
      iteratedDeriv 4 (fun s : ℝ => u (p.1, s)) p.2)) :
    ∀ K : Set (ℝ × ℝ), IsCompact K →
      ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
        ∀ x y : ℝ, (x, y) ∈ K → ∀ h : ℝ, 0 < |h| → |h| < δ →
          |apm_m94a01_laplacian u x y - apm_m94a01_T u h x y| ≤ C * h^2 := by
  intro K hK
  let L : Set (ℝ × ℝ) := Metric.cthickening 1 K
  have hL : IsCompact L := hK.cthickening
  obtain ⟨Ax, hAx⟩ := hL.exists_bound_of_continuousOn hux4.continuousOn
  obtain ⟨Ay, hAy⟩ := hL.exists_bound_of_continuousOn huy4.continuousOn
  let Mx := max 0 Ax
  let My := max 0 Ay
  have hMx : ∀ p ∈ L, ‖iteratedDeriv 4 (fun s => u (s, p.2)) p.1‖ ≤ Mx :=
    fun p hp => (hAx p hp).trans (le_max_right _ _)
  have hMy : ∀ p ∈ L, ‖iteratedDeriv 4 (fun s => u (p.1, s)) p.2‖ ≤ My :=
    fun p hp => (hAy p hp).trans (le_max_right _ _)
  refine ⟨(Mx + My) / 12, 1, ?_, zero_lt_one, ?_⟩
  · have hx0 : 0 ≤ Mx := le_max_left _ _
    have hy0 : 0 ≤ My := le_max_left _ _
    positivity
  intro x y hxy h hhpos hh1
  let t := |h|
  have ht : 0 < t := hhpos
  have hbx := apm_m94a01_centered2_bound (fun s => u (s, y)) (hux y) x t Mx ht
    (fun z hz => hMx (z, y) (Metric.mem_cthickening_of_dist_le (z, y) (x, y) 1 K hxy (by
      rw [Prod.dist_eq, max_le_iff]
      constructor
      · simpa [Real.dist_eq] using hz.trans hh1.le
      · simp)))
  have hby := apm_m94a01_centered2_bound (fun s => u (x, s)) (huy x) y t My ht
    (fun z hz => hMy (x, z) (Metric.mem_cthickening_of_dist_le (x, z) (x, y) 1 K hxy (by
      rw [Prod.dist_eq, max_le_iff]
      constructor
      · simp
      · simpa [Real.dist_eq] using hz.trans hh1.le)))
  have hh : h ≠ 0 := by aesop
  have hrewrite : apm_m94a01_laplacian u x y - apm_m94a01_T u h x y =
      -(((u (x + t, y) + u (x - t, y) - 2 * u (x, y) -
          t ^ 2 * iteratedDeriv 2 (fun s => u (s, y)) x) +
        (u (x, y + t) + u (x, y - t) - 2 * u (x, y) -
          t ^ 2 * iteratedDeriv 2 (fun s => u (x, s)) y)) / t ^ 2) := by
    simp only [apm_m94a01_laplacian, apm_m94a01_T,
      apm_m94a01_iteratedDeriv_two, t]
    rw [sq_abs]
    rcases le_total 0 h with hh' | hh'
    · rw [abs_of_nonneg hh']
      field_simp [hh] <;> ring
    · rw [abs_of_nonpos hh']
      simp only [sub_neg_eq_add, add_comm]
      field_simp [hh] <;> ring
  rw [hrewrite, abs_neg, abs_div, abs_sq]
  rw [div_le_iff₀ (sq_pos_of_pos ht)]
  calc
    _ ≤ Mx * t ^ 4 / 12 + My * t ^ 4 / 12 := (abs_add_le _ _).trans (add_le_add hbx hby)
    _ = (Mx + My) / 12 * h ^ 2 * t ^ 2 := by
      have : t ^ 2 = h ^ 2 := by simp [t]
      rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, this]
      ring
