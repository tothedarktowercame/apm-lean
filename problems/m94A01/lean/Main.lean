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

theorem apm_m94a01 (u : ℝ × ℝ → ℝ)
    (hu : ContDiff ℝ 4 u) :
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
  have hfx : ContDiff ℝ 4 fx := apm_m94a01_contDiff_slice_fst u hu y
  have hfy : ContDiff ℝ 4 fy := apm_m94a01_contDiff_slice_snd u hu x
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
