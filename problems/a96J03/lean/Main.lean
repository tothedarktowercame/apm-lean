import Mathlib

/-!
# APM a96J03

## Statement repairs

None.

## Encoding questions

None. Membership in `L¹(ℝ, μ)` is expressed for the given representative by
`MeasureTheory.Integrable f volume`, and the displayed limit is encoded
directly with the neighborhood filter at zero.
-/

open MeasureTheory Filter

/-- Translation by a real number preserves the `L¹` distance.  This is the
Haar-invariance estimate used in the density argument below. -/
lemma apm_a96J03_integral_abs_sub_translate (f g : ℝ → ℝ) (t : ℝ) :
    (∫ x : ℝ, |f (x - t) - g (x - t)|) = ∫ x : ℝ, |f x - g x| := by
  simpa only using
    (integral_sub_right_eq_self (fun x : ℝ ↦ |f x - g x|) t)

/-- Continuous compactly supported functions approximate an integrable real
function in the exact integral metric appearing in the theorem. -/
lemma apm_a96J03_exists_compact_continuous_approx (f : ℝ → ℝ)
    (hf : Integrable f volume) {e : ℝ} (he : 0 < e) :
    ∃ g : ℝ → ℝ, HasCompactSupport g ∧ Continuous g ∧ Integrable g volume ∧
      (∫ x : ℝ, |f x - g x|) ≤ e := by
  obtain ⟨g, hg, hfg, hgc, hgi⟩ :=
    hf.exists_hasCompactSupport_integral_sub_le he
  exact ⟨g, hg, hgc, hgi, by simpa only [Real.norm_eq_abs] using hfg⟩

theorem apm_a96j03 (f : ℝ → ℝ) (hf : Integrable f volume) :
    Tendsto
      (fun t : ℝ => ∫ x : ℝ, |f (x - t) - f x|)
      (nhds 0) (nhds 0) := by
  /- CLOSER HOP 1 BOUNDARY.

  Repository and Mathlib searches found no packaged strong-continuity theorem
  for translations on `L¹`.  The two reusable reduction lemmas above now
  compile the exact density route: Mathlib's
  `Integrable.exists_hasCompactSupport_integral_sub_le` supplies a continuous
  compactly supported approximant in the displayed integral metric, and
  `integral_sub_right_eq_self` proves that both translated approximation
  errors have the same size.

  The remaining bridge is the compact-support core: for continuous compactly
  supported `g`, prove
  `∫ x, |g (x - t) - g x| → 0`.  A direct dominated-convergence proof must
  thicken `tsupport g` by a compact neighborhood of zero, dominate all nearby
  translates by a bounded multiple of that compact set's indicator, and then
  discharge the resulting support, measurability, and integrability facts.
  Mathlib's convolution continuity theorems were also inspected, but they do
  not directly express this translation norm.  No solved sibling or
  `ConstructionTargets` module packages that final compact-support assembly.
  The frozen statement is unchanged.
  -/
  sorry
