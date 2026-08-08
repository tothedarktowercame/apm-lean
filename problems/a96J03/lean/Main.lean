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
open scoped Pointwise

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

/-- Translation is continuous in the integral metric for continuous,
compactly supported functions.  The uniformly compact support over
`t ∈ closedBall 0 1` is `tsupport g + closedBall 0 1`. -/
lemma apm_a96J03_compact_core (g : ℝ → ℝ)
    (hg : HasCompactSupport g) (hgc : Continuous g) :
    Tendsto (fun t : ℝ => ∫ x : ℝ, |g (x - t) - g x|)
      (nhds 0) (nhds 0) := by
  let s : Set ℝ := Metric.closedBall 0 1
  let k : Set ℝ := tsupport g + s
  have hs : IsCompact s := isCompact_closedBall 0 1
  have hk : IsCompact k := IsCompact.add hg hs
  have hjoint : Continuous (Function.uncurry fun t x : ℝ => |g (x - t) - g x|) := by
    fun_prop
  have hzero : ∀ t x : ℝ, t ∈ s → x ∉ k → |g (x - t) - g x| = 0 := by
    intro t x ht hx
    have hxt : x - t ∉ tsupport g := by
      intro hmem
      apply hx
      refine ⟨x - t, hmem, t, ht, ?_⟩
      ring
    have hxg : x ∉ tsupport g := by
      intro hmem
      apply hx
      refine ⟨x, hmem, 0, ?_, by simp⟩
      change dist (0 : ℝ) 0 ≤ 1
      simp
    simp [image_eq_zero_of_notMem_tsupport hxt,
      image_eq_zero_of_notMem_tsupport hxg]
  have hcont : ContinuousOn
      (fun t : ℝ => ∫ x : ℝ, |g (x - t) - g x|) s :=
    continuousOn_integral_of_compact_support hk hjoint.continuousOn
      (fun t x ht hx => hzero t x ht hx)
  have hsnhds : s ∈ nhds (0 : ℝ) := by
    exact Metric.closedBall_mem_nhds 0 (by norm_num)
  have hat : ContinuousAt (fun t : ℝ => ∫ x : ℝ, |g (x - t) - g x|) 0 :=
    (hcont 0 (by simp [s])).continuousAt hsnhds
  have hval : (fun t : ℝ => ∫ x : ℝ, |g (x - t) - g x|) 0 = 0 := by simp
  have hat' : Tendsto (fun t : ℝ => ∫ x : ℝ, |g (x - t) - g x|)
      (nhds 0) (nhds ((fun t : ℝ => ∫ x : ℝ, |g (x - t) - g x|) 0)) := hat
  rw [hval] at hat'
  exact hat'

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

  CLOSER HOP 2 closes the compact-support core in
  `apm_a96J03_compact_core`. The previously missed theorem
  `continuousOn_integral_of_compact_support` applies to the jointly continuous
  family `|g (x-t)-g x|`; for `t ∈ closedBall 0 1`, its uniform compact
  support is `tsupport g + closedBall 0 1`. This avoids all manual dominated-
  convergence bookkeeping.

  The remaining bridge is now only the final epsilon/triangle assembly:
  choose the compiled compactly supported approximant, use Haar invariance for
  both approximation-error translates, and combine those two errors with the
  compact-core bound. No packaged integral-metric triangle lemma was found in
  the renewed `L1`, Haar, and Bochner-integral searches. The frozen statement
  is unchanged.
  -/
  sorry
