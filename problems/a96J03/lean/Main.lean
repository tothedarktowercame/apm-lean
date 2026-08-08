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
  /- CLOSER HOPS 1--3.

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

  Hop 3 closes the final epsilon/triangle assembly directly. It chooses an
  `ε/3` compactly supported approximant, takes the eventual compact-core
  bound, proves the pointwise three-term absolute-value inequality, supplies
  integrability for every term, splits the integral, and uses Haar invariance
  for the translated approximation error. The frozen statement is unchanged.
  -/
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨g, hg, hgc, hgi, hfg⟩ :=
    apm_a96J03_exists_compact_continuous_approx f hf (show 0 < ε / 3 by positivity)
  have hcore := apm_a96J03_compact_core g hg hgc
  rw [Metric.tendsto_nhds] at hcore
  filter_upwards [hcore (ε / 3) (by positivity)] with t ht
  rw [Real.dist_eq, sub_zero, abs_of_nonneg]
  · have hft : Integrable (fun x : ℝ ↦ f (x - t)) volume := hf.comp_sub_right t
    have hgt : Integrable (fun x : ℝ ↦ g (x - t)) volume := hgi.comp_sub_right t
    have hleft : Integrable (fun x : ℝ ↦ |f (x - t) - g (x - t)|) volume :=
      (hft.sub hgt).abs
    have hmid : Integrable (fun x : ℝ ↦ |g (x - t) - g x|) volume :=
      (hgt.sub hgi).abs
    have hright : Integrable (fun x : ℝ ↦ |g x - f x|) volume :=
      (hgi.sub hf).abs
    have hmono :
        (∫ x : ℝ, |f (x - t) - f x|) ≤
          ∫ x : ℝ, |f (x - t) - g (x - t)| +
            |g (x - t) - g x| + |g x - f x| := by
      apply integral_mono
      · exact (hft.sub hf).abs
      · exact (hleft.add hmid).add hright
      · intro x
        calc
          |f (x - t) - f x| ≤
              |f (x - t) - g (x - t)| + |g (x - t) - f x| := abs_sub_le _ _ _
          _ ≤ |f (x - t) - g (x - t)| +
              (|g (x - t) - g x| + |g x - f x|) :=
                add_le_add (le_refl _) (abs_sub_le (g (x - t)) (g x) (f x))
          _ = |f (x - t) - g (x - t)| +
              |g (x - t) - g x| + |g x - f x| := by ring
    have hrhs :
        (∫ x : ℝ, |f (x - t) - g (x - t)| +
            |g (x - t) - g x| + |g x - f x|) =
          (∫ x : ℝ, |f (x - t) - g (x - t)|) +
          (∫ x : ℝ, |g (x - t) - g x|) +
          (∫ x : ℝ, |g x - f x|) := by
      calc
        _ = (∫ x : ℝ, (|f (x - t) - g (x - t)| +
              |g (x - t) - g x|) + |g x - f x|) := rfl
        _ = (∫ x : ℝ, |f (x - t) - g (x - t)| +
              |g (x - t) - g x|) + (∫ x : ℝ, |g x - f x|) :=
                integral_add (hleft.add hmid) hright
        _ = _ := by rw [integral_add hleft hmid]
    rw [hrhs, apm_a96J03_integral_abs_sub_translate f g t] at hmono
    have hgf : (∫ x : ℝ, |g x - f x|) = ∫ x : ℝ, |f x - g x| := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [abs_sub_comm]
    rw [hgf] at hmono
    have ht' : (∫ x : ℝ, |g (x - t) - g x|) < ε / 3 := by
      simpa [Real.dist_eq, abs_of_nonneg (integral_nonneg fun _ ↦ abs_nonneg _)] using ht
    exact lt_of_le_of_lt hmono (by linarith)
  · exact integral_nonneg fun _ ↦ abs_nonneg _
