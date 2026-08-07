import Mathlib

open Filter MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

/-!
# APM a99J02

## Statement repairs

The source's `E \leq [0,1]` is read as the intended set containment
`E \subseteq [0,1]`; numerical order between a set and an interval is ill-typed.

## Encoding notes

`apmTranslate E t` is exactly the image `{x+t | x ∈ E}`, and
`apmIndicatorConvolution` is the displayed Lebesgue integral on all of `ℝ`.
-/

def apmIndicator (E : Set ℝ) : ℝ → ℝ :=
  E.indicator (fun _ ↦ 1)

noncomputable def apmIndicatorConvolution (E : Set ℝ) (x : ℝ) : ℝ :=
  ∫ y, apmIndicator E (x - y) * apmIndicator E y ∂volume

def apmTranslate (E : Set ℝ) (t : ℝ) : Set ℝ :=
  (fun x ↦ x + t) '' E

lemma apmIndicator_memLp_two
    {E : Set ℝ} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤) :
    MemLp (apmIndicator E) 2 volume := by
  simpa [apmIndicator] using
    memLp_indicator_const (2 : ENNReal) hE (1 : ℝ) (Or.inr hEfin)

lemma apm_exists_ball_subset_sub
    {E : Set ℝ} (hE : MeasurableSet E) (hEpos : 0 < volume E) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → t ∈ E - E := by
  have hnhds : E - E ∈ 𝓝 (0 : ℝ) :=
    MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos volume E hE hEpos
  rcases Metric.mem_nhds_iff.1 hnhds with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro t ht
  exact hball (by simpa [Real.dist_eq] using ht)

theorem apm_a99j02
    {E : Set ℝ}
    (hE_measurable : MeasurableSet E)
    (hE_interval : E ⊆ Icc (0 : ℝ) 1)
    (hE_positive : 0 < volume E) :
    Continuous (apmIndicatorConvolution E) ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∀ t : ℝ, |t| < ε → 0 < volume (E ∩ apmTranslate E t) := by
  /-
  PARTIAL boundary (closer hop 1).

  Two dependencies missed by the original pass are now isolated. First,
  `apmIndicator_memLp_two` packages the finite-measure indicator in L².
  Second, Mathlib already contains Steinhaus's theorem as
  `MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos`; the compiled lemma
  `apm_exists_ball_subset_sub` extracts an explicit ε-ball contained in
  `E-E`. This proves nearby translates have nonempty overlap, though the
  frozen conclusion needs positive-measure overlap.

  Closed sibling `a96J02` supplies the exact analytic machinery:
  `continuous_convolution_indicator` proves indicator convolution continuity,
  while its `continuous_overlapMeasure` uses continuity in symmetric-difference
  measure. The sibling also proves the convolution/overlap identity. These
  declarations live only in its problem file and are not importable modules;
  closing here requires promoting/copying that measured-set development and
  adapting the orientation from the preimage `{y | t-y ∈ E}` to the frozen
  image translate `E+t`. The first frozen convolution uses `E*E`, whereas the
  overlap uses the reflected indicator, so they are related applications of
  the same L² convolution-continuity theorem rather than literally one
  function.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, Mathlib Haar/Steinhaus,
  convolution, translation/symmetric-difference APIs, closed artifacts, and
  git history found no importable theorem completing that orientation and
  positive-measure transport. No statement defect was found.
  -/
  sorry
