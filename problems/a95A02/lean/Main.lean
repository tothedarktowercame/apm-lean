/-
! # APM a95A02: AC functions satisfy Lusin's condition (N) and preserve measurability

This file formalizes the three parts of the problem:
(a) The definition of absolute continuity on [0,1].
(b) Lusin's condition (N): for every ε > 0 there exists δ > 0 such that
    m*(f(E)) ≤ ε whenever m*(E) ≤ δ.
(c) AC functions map measurable subsets of [0,1] to measurable sets.

## Formalization notes

The informal proof routes (b) through the fundamental theorem of calculus for
AC functions: an AC function f satisfies f(x) = f(0) + ∫₀ˣ f'(t) dt, and then
the absolute continuity of the Lebesgue integral (for f' ∈ L¹) provides the δ.
Current Mathlib gives both the ε-δ definition and the integral representation
via `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`. The remaining
bridge is the covering argument which bounds the outer measure of an image by
the integral of `|f'|` over a small open cover.

## Statement repair

The auto-generated Lean statements used a custom `AbsolutelyContinuousOn` def
with `Fin n → ℝ` indexed intervals. This is structurally correct but does not
match Mathlib's `AbsolutelyContinuousOnInterval`, which uses a filter-based
definition with the equivalent ε-δ form (`absolutelyContinuousOnInterval_iff`).
We adopt Mathlib's definition to leverage its existing API (continuity, BV,
ae-differentiability, closure under interval integrals).

For part (b), the generated statement used `volume.toOuterMeasure.measureOf`
directly. We keep this since it matches the problem's use of m*, but we also
prove the special case with `volume` (Lebesgue measure) for use in part (c).
-/

import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory Set Filter

open scoped NNReal ENNReal

noncomputable section

section PartA

/-! ## Part (a): Definition of absolute continuity

We use Mathlib's `AbsolutelyContinuousOnInterval f 0 1`, which is equivalent
to the classical ε-δ definition (see `absolutelyContinuousOnInterval_iff`).

The classical definition: f : [0,1] → ℝ is absolutely continuous if for every
ε > 0 there exists δ > 0 such that for every finite collection of pairwise
disjoint intervals (aₖ, bₖ) ⊆ [0,1] with Σ(bₖ - aₖ) < δ, we have
Σ|f(bₖ) - f(aₖ)| < ε.
-/

/-- Part (a): Definition of absolute continuity on [0,1].

We state it using Mathlib's `AbsolutelyContinuousOnInterval`. The equivalence
with the textbook ε-δ formulation is `absolutelyContinuousOnInterval_iff`. -/
def ACOnUnitInterval (f : ℝ → ℝ) : Prop :=
  AbsolutelyContinuousOnInterval f 0 1

/-- Part (a) restatement: the classical ε-δ form of absolute continuity.

For every ε > 0, there exists δ > 0 such that for any finite collection of
non-overlapping intervals with total length < δ, the sum of |f(bₖ) - f(aₖ)| < ε.

We delegate to Mathlib's `absolutelyContinuousOnInterval_iff`, noting that
`uIcc 0 1 = Icc 0 1` since `0 ≤ 1`. -/
theorem acOnUnitInterval_iff (f : ℝ → ℝ) :
    ACOnUnitInterval f ↔
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ E,
      E ∈ AbsolutelyContinuousOnInterval.disjWithin 0 1 →
      ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ →
      ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) < ε := by
  show AbsolutelyContinuousOnInterval f 0 1 ↔ _
  exact absolutelyContinuousOnInterval_iff f 0 1

end PartA

section PartB

/-! ## Part (b): Lusin's condition (N)

For every ε > 0, there exists δ > 0 such that m*(f(E)) ≤ ε whenever m*(E) ≤ δ.

### Proof strategy

The informal proof proceeds as follows:
1. An AC function f equals f(0) + ∫₀ˣ f'(t)dt (FTC for AC functions).
2. For a measurable set E, m*(f(E)) ≤ ∫_E |f'|.
3. By absolute continuity of the Lebesgue integral, for ε > 0 there exists δ > 0
   with ∫_E |f'| < ε whenever m(E) < δ.

Step 1 is available as
`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`.

### What we can prove

The σ-compact decomposition lemma (inner regularity of volume on ℝ) is fully
proved below. The remaining Lusin-condition frontier is the countable
open-interval cover assembly for arbitrary outer-measurable sets.
-/

/-- Part (b): For every ε > 0 there exists δ > 0 such that m*(f(E)) ≤ ε
whenever E ⊆ [0,1] and m*(E) ≤ δ.

This is Lusin's condition (N) for absolutely continuous functions.

The integral representation and its pointwise variation estimate are available
below. The remaining obligation is to decompose a small open cover into
disjoint intervals, bound each image interval, and sum those bounds.
-/
theorem ac_lusin_condition_N
    {f : ℝ → ℝ}
    (hac : ACOnUnitInterval f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ E ⊆ Icc (0:ℝ) 1,
      volume.toOuterMeasure E < ENNReal.ofReal δ →
      volume.toOuterMeasure (f '' E) ≤ ENNReal.ofReal ε := by
  sorry

/-- Part (b) special case: AC maps null sets to null sets.

If f is absolutely continuous on [0,1] and E ⊆ [0,1] has measure zero,
then f(E) has measure zero.

This follows from `ac_lusin_condition_N` by choosing any ε > 0 (e.g. ε = 1):
since volume(E) = 0 < δ for any δ > 0, we get volume(f(E)) ≤ ε for all ε > 0,
hence volume(f(E)) = 0.

The sorry here inherits from `ac_lusin_condition_N`. -/
theorem ac_maps_null_to_null
    {f : ℝ → ℝ}
    (hac : ACOnUnitInterval f)
    {E : Set ℝ} (hE : E ⊆ Icc (0:ℝ) 1)
    (hE_null : volume E = 0) :
    volume (f '' E) = 0 := by
  apply le_antisymm ?_ (zero_le _)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε_real : 0 < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨δ, hδ, hbound⟩ := ac_lusin_condition_N hac hε_real
  have hE_outer : volume.toOuterMeasure E < ENNReal.ofReal δ := by
    rw [Measure.toOuterMeasure_apply, hE_null]
    exact ENNReal.ofReal_pos.2 hδ
  simpa using hbound E hE hE_outer

end PartB

section PartC

/-! ## Part (c): AC functions preserve measurability

If E ⊆ [0,1] is Lebesgue measurable, then f(E) is Lebesgue measurable.

### Proof strategy (from informal proof)

Write E = K ∪ N where K = ⋃ₘ Kₘ (σ-compact) and N is null.
- f(Kₘ) is compact (continuous image of compact), hence measurable.
  So f(K) = ⋃ f(Kₘ) is Fσ, hence measurable.
- f(N) is null by part (b), hence measurable.
- f(E) = f(K) ∪ f(N) is measurable.

### Key ingredients

1. **σ-compact + null decomposition** of measurable subsets of [0,1].
   ✓ Proved below via inner regularity of `volume` on `ℝ`.

2. **Continuous image of compact is compact**: `IsCompact.image_of_continuousOn`
   ✓ Available in Mathlib, applied in `ac_image_compact_is_compact`.

3. **Null sets are measurable in the Lebesgue completion.**
   The ambient `MeasurableSpace ℝ` in this file is the Borel σ-algebra, however,
   and `volume.IsComplete` is deliberately not an instance.  Thus this step
   cannot conclude the stated `MeasurableSet` goal from a measure-zero image.

4. **AC ⟹ continuous**: `AbsolutelyContinuousOnInterval.continuousOn`.
   ✓ Applied in `ac_continuousOn`.

5. **Null sets map to null sets** (Lusin condition N).
   This gives null-measurability, not Borel measurability, of the residual
   image. A corrected target should use `NullMeasurableSet` (or the completed
   Lebesgue measurable space), unless additional Borel-image regularity is
   supplied.
-/

/-- Part (c): If f is absolutely continuous on [0,1] and E ⊆ [0,1] is
Borel measurable, then f(E) is Borel measurable.

The standard σ-compact-plus-null proof only proves Lebesgue measurability:
Mathlib's ambient `MeasurableSpace ℝ` is Borel and `volume` is not complete.
The stated Borel conclusion therefore needs a separate image-regularity
argument (or a corrected completed-measurable-space target). -/
theorem ac_maps_measurable_to_measurable
    {f : ℝ → ℝ}
    (hac : ACOnUnitInterval f)
    {E : Set ℝ} (hE : E ⊆ Icc (0:ℝ) 1)
    (hE_meas : MeasurableSet E) :
    MeasurableSet (f '' E) := by
  sorry

end PartC

section Lemmas

/-! ## Supporting lemmas

These are intermediate results that expose the proof structure.
All lemmas in this section are fully proved from Mathlib.
-/

/-- An AC function on [0,1] is continuous on [0,1].

This is directly from Mathlib's `AbsolutelyContinuousOnInterval.continuousOn`.
Note: `uIcc 0 1 = Icc 0 1` since `0 ≤ 1`. -/
lemma ac_continuousOn
    {f : ℝ → ℝ}
    (hac : ACOnUnitInterval f) :
    ContinuousOn f (Icc (0:ℝ) 1) := by
  have : AbsolutelyContinuousOnInterval f 0 1 := hac
  convert this.continuousOn using 1
  exact (uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm

/-- The derivative of an AC function is interval-integrable on `[0,1]`. -/
lemma ac_intervalIntegrable_deriv
    {f : ℝ → ℝ} (hac : ACOnUnitInterval f) :
    IntervalIntegrable (deriv f) volume 0 1 :=
  hac.intervalIntegrable_deriv

/-- The current Mathlib FTC for AC functions, specialized to subintervals of
`[0,1]`. -/
lemma ac_integral_deriv_eq_sub
    {f : ℝ → ℝ} (hac : ACOnUnitInterval f)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    ∫ t in x..y, deriv f t = f y - f x := by
  apply AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
  exact hac.mono (by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro z hz
    rcases le_total x y with hxy | hyx
    · rw [uIcc_of_le hxy] at hz
      exact ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩
    · rw [uIcc_of_ge hyx] at hz
      exact ⟨hy.1.trans hz.1, hz.2.trans hx.2⟩)

/-- Variation bound on one ordered subinterval. This is the analytic component
of the Lusin-(N) covering argument. -/
lemma ac_dist_le_integral_norm_deriv
    {f : ℝ → ℝ} (hac : ACOnUnitInterval f)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxy : x ≤ y) :
    dist (f x) (f y) ≤ ∫ t in x..y, ‖deriv f t‖ := by
  rw [Real.dist_eq, abs_sub_comm, ← ac_integral_deriv_eq_sub hac hx hy]
  simpa only [Real.norm_eq_abs] using
    (intervalIntegral.norm_integral_le_integral_norm
      (f := fun t : ℝ => deriv f t) (μ := volume) hxy)

/-- The continuous image of a compact subset of [0,1] under an AC function
is compact (hence measurable).

Uses Mathlib's `IsCompact.image_of_continuousOn`. -/
lemma ac_image_compact_is_compact
    {f : ℝ → ℝ}
    (hac : ACOnUnitInterval f)
    {K : Set ℝ}
    (hK : IsCompact K) (hK_sub : K ⊆ Icc (0:ℝ) 1) :
    IsCompact (f '' K) := by
  exact hK.image_of_continuousOn (ac_continuousOn hac |>.mono hK_sub)

/-- Compact subsets of ℝ (with the Borel σ-algebra) are measurable. -/
lemma compact_is_measurable
    {K : Set ℝ}
    (hK : IsCompact K) :
    MeasurableSet K :=
  hK.isClosed.measurableSet

/-- A measurable subset of [0,1] can be decomposed as a σ-compact set
union a null set.

This is a consequence of the inner regularity of Lebesgue measure on ℝ
(`volume` is `InnerRegular` as a regular Haar measure on a σ-compact group).

**Proof.** Since `E ⊆ Icc 0 1`, `volume E ≤ 1 < ⊤`. For each `n`, use
`MeasurableSet.exists_lt_isCompact` (from `InnerRegular`) to find a compact
`Kₙ ⊆ E` with `volume(Kₙ) > volume(E) - 1/(n+1)`. Let `K = ⋃ Kₙ` and
`N = E \ K`. Then:
- `E = K ∪ N` (set-theoretic identity, since `K ⊆ E`).
- `volume(K) = volume(E)`: `volume(K) ≤ volume(E)` by `measure_mono`. For the
  reverse, for every `n`, `volume(K) ≥ volume(Kₙ) > volume(E) - 1/(n+1)`.
  By the Archimedean property, `volume(K) ≥ volume(E)`.
- `volume(N) = volume(E \ K) = volume(E) - volume(K) = 0` by `measure_diff`. -/
lemma measurable_subset_Icc_eq_sigmaCompact_union_null
    {E : Set ℝ} (hE_meas : MeasurableSet E) (hE_sub : E ⊆ Icc (0:ℝ) 1) :
    ∃ (K : ℕ → Set ℝ) (N : Set ℝ),
      (∀ n, IsCompact (K n)) ∧
      volume N = 0 ∧
      E = (⋃ n, K n) ∪ N := by
  have hvol_unit : volume (Icc (0 : ℝ) 1) = ENNReal.ofReal (1 : ℝ) := by
    rw [Real.volume_Icc]; simp
  have hE_le : volume E ≤ ENNReal.ofReal (1 : ℝ) :=
    (measure_mono hE_sub).trans (le_of_eq hvol_unit)
  have hE_finite : volume E < ⊤ :=
    lt_of_le_of_lt hE_le ENNReal.ofReal_lt_top
  by_cases hE0 : volume E = 0
  · -- Trivial case: volume E = 0. Take Kₙ = ∅, N = E.
    refine ⟨fun _ => ∅, E, fun _ => isCompact_empty, hE0, ?_⟩
    simp only [iUnion_const, empty_union]
  · have hE_pos : 0 < volume E := lt_of_le_of_ne (zero_le _) (Ne.symm hE0)
    -- For each n, choose compact Kₙ ⊆ E with vol(Kₙ) > vol(E) - 1/(n+1).
    have hex : ∀ n : ℕ, ∃ Ks, Ks ⊆ E ∧ IsCompact Ks ∧
        volume E - ENNReal.ofReal (1 / ((n : ℝ) + 1)) < volume Ks := by
      intro n
      have h_eps_pos : 0 < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
        simp [ENNReal.ofReal_pos]; positivity
      have hlt : volume E - ENNReal.ofReal (1 / ((n : ℝ) + 1)) < volume E := by
        rw [ENNReal.sub_lt_self_iff hE_finite.ne]
        exact ⟨hE_pos, h_eps_pos⟩
      exact MeasurableSet.exists_lt_isCompact hE_meas hlt
    choose! Kf hK_sub hK_comp hK_vol using hex
    -- ⋃ Kₙ ⊆ E.
    have hK_union_sub : (⋃ n, Kf n) ⊆ E := by
      intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact hK_sub i hi
    -- N = E \ ⋃ Kₙ
    set N := E \ ⋃ n, Kf n with hN_def
    -- Set equality: E = (⋃ Kₙ) ∪ N.
    have hEN : E = (⋃ n, Kf n) ∪ N := by
      ext x
      constructor
      · intro hxE
        by_cases hx : x ∈ (⋃ n, Kf n)
        · exact Or.inl hx
        · exact Or.inr ⟨hxE, hx⟩
      · rintro (hx | ⟨hxE, _⟩)
        · exact hK_union_sub hx
        · exact hxE
    refine ⟨Kf, N, hK_comp, ?_, hEN⟩
    -- Prove vol(N) = 0.
    have hK_mbl : ∀ n, MeasurableSet (Kf n) := fun n =>
      (hK_comp n).isClosed.measurableSet
    have hK_union_mbl : MeasurableSet (⋃ n, Kf n) :=
      MeasurableSet.iUnion fun n => hK_mbl n
    have hK_union_finite : volume (⋃ n, Kf n) ≠ ⊤ :=
      ne_top_of_le_ne_top hE_finite.ne (measure_mono hK_union_sub)
    -- vol(⋃ Kₙ) ≥ vol(E): Archimedean argument.
    have hKf_le_union : ∀ n, volume (Kf n) ≤ volume (⋃ m, Kf m) := fun n =>
      measure_mono (subset_iUnion Kf n)
    have hle : volume E ≤ volume (⋃ n, Kf n) := by
      -- Suppose vol(E) > vol(⋃Kf). Find n with 1/(n+1) < gap, contradiction.
      by_contra hnot
      rw [not_le] at hnot
      have hvol_lt : volume (⋃ n, Kf n) < volume E := hnot
      have hvolU_finite : volume (⋃ n, Kf n) < ⊤ :=
        lt_trans hvol_lt hE_finite
      set d := volume E - volume (⋃ n, Kf n)
      have hd_finite : d ≠ ⊤ :=
        ne_top_of_le_ne_top hE_finite.ne tsub_le_self
      have hd_toReal : d.toReal =
          (volume E).toReal - (volume (⋃ n, Kf n)).toReal :=
        ENNReal.toReal_sub_of_le hvol_lt.le hE_finite.ne
      have hd_pos : 0 < d.toReal := by
        rw [hd_toReal]
        exact sub_pos.mpr
          ((ENNReal.toReal_lt_toReal hvolU_finite.ne hE_finite.ne).mpr hvol_lt)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd_pos
      have hnnreal : ENNReal.ofReal (1 / ((n : ℝ) + 1)) < d := by
        rw [← ENNReal.ofReal_toReal hd_finite]
        exact (ENNReal.ofReal_lt_ofReal_iff hd_pos).mpr hn
      have hgt : volume (⋃ m, Kf m) <
          volume E - ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
        have hsub_le : d ≤ volume E := tsub_le_self
        have key : volume E - ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≤
            volume E - d ↔ d ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
          ENNReal.sub_le_sub_iff_left hsub_le hE_finite.ne
        have hcancel : volume E - d = volume (⋃ m, Kf m) :=
          ENNReal.sub_sub_cancel hE_finite.ne hvol_lt.le
        rw [hcancel] at key
        contrapose! hnnreal
        exact key.mp hnnreal
      -- vol(Kf n) > vol(E) - eps > vol(⋃Kf), but vol(Kf n) ≤ vol(⋃Kf).
      -- Contradiction.
      exact absurd (lt_trans hgt (hK_vol n))
        (fun h => lt_irrefl _ ((hKf_le_union n).trans_lt h))
    have hK_union_eq : volume (⋃ n, Kf n) = volume E :=
      le_antisymm (measure_mono hK_union_sub) hle
    -- vol(N) = vol(E \ ⋃Kf) = vol(E) - vol(⋃Kf) = 0.
    rw [hN_def,
        measure_diff hK_union_sub hK_union_mbl.nullMeasurableSet hK_union_finite,
        hK_union_eq, tsub_self]

end Lemmas

end
