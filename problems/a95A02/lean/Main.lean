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
import Mathlib.Order.Interval.Set.OrdConnectedComponent
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.T5

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

/-- The outer measure of the image of any subset of a subinterval is bounded
by the total variation estimate coming from the derivative on that interval.

This packages the diameter step in the covering proof of Lusin's condition
`(N)`: no measurability assumption on `S` or `f '' S` is needed. -/
lemma ac_volume_image_subset_Icc_le_integral_norm_deriv
    {f : ℝ → ℝ} (hac : ACOnUnitInterval f)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    {S : Set ℝ} (hS : S ⊆ Icc a b) :
    volume (f '' S) ≤
      ENNReal.ofReal (∫ t in a..b, ‖deriv f t‖) := by
  refine (Real.volume_le_diam (f '' S)).trans ?_
  rw [Metric.ediam_le_iff]
  rintro _ ⟨x, hxS, rfl⟩ _ ⟨y, hyS, rfl⟩
  have hx := hS hxS
  have hy := hS hyS
  have hfi : IntervalIntegrable (fun t => ‖deriv f t‖) volume a b :=
    hac.intervalIntegrable_deriv.norm.mono
      (Set.uIcc_subset_uIcc
        (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ha)
        (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hb))
      le_rfl
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  rcases le_total x y with hxy | hyx
  · exact (ac_dist_le_integral_norm_deriv hac
      ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
          ⟨ha.1.trans hy.1, hy.2.trans hb.2⟩ hxy).trans
        (intervalIntegral.integral_mono_interval hx.1 hxy hy.2
          (Eventually.of_forall fun _ => norm_nonneg _)
          hfi)
  · rw [dist_comm]
    exact (ac_dist_le_integral_norm_deriv hac
      ⟨ha.1.trans hy.1, hy.2.trans hb.2⟩
          ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩ hyx).trans
        (intervalIntegral.integral_mono_interval hy.1 hyx hx.2
          (Eventually.of_forall fun _ => norm_nonneg _)
          hfi)

/-- The image of the part of one order-connected component lying in `[0,1]`
is controlled directly by the `L¹` mass of `f'` on that component.  This
formulation deliberately avoids choosing endpoints: order-connectedness puts
the interval between any two points back in the component, which is exactly
what the diameter estimate needs. -/
lemma ac_volume_image_component_le_lintegral_enorm_deriv
    {f : ℝ → ℝ} (hac : ACOnUnitInterval f)
    {U : Set ℝ} (x : ℝ) :
    volume (f '' (ordConnectedComponent U x ∩ Icc (0 : ℝ) 1)) ≤
      ∫⁻ t in ordConnectedComponent U x ∩ Icc (0 : ℝ) 1, ‖deriv f t‖ₑ := by
  refine (Real.volume_le_diam _).trans ?_
  rw [Metric.ediam_le_iff]
  rintro _ ⟨u, ⟨huC, huI⟩, rfl⟩ _ ⟨v, ⟨hvC, hvI⟩, rfl⟩
  rw [edist_dist]
  rcases le_total u v with huv | hvu
  · calc
      ENNReal.ofReal (dist (f u) (f v)) ≤
          ENNReal.ofReal (∫ t in u..v, ‖deriv f t‖) :=
        ENNReal.ofReal_le_ofReal
          (ac_dist_le_integral_norm_deriv hac huI hvI huv)
      _ = ∫⁻ t in Ioc u v, ENNReal.ofReal ‖deriv f t‖ := by
        rw [intervalIntegral.integral_of_le huv,
          ofReal_integral_eq_lintegral_ofReal]
        · apply (intervalIntegrable_iff.mp hac.intervalIntegrable_deriv.norm).mono_set
          intro t ht
          rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
          exact ⟨huI.1.trans_lt ht.1, ht.2.trans hvI.2⟩
        · exact Eventually.of_forall fun _ => norm_nonneg _
      _ ≤ ∫⁻ t in ordConnectedComponent U x ∩ Icc (0 : ℝ) 1,
          ENNReal.ofReal ‖deriv f t‖ := lintegral_mono_set (fun t ht =>
        ⟨Ioc_subset_Icc_self.trans (by
            simpa [uIcc_of_le huv] using
              (show OrdConnected (ordConnectedComponent U x) from inferInstance).uIcc_subset
                huC hvC) ht,
          ⟨huI.1.trans_lt ht.1 |>.le, ht.2.trans hvI.2⟩⟩)
      _ = ∫⁻ t in ordConnectedComponent U x ∩ Icc (0 : ℝ) 1, ‖deriv f t‖ₑ := by
        simp only [ofReal_norm_eq_enorm]
  · rw [dist_comm]
    calc
      ENNReal.ofReal (dist (f v) (f u)) ≤
          ENNReal.ofReal (∫ t in v..u, ‖deriv f t‖) :=
        ENNReal.ofReal_le_ofReal
          (ac_dist_le_integral_norm_deriv hac hvI huI hvu)
      _ = ∫⁻ t in Ioc v u, ENNReal.ofReal ‖deriv f t‖ := by
        rw [intervalIntegral.integral_of_le hvu,
          ofReal_integral_eq_lintegral_ofReal]
        · apply (intervalIntegrable_iff.mp hac.intervalIntegrable_deriv.norm).mono_set
          intro t ht
          rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
          exact ⟨hvI.1.trans_lt ht.1, ht.2.trans huI.2⟩
        · exact Eventually.of_forall fun _ => norm_nonneg _
      _ ≤ ∫⁻ t in ordConnectedComponent U x ∩ Icc (0 : ℝ) 1,
          ENNReal.ofReal ‖deriv f t‖ := lintegral_mono_set (fun t ht =>
        ⟨Ioc_subset_Icc_self.trans (by
            simpa [uIcc_of_le hvu] using
              (show OrdConnected (ordConnectedComponent U x) from inferInstance).uIcc_subset
                hvC huC) ht,
          ⟨hvI.1.trans_lt ht.1 |>.le, ht.2.trans huI.2⟩⟩)
      _ = ∫⁻ t in ordConnectedComponent U x ∩ Icc (0 : ℝ) 1, ‖deriv f t‖ₑ := by
        simp only [ofReal_norm_eq_enorm]

/-! The following lemmas package the missing topological half of the Lusin-(N)
covering argument.  The order-connected components of an open real set are
nonempty, pairwise disjoint open intervals; separability makes their index set
countable. -/

lemma isOpen_ordConnectedComponent_of_isOpen {U : Set ℝ} (hU : IsOpen U) (x : ℝ) :
    IsOpen (ordConnectedComponent U x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hxy := mem_ordConnectedComponent.mp hy
  rw [ordConnectedComponent_eq hxy]
  exact ordConnectedComponent_mem_nhds.2
    (hU.mem_nhds (ordConnectedComponent_subset hy))

lemma ordConnectedSection_pairwiseDisjoint (U : Set ℝ) :
    (ordConnectedSection U).PairwiseDisjoint (ordConnectedComponent U) := by
  intro x hx y hy hxy
  apply Set.disjoint_left.2
  intro z hzx hzy
  have hxz : ordConnectedComponent U x = ordConnectedComponent U z :=
    ordConnectedComponent_eq (mem_ordConnectedComponent.mp hzx)
  have hyz : ordConnectedComponent U y = ordConnectedComponent U z :=
    ordConnectedComponent_eq (mem_ordConnectedComponent.mp hzy)
  have hyU : y ∈ U := ordConnectedSection_subset hy
  have hy_in : y ∈ ordConnectedComponent U x := by
    rw [hxz, ← hyz]
    exact self_mem_ordConnectedComponent.2 hyU
  exact hxy (eq_of_mem_ordConnectedSection_of_uIcc_subset hx hy
    (mem_ordConnectedComponent.mp hy_in))

lemma countable_ordConnectedSection_of_isOpen {U : Set ℝ} (hU : IsOpen U) :
    (ordConnectedSection U).Countable := by
  apply (ordConnectedSection_pairwiseDisjoint U).countable_of_isOpen
  · intro x _
    exact isOpen_ordConnectedComponent_of_isOpen hU x
  · intro x hx
    exact nonempty_ordConnectedComponent.2 (ordConnectedSection_subset hx)

lemma iUnion_ordConnectedComponents_eq {U : Set ℝ} :
    ⋃ x ∈ ordConnectedSection U, ordConnectedComponent U x = U := by
  apply Set.Subset.antisymm
  · exact iUnion₂_subset fun x _ => ordConnectedComponent_subset
  · intro y hy
    let x := ordConnectedProj U ⟨y, hy⟩
    apply mem_iUnion.2
    refine ⟨x, mem_iUnion.2 ?_⟩
    exact ⟨⟨⟨y, hy⟩, rfl⟩, mem_ordConnectedComponent_ordConnectedProj U ⟨y, hy⟩⟩

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

section PartB

/-! ## Part (b): Lusin's condition (N) -/

/-- Part (b): AC functions uniformly control outer measure of images of small
subsets of `[0,1]`. -/
private theorem ac_lusin_condition_N_lt_aux
    {f : ℝ → ℝ}
    (hac : ACOnUnitInterval f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ E ⊆ Icc (0:ℝ) 1,
      volume.toOuterMeasure E < ENNReal.ofReal δ →
      volume.toOuterMeasure (f '' E) ≤ ENNReal.ofReal ε := by
  have hnorm_int : IntegrableOn (fun t => ‖deriv f t‖) (Ioc (0 : ℝ) 1) volume := by
    simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (intervalIntegrable_iff.mp hac.intervalIntegrable_deriv.norm)
  have hfinite_Ioc : (∫⁻ t in Ioc (0 : ℝ) 1, ‖deriv f t‖ₑ) ≠ ∞ := by
    have h := (hasFiniteIntegral_iff_norm (fun t => ‖deriv f t‖)).mp
      hnorm_int.hasFiniteIntegral
    simpa only [Real.norm_eq_abs, Real.enorm_eq_ofReal_abs, abs_abs] using (ne_of_lt h)
  have hfinite_Icc : (∫⁻ t in Icc (0 : ℝ) 1, ‖deriv f t‖ₑ) ≠ ∞ := by
    rw [← setLIntegral_congr Ioc_ae_eq_Icc]
    exact hfinite_Ioc
  have hfinite_indicator :
      (∫⁻ t, (Icc (0 : ℝ) 1).indicator (fun t => ‖deriv f t‖ₑ) t) ≠ ∞ := by
    rw [lintegral_indicator measurableSet_Icc]
    exact hfinite_Icc
  obtain ⟨δe, hδe, hsmall⟩ :=
    exists_pos_setLIntegral_lt_of_measure_lt hfinite_indicator
      (ENNReal.ofReal_pos.2 hε).ne'
  let δe' := min δe 1
  have hδe' : 0 < δe' := lt_min hδe (by simp)
  have hδe'_top : δe' ≠ ∞ :=
    ne_top_of_lt (lt_of_le_of_lt (min_le_right δe 1) ENNReal.one_lt_top)
  let δ := δe'.toReal
  have hδ : 0 < δ := ENNReal.toReal_pos hδe'.ne' hδe'_top
  refine ⟨δ, hδ, ?_⟩
  intro E hE hEsmall
  have hEvol' : volume E < δe' := by
    change volume E < ENNReal.ofReal δ at hEsmall
    simpa [δ, ENNReal.ofReal_toReal hδe'_top] using hEsmall
  obtain ⟨U, hEU, hUopen, hUvol'⟩ := E.exists_isOpen_lt_of_lt δe' hEvol'
  have hUvol : volume U < δe := hUvol'.trans_le (min_le_left _ _)
  have hUintegral :
      (∫⁻ t in U ∩ Icc (0 : ℝ) 1, ‖deriv f t‖ₑ) < ENNReal.ofReal ε := by
    have hs := hsmall U hUvol
    rw [setLIntegral_indicator measurableSet_Icc, inter_comm] at hs
    exact hs
  have hcount := countable_ordConnectedSection_of_isOpen hUopen
  let C := fun x : ℝ => ordConnectedComponent U x ∩ Icc (0 : ℝ) 1
  have hCU : ⋃ x ∈ ordConnectedSection U, C x = U ∩ Icc (0 : ℝ) 1 := by
    simp only [C, ← iUnion_inter]
    rw [iUnion_ordConnectedComponents_eq]
  have hcover : f '' E ⊆ ⋃ x : (ordConnectedSection U), f '' C x := by
    intro y hy
    obtain ⟨z, hzE, rfl⟩ := hy
    have hzU : z ∈ U := hEU hzE
    have hzcomp : z ∈ ⋃ x ∈ ordConnectedSection U, ordConnectedComponent U x := by
      rw [iUnion_ordConnectedComponents_eq]
      exact hzU
    obtain ⟨x, hxsec, hzx⟩ := Set.mem_iUnion₂.mp hzcomp
    exact Set.mem_iUnion.2 ⟨⟨x, hxsec⟩, ⟨z, ⟨hzx, hE hzE⟩, rfl⟩⟩
  rw [Measure.toOuterMeasure_apply]
  refine (measure_mono hcover).trans ?_
  letI := hcount.toEncodable
  refine (measure_iUnion_le (fun x : (ordConnectedSection U) => f '' C x)).trans ?_
  refine (ENNReal.tsum_le_tsum fun x => by
    simpa [C] using
      (ac_volume_image_component_le_lintegral_enorm_deriv hac (U := U) (x : ℝ))).trans ?_
  have hmeas : ∀ x ∈ ordConnectedSection U, MeasurableSet (C x) := by
    intro x hx
    exact (isOpen_ordConnectedComponent_of_isOpen hUopen x).measurableSet.inter
      measurableSet_Icc
  have hdisj : (ordConnectedSection U).PairwiseDisjoint C := by
    intro a ha b hb hab
    exact ((ordConnectedSection_pairwiseDisjoint U) ha hb hab).mono
      inter_subset_left inter_subset_left
  rw [← lintegral_biUnion hcount hmeas hdisj, hCU]
  exact hUintegral.le

/-- Part (b): AC functions uniformly control outer measure of images of small
subsets of `[0,1]`, with the non-strict input bound used in the source. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): replace the strict small-set
-- hypothesis by the source's non-strict outer-measure bound.
theorem ac_lusin_condition_N
    {f : ℝ → ℝ}
    (hac : ACOnUnitInterval f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ E ⊆ Icc (0:ℝ) 1,
      volume.toOuterMeasure E ≤ ENNReal.ofReal δ →
      volume.toOuterMeasure (f '' E) ≤ ENNReal.ofReal ε := by
  sorry

/-- Part (b), null-set specialization. -/
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
  simpa using hbound E hE hE_outer.le

end PartB

section PartC

/-- Part (c): AC functions map Lebesgue-measurable subsets of `[0,1]` to
Lebesgue-measurable sets. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): express both input and output
-- measurability in the completion of Borel measure, as the source requires.
theorem ac_maps_measurable_to_measurable
    {f : ℝ → ℝ}
    (hac : ACOnUnitInterval f)
    {E : Set ℝ} (hE : E ⊆ Icc (0:ℝ) 1)
    (hE_meas : NullMeasurableSet E volume) :
    NullMeasurableSet (f '' E) volume := by
  sorry

end PartC

end
