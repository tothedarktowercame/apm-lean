/-
! # APM a96J04: AC monotone increasing maps null sets to null sets

Let `f : [0,1] → ℝ` be absolutely continuous and monotone increasing.
If `E ⊆ [0,1]` has Lebesgue measure zero, then `f(E)` has Lebesgue measure zero.

## Proof

Given ε > 0, AC gives δ > 0. Cover E by countably many disjoint open intervals
with total length < δ. By monotonicity, f(E) ⊆ ∪[f(a_k), f(b_k)], and by AC
the total image length ≤ ε. So volume(f(E)) ≤ ε.

## Statement note

On [0,1] per the TeX. AC encoded as explicit ε-δ since Mathlib has no
function-level AC typeclass.

## Formalization

The open-cover decomposition is constructed locally from connected components
inside `(0,1)`. Each component contains a rational, hence the component family
is countable; an open connected bounded subset of `ℝ` is the `Ioo` interval
between its infimum and supremum. Finite component families then feed directly
to the stated finite absolute-continuity hypothesis.
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.IntermediateValue

open MeasureTheory Set

open scoped NNReal ENNReal

noncomputable section

/-! The decomposition used below is built locally from connected components of
an open subset of `(0, 1)`.  Each component contains a rational, so the family
is countable; openness and order-connectedness identify each component with
the interval between its infimum and supremum. -/

noncomputable def openComponentSet (U : Set ℝ) (c : ConnectedComponents U) : Set ℝ :=
  Subtype.val '' (ConnectedComponents.mk ⁻¹' ({c} : Set (ConnectedComponents U)))

lemma openComponentSet_nonempty (U : Set ℝ) (c : ConnectedComponents U) :
    (openComponentSet U c).Nonempty := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  exact ⟨x, ⟨x, by simp⟩⟩

lemma openComponentSet_subset (U : Set ℝ) (c : ConnectedComponents U) :
    openComponentSet U c ⊆ U := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

lemma openComponentSet_preconnected (U : Set ℝ) (c : ConnectedComponents U) :
    IsPreconnected (openComponentSet U c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [openComponentSet, connectedComponents_preimage_singleton]
  exact isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn

lemma openComponentSet_open (U : Set ℝ) (hU : IsOpen U) (c : ConnectedComponents U) :
    IsOpen (openComponentSet U c) := by
  letI : LocallyConnectedSpace U := hU.locallyConnectedSpace
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [openComponentSet, connectedComponents_preimage_singleton]
  exact hU.isOpenMap_subtype_val _ isOpen_connectedComponent

lemma openComponentSet_exists_rat (U : Set ℝ) (hU : IsOpen U)
    (c : ConnectedComponents U) : ∃ q : ℚ, (q : ℝ) ∈ openComponentSet U c := by
  obtain ⟨a, b, hab, hsub⟩ :=
    (openComponentSet_open U hU c).exists_Ioo_subset (openComponentSet_nonempty U c)
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn hab
  exact ⟨q, hsub ⟨haq, hqb⟩⟩

noncomputable def openComponentRat (U : Set ℝ) (hU : IsOpen U)
    (c : ConnectedComponents U) : ℚ :=
  (openComponentSet_exists_rat U hU c).choose

lemma openComponentRat_mem (U : Set ℝ) (hU : IsOpen U) (c : ConnectedComponents U) :
    (openComponentRat U hU c : ℝ) ∈ openComponentSet U c :=
  (openComponentSet_exists_rat U hU c).choose_spec

lemma openComponentRat_injective (U : Set ℝ) (hU : IsOpen U) :
    Function.Injective (openComponentRat U hU) := by
  intro c d hcd
  obtain ⟨x, hx, hxc⟩ := openComponentRat_mem U hU c
  obtain ⟨y, hy, hyd⟩ := openComponentRat_mem U hU d
  have hxy : x = y := Subtype.ext (hxc.trans (hcd ▸ hyd.symm))
  exact hx.symm.trans (hxy ▸ hy)

lemma openComponentSet_eq_Ioo (U : Set ℝ) (hU : IsOpen U) (hUI : U ⊆ Ioo 0 1)
    (c : ConnectedComponents U) :
    openComponentSet U c = Ioo (sInf (openComponentSet U c)) (sSup (openComponentSet U c)) := by
  let s := openComponentSet U c
  have hsne : s.Nonempty := openComponentSet_nonempty U c
  have hsopen : IsOpen s := openComponentSet_open U hU c
  have hspre : IsPreconnected s := openComponentSet_preconnected U c
  have hs0 : s ⊆ Ioo 0 1 := (openComponentSet_subset U c).trans hUI
  have hbelow : BddBelow s := ⟨0, fun _ hx => (hs0 hx).1.le⟩
  have habove : BddAbove s := ⟨1, fun _ hx => (hs0 hx).2.le⟩
  apply Subset.antisymm
  · intro x hx
    have hle : sInf s ≤ x := csInf_le hbelow hx
    have hge : x ≤ sSup s := le_csSup habove hx
    constructor
    · refine lt_of_le_of_ne hle ?_
      intro heq
      change sInf s = x at heq
      obtain ⟨l, u, hlu, hsub⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (hsopen.mem_nhds hx)
      rcases hlu with ⟨hlx, hxu⟩
      have hly : l < (l + x) / 2 := by linarith
      have hyx : (l + x) / 2 < x := by linarith
      have hy : (l + x) / 2 ∈ s := hsub ⟨hly, hyx.trans hxu⟩
      have := csInf_le hbelow hy
      linarith
    · refine lt_of_le_of_ne hge ?_
      intro heq
      change x = sSup s at heq
      obtain ⟨l, u, hlu, hsub⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (hsopen.mem_nhds hx)
      rcases hlu with ⟨hlx, hxu⟩
      have hxy : x < (x + u) / 2 := by linarith
      have hyu : (x + u) / 2 < u := by linarith
      have hy : (x + u) / 2 ∈ s := hsub ⟨hlx.trans hxy, hyu⟩
      have := le_csSup habove hy
      linarith
  · exact (show IsConnected s from ⟨hsne, hspre⟩).Ioo_csInf_csSup_subset hbelow habove

lemma openComponentSet_pairwiseDisjoint (U : Set ℝ) :
    Pairwise (fun c d => Disjoint (openComponentSet U c) (openComponentSet U d)) := by
  intro c d hcd
  rw [Set.disjoint_left]
  intro z hzc hzd
  obtain ⟨x, hx, hzx⟩ := hzc
  obtain ⟨y, hy, hzy⟩ := hzd
  have hxy : x = y := Subtype.ext (hzx.trans hzy.symm)
  exact hcd (hx.symm.trans (hxy ▸ hy))

noncomputable def openComponentLeft (U : Set ℝ) (c : ConnectedComponents U) : ℝ :=
  sInf (openComponentSet U c)

noncomputable def openComponentRight (U : Set ℝ) (c : ConnectedComponents U) : ℝ :=
  sSup (openComponentSet U c)

lemma openComponent_endpoints_mem_Icc (U : Set ℝ) (hUI : U ⊆ Ioo 0 1)
    (c : ConnectedComponents U) :
    openComponentLeft U c ∈ Icc 0 1 ∧ openComponentRight U c ∈ Icc 0 1 ∧
      openComponentLeft U c ≤ openComponentRight U c := by
  have hsne := openComponentSet_nonempty U c
  have hs0 : openComponentSet U c ⊆ Ioo 0 1 := (openComponentSet_subset U c).trans hUI
  have hbelow : BddBelow (openComponentSet U c) := ⟨0, fun _ hx => (hs0 hx).1.le⟩
  have habove : BddAbove (openComponentSet U c) := ⟨1, fun _ hx => (hs0 hx).2.le⟩
  have ha0 : 0 ≤ openComponentLeft U c := le_csInf hsne (fun _ hx => (hs0 hx).1.le)
  have hb1 : openComponentRight U c ≤ 1 := csSup_le hsne (fun _ hx => (hs0 hx).2.le)
  obtain ⟨x, hx⟩ := hsne
  have haxb : openComponentLeft U c ≤ x := csInf_le hbelow hx
  have hxbb : x ≤ openComponentRight U c := le_csSup habove hx
  exact ⟨⟨ha0, haxb.trans hxbb |>.trans hb1⟩,
    ⟨ha0.trans (haxb.trans hxbb), hb1⟩, haxb.trans hxbb⟩

lemma openComponentSet_eq_endpoints (U : Set ℝ) (hU : IsOpen U) (hUI : U ⊆ Ioo 0 1)
    (c : ConnectedComponents U) :
    openComponentSet U c = Ioo (openComponentLeft U c) (openComponentRight U c) :=
  openComponentSet_eq_Ioo U hU hUI c

lemma openComponentSet_injective (U : Set ℝ) : Function.Injective (openComponentSet U) := by
  intro c d hcd
  obtain ⟨z, hzc⟩ := openComponentSet_nonempty U c
  have hzd : z ∈ openComponentSet U d := hcd ▸ hzc
  obtain ⟨x, hx, hzx⟩ := hzc
  obtain ⟨y, hy, hzy⟩ := hzd
  have hxy : x = y := Subtype.ext (hzx.trans hzy.symm)
  exact hx.symm.trans (hxy ▸ hy)

noncomputable def openComponentEndpointsEmbedding (U : Set ℝ) (hU : IsOpen U)
    (hUI : U ⊆ Ioo 0 1) : ConnectedComponents U ↪ (ℝ × ℝ) where
  toFun c := (openComponentLeft U c, openComponentRight U c)
  inj' := by
    intro c d h
    apply openComponentSet_injective U
    rw [openComponentSet_eq_endpoints U hU hUI c,
      openComponentSet_eq_endpoints U hU hUI d]
    exact congrArg (fun p : ℝ × ℝ => Ioo p.1 p.2) h

lemma openComponent_image_subset (f : ℝ → ℝ) (hf : MonotoneOn f (Icc 0 1))
    (U : Set ℝ) (hU : IsOpen U) (hUI : U ⊆ Ioo 0 1)
    (c : ConnectedComponents U) :
    f '' openComponentSet U c ⊆
      Icc (f (openComponentLeft U c)) (f (openComponentRight U c)) := by
  rw [openComponentSet_eq_endpoints U hU hUI c]
  rintro _ ⟨x, hx, rfl⟩
  have he := openComponent_endpoints_mem_Icc U hUI c
  have hx01 : x ∈ Icc 0 1 := ⟨he.1.1.trans hx.1.le, hx.2.le.trans he.2.1.2⟩
  exact ⟨hf he.1 hx01 hx.1.le, hf hx01 he.2.1 hx.2.le⟩

/-- Helper: for monotone f on [0,1], the image of an interval [a,b] ⊆ [0,1]
    is contained in [f(a), f(b)]. -/
lemma monotone_image_interval (f : ℝ → ℝ) (hf : MonotoneOn f (Icc 0 1))
    {a b x : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hx : x ∈ Icc 0 1)
    (hax : a ≤ x) (hxb : x ≤ b) :
    f a ≤ f x ∧ f x ≤ f b :=
  ⟨hf ha hx hax, hf hx hb hxb⟩

/-- Helper: the image f '' Icc a b ⊆ Icc (f a) (f b) for monotone f. -/
lemma monotone_image_Icc (f : ℝ → ℝ) (hf : MonotoneOn f (Icc 0 1))
    {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (_hab : a ≤ b) :
    f '' Icc a b ⊆ Icc (f a) (f b) := by
  rintro y ⟨x, hx, rfl⟩
  have hx01 : x ∈ Icc 0 1 := ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
  exact ⟨hf ha hx01 hx.1, hf hx01 hb hx.2⟩

/-- **Main theorem**: AC + monotone increasing ⟹ maps null sets to null sets.

    The AC condition is: ∀ ε > 0, ∃ δ > 0, for any finite collection of
    pairwise-disjoint-interval-interior intervals in [0,1] with total length < δ,
    the total variation Σ‖f(b_k) - f(a_k)‖ < ε. -/
theorem ac_monotone_maps_null_to_null
    (f : ℝ → ℝ)
    (hf_mono : MonotoneOn f (Icc 0 1))
    (hf_ac : ∀ ε > 0, ∃ δ > 0, ∀ (s : Finset (ℝ × ℝ)),
      (∀ p ∈ s, p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc 0 1 ∧ p.1 ≤ p.2) →
      (∀ p q, p ∈ s → q ∈ s → p ≠ q →
        Disjoint (Ioo p.1 p.2) (Ioo q.1 q.2)) →
      (∑ p ∈ s, (p.2 - p.1)) < δ →
      (∑ p ∈ s, ‖f p.2 - f p.1‖) < ε)
    (E : Set ℝ) (hE : E ⊆ Icc 0 1)
    (hE_null : volume E = 0) :
    volume (f '' E) = 0 := by
  have hinterior : volume (f '' (E ∩ Ioo 0 1)) = 0 := by
    apply le_antisymm
    · apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      simp only [zero_add]
      obtain ⟨δ, hδ, hAC⟩ := hf_ac (ε : ℝ) (by exact_mod_cast hε)
      obtain ⟨U, hEU, hUopen, hUvol⟩ :=
        Set.exists_isOpen_lt_of_lt (μ := volume) E (ENNReal.ofReal δ)
          (by simp [hE_null, hδ])
      let U0 := U ∩ Ioo (0 : ℝ) 1
      have hU0open : IsOpen U0 := hUopen.inter isOpen_Ioo
      have hU0I : U0 ⊆ Ioo (0 : ℝ) 1 := inter_subset_right
      letI : Countable (ConnectedComponents U0) :=
        (openComponentRat_injective U0 hU0open).countable
      let emb := openComponentEndpointsEmbedding U0 hU0open hU0I
      have himage : f '' (E ∩ Ioo 0 1) ⊆
          ⋃ c : ConnectedComponents U0,
            Icc (f (openComponentLeft U0 c)) (f (openComponentRight U0 c)) := by
        rintro y ⟨x, hx, rfl⟩
        let xu : U0 := ⟨x, hEU hx.1, hx.2⟩
        apply mem_iUnion.2
        refine ⟨(xu : ConnectedComponents U0), ?_⟩
        apply openComponent_image_subset f hf_mono U0 hU0open hU0I
        exact ⟨x, ⟨xu, by simp, rfl⟩, rfl⟩
      refine (measure_mono himage).trans <| (measure_iUnion_le _).trans ?_
      apply ENNReal.summable.tsum_le_of_sum_le
      intro s
      have hpair : (s : Set (ConnectedComponents U0)).PairwiseDisjoint
          (openComponentSet U0) := by
        intro c hc d hd hcd
        exact openComponentSet_pairwiseDisjoint U0 hcd
      have hlen : s.sum (fun c => openComponentRight U0 c - openComponentLeft U0 c) < δ := by
        rw [← ENNReal.ofReal_lt_ofReal_iff hδ,
          ENNReal.ofReal_sum_of_nonneg]
        · calc
            (∑ c ∈ s, ENNReal.ofReal (openComponentRight U0 c - openComponentLeft U0 c)) =
                ∑ c ∈ s, volume (openComponentSet U0 c) := by
                  apply Finset.sum_congr rfl
                  intro c hc
                  rw [openComponentSet_eq_endpoints U0 hU0open hU0I c,
                    Real.volume_Ioo]
            _ = volume (⋃ c ∈ s, openComponentSet U0 c) :=
              (measure_biUnion_finset hpair (fun c _ =>
                (openComponentSet_open U0 hU0open c).measurableSet)).symm
            _ ≤ volume U0 := measure_mono (by
              exact iUnion₂_subset fun c hc => openComponentSet_subset U0 c)
            _ ≤ volume U := measure_mono inter_subset_left
            _ < ENNReal.ofReal δ := hUvol
        · intro c hc
          exact sub_nonneg.mpr (openComponent_endpoints_mem_Icc U0 hU0I c).2.2
      have hpairs : ∀ p q, p ∈ s.map emb → q ∈ s.map emb → p ≠ q →
          Disjoint (Ioo p.1 p.2) (Ioo q.1 q.2) := by
        intro p q hp hq hpq
        rw [Finset.mem_map] at hp hq
        obtain ⟨c, hc, rfl⟩ := hp
        obtain ⟨d, hd, rfl⟩ := hq
        change Disjoint
          (Ioo (openComponentLeft U0 c) (openComponentRight U0 c))
          (Ioo (openComponentLeft U0 d) (openComponentRight U0 d))
        rw [← openComponentSet_eq_endpoints U0 hU0open hU0I c,
          ← openComponentSet_eq_endpoints U0 hU0open hU0I d]
        exact openComponentSet_pairwiseDisjoint U0 (fun hcd => hpq (congrArg emb hcd))
      have hvariation := hAC (s.map emb)
        (by
          intro p hp
          rw [Finset.mem_map] at hp
          obtain ⟨c, hc, rfl⟩ := hp
          exact openComponent_endpoints_mem_Icc U0 hU0I c)
        hpairs (by simpa [emb] using hlen)
      calc
        (∑ c ∈ s, volume (Icc (f (openComponentLeft U0 c))
            (f (openComponentRight U0 c)))) =
            ENNReal.ofReal (∑ c ∈ s,
              ‖f (openComponentRight U0 c) - f (openComponentLeft U0 c)‖) := by
              rw [ENNReal.ofReal_sum_of_nonneg]
              · apply Finset.sum_congr rfl
                intro c hc
                rw [Real.volume_Icc]
                congr 1
                rw [Real.norm_eq_abs, abs_of_nonneg]
                exact sub_nonneg.mpr <| hf_mono
                  (openComponent_endpoints_mem_Icc U0 hU0I c).1
                  (openComponent_endpoints_mem_Icc U0 hU0I c).2.1
                  (openComponent_endpoints_mem_Icc U0 hU0I c).2.2
              · intro c hc
                exact norm_nonneg _
        _ ≤ (ε : ℝ≥0∞) := by
          have hvreal : s.sum (fun c =>
              ‖f (openComponentRight U0 c) - f (openComponentLeft U0 c)‖) ≤ (ε : ℝ) := by
            simpa [emb] using hvariation.le
          simpa using ENNReal.ofReal_le_ofReal hvreal
    · exact zero_le _
  have hsplit : E ⊆ (E ∩ Ioo 0 1) ∪ ({0, 1} : Set ℝ) := by
    intro x hx
    rcases hE hx with ⟨hx0, hx1⟩
    by_cases h0 : x = 0
    · exact Or.inr (by simp [h0])
    by_cases h1 : x = 1
    · exact Or.inr (by simp [h1])
    exact Or.inl ⟨hx, lt_of_le_of_ne hx0 (Ne.symm h0), lt_of_le_of_ne hx1 h1⟩
  apply measure_mono_null (image_mono hsplit)
  rw [image_union]
  apply measure_union_null hinterior
  exact (Set.toFinite (f '' ({0, 1} : Set ℝ))).measure_zero volume

end
