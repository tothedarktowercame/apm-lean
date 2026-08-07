import Mathlib

/-!
# APM t91J01

## Statement repairs

None.

## Encoding questions

None. The domain is Mathlib's standard ternary `cantorSet`, and the codomain
is the actual subtype of irrational real numbers strictly between `0` and `1`,
both carrying their subspace topologies.
-/

open Set MeasureTheory
open scoped ENNReal

abbrev apm_t91J01_Cantor := cantorSet
abbrev apm_t91J01_IrrationalsInUnitInterval :=
  {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1}

-- (Sibling: a95J06)
lemma apm_t91J01_cantorSet_measure_zero : volume cantorSet = 0 := by
  have hscale :
      volume ((fun x : ℝ => x / 3) '' cantorSet) =
        ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet := by
    rw [show (fun x : ℝ => x / 3) = fun x => (3 : ℝ)⁻¹ * x by funext x; ring,
      show (fun x : ℝ => 3⁻¹ * x) '' cantorSet =
          (fun x : ℝ => 3 * x) ⁻¹' cantorSet by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          simpa using hy
        · intro hx
          exact ⟨3 * x, hx, by ring⟩,
      Real.volume_preimage_mul_left (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have htranslate :
      volume ((fun x : ℝ => (2 + x) / 3) '' cantorSet) =
        ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet := by
    have himage :
        (fun x : ℝ => (2 + x) / 3) '' cantorSet =
          (fun x : ℝ => 2 / 3 + x) '' ((fun x : ℝ => x / 3) '' cantorSet) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y / 3, ⟨y, hy, rfl⟩, by ring⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, by ring⟩
    rw [himage, image_add_left, measure_preimage_add, hscale]
  have hle : volume cantorSet ≤
      ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet +
        ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet := by
    calc
      volume cantorSet = volume ((fun x : ℝ => x / 3) '' cantorSet ∪
          (fun x : ℝ => (2 + x) / 3) '' cantorSet) :=
        congrArg volume cantorSet_eq_union_halves
      _ ≤ volume ((fun x : ℝ => x / 3) '' cantorSet) +
            volume ((fun x : ℝ => (2 + x) / 3) '' cantorSet) := measure_union_le _ _
      _ = _ := by rw [hscale, htranslate]
  have hfin : volume cantorSet ≠ ∞ := by
    exact ne_of_lt ((measure_mono cantorSet_subset_unitInterval).trans_lt (by simp))
  have hzreal : (volume cantorSet).toReal = 0 := by
    have hmul : ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
    have hrhs : ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet +
        ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet ≠ ∞ :=
      ENNReal.add_ne_top.mpr ⟨hmul, hmul⟩
    have hreal := ENNReal.toReal_mono hrhs hle
    rw [ENNReal.toReal_add hmul hmul] at hreal
    simp only [ENNReal.toReal_mul] at hreal
    norm_num at hreal
    exact le_antisymm (by linarith [ENNReal.toReal_nonneg (a := volume cantorSet)])
      ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).mp hzreal with hzero | htop
  · exact hzero
  · exact (hfin htop).elim

theorem apm_t91j01 :
    (¬∃ f : C(apm_t91J01_Cantor, apm_t91J01_IrrationalsInUnitInterval),
      Function.Surjective f) ∧
    ∃ f : C(apm_t91J01_Cantor, apm_t91J01_IrrationalsInUnitInterval),
      Function.Injective f := by
  constructor
  · rintro ⟨f, hf⟩
    letI : CompactSpace apm_t91J01_Cantor :=
      isCompact_iff_compactSpace.mp isCompact_cantorSet
    have hcompact : IsCompact
        (Set.univ : Set apm_t91J01_IrrationalsInUnitInterval) := by
      simpa [hf.range_eq] using isCompact_range f.continuous
    have hcompact' : IsCompact
        {x : ℝ | Irrational x ∧ 0 < x ∧ x < 1} := by
      simpa using hcompact.image continuous_subtype_val
    have hclosed : IsClosed {x : ℝ | Irrational x ∧ 0 < x ∧ x < 1} :=
      hcompact'.isClosed
    have hhalf : (1 / 2 : ℝ) ∈
        closure {x : ℝ | Irrational x ∧ 0 < x ∧ x < 1} := by
      rw [mem_closure_iff_nhds]
      intro t ht
      have hI : Set.Ioo (0 : ℝ) 1 ∈ nhds (1 / 2 : ℝ) :=
        Ioo_mem_nhds (by norm_num) (by norm_num)
      obtain ⟨x, hxirr, hxt, hx0, hx1⟩ :=
        dense_irrational.inter_nhds_nonempty (Filter.inter_mem ht hI)
      exact ⟨x, hxt, hxirr, hx0, hx1⟩
    have hmem := hclosed.closure_subset hhalf
    exact hmem.1 ⟨(1 / 2 : ℚ), by norm_num⟩
  · -- (Sibling: a95J06) supplies the missing nullity argument for `cantorSet`.
    -- The countable union of affine bad-parameter sets is null, so it cannot
    -- cover the positive-measure interval `(0, 1/2)`.
    let scaledCantor : Set ℝ := (fun x : ℝ => x / 2) '' cantorSet
    have hscaled : volume scaledCantor = 0 := by
      have heq : scaledCantor = (fun x : ℝ => 2 * x) ⁻¹' cantorSet := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          change 2 * (y / 2) ∈ cantorSet
          rw [show 2 * (y / 2) = y by ring]
          exact hy
        · intro hx
          exact ⟨2 * x, hx, by ring⟩
      rw [heq, Real.volume_preimage_mul_left (by norm_num : (2 : ℝ) ≠ 0),
        apm_t91J01_cantorSet_measure_zero, mul_zero]
    let bad : Set ℝ := ⋃ q : ℚ, (fun x : ℝ => (q : ℝ) - x) '' scaledCantor
    have hbad_piece (q : ℚ) :
        volume ((fun x : ℝ => (q : ℝ) - x) '' scaledCantor) = 0 := by
      have himage : (fun x : ℝ => (q : ℝ) - x) '' scaledCantor =
          (fun x : ℝ => (q : ℝ) - x) ⁻¹' scaledCantor := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          simpa only [mem_preimage, sub_sub_cancel] using hy
        · intro hx
          exact ⟨(q : ℝ) - x, hx, by ring⟩
      rw [himage, show (fun x : ℝ => (q : ℝ) - x) ⁻¹' scaledCantor =
          (fun x : ℝ => (-1) * x) ⁻¹' ((fun x : ℝ => (q : ℝ) + x) ⁻¹' scaledCantor) by
            ext x
            simp [sub_eq_add_neg],
        Real.volume_preimage_mul_left (by norm_num : (-1 : ℝ) ≠ 0),
        measure_preimage_add, hscaled, mul_zero]
    have hbad : volume bad = 0 := by
      exact measure_iUnion_null hbad_piece
    obtain ⟨b, hbI, hb⟩ : ∃ b ∈ Ioo (0 : ℝ) (1 / 2), b ∉ bad := by
      by_contra h
      push_neg at h
      have hzero : volume (Ioo (0 : ℝ) (1 / 2)) = 0 :=
        measure_mono_null (fun x hx => h x hx) hbad
      rw [Real.volume_Ioo] at hzero
      norm_num at hzero
    let F : apm_t91J01_Cantor → apm_t91J01_IrrationalsInUnitInterval :=
      fun x => ⟨x.1 / 2 + b, by
        refine ⟨?_, ?_, ?_⟩
        · intro hrat
          rcases hrat with ⟨q, hq⟩
          apply hb
          refine mem_iUnion.2 ⟨q, ?_⟩
          refine ⟨x.1 / 2, ⟨x.1, x.2, rfl⟩, ?_⟩
          change (q : ℝ) - x.1 / 2 = b
          rw [hq]
          ring
        · have hx0 : 0 ≤ x.1 := (cantorSet_subset_unitInterval x.2).1
          exact add_pos_of_nonneg_of_pos (div_nonneg hx0 (by norm_num)) hbI.1
        · have hx1 : x.1 ≤ 1 := (cantorSet_subset_unitInterval x.2).2
          linarith [hbI.2]⟩
    have hF : Continuous F :=
      ((continuous_subtype_val.div_const 2).add continuous_const).subtype_mk _
    let f : C(apm_t91J01_Cantor, apm_t91J01_IrrationalsInUnitInterval) := ⟨F, hF⟩
    refine ⟨f, ?_⟩
    intro x y hxy
    have hv := congrArg (fun z : apm_t91J01_IrrationalsInUnitInterval => (z : ℝ)) hxy
    apply Subtype.ext
    change x.1 = y.1
    change x.1 / 2 + b = y.1 / 2 + b at hv
    linarith
