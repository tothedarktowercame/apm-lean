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

open Set

abbrev apm_t91J01_Cantor := cantorSet
abbrev apm_t91J01_IrrationalsInUnitInterval :=
  {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1}

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
  · /-
    Boundary: the injection route chooses an affine translate of the Cantor
    set avoiding every rational. I searched `cantorSet`,
    `cantorSetHomeomorphNatToBool`, `dense_irrational`, Baire-category,
    measure-zero, null, and irrational-homeomorphism APIs. Mathlib does not
    provide that the ternary Cantor set is null/meager, a packaged embedding
    of Cantor space into the irrational interval, or a homeomorphism between
    the irrationals and Baire space. Formalizing the exceptional-translation
    argument (or an explicit continued-fraction embedding) is the remaining
    blocker.
    -/
    sorry
