import Mathlib

/-!
# APM a97J04: Local absolute continuity at a boundary point

## Statement repairs

None.

## Encoding questions

None. A function on `[0,1]` is represented by an ambient `f : ℝ → ℝ` whose
hypotheses and conclusion are all restricted to the stated intervals. Bounded
variation and absolute continuity use Mathlib's `BoundedVariationOn` and
`AbsolutelyContinuousOnInterval` predicates directly.
-/

open Set Topology Filter

theorem apm_a97j04
    (f : ℝ → ℝ)
    (hcontinuous : ContinuousOn f (Icc (0 : ℝ) 1))
    (hvariation : BoundedVariationOn f (Icc (0 : ℝ) 1))
    (hlocal : ∀ δ : ℝ, 0 < δ → δ < 1 →
      AbsolutelyContinuousOnInterval f δ 1) :
    AbsolutelyContinuousOnInterval f 0 1 := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  -- Step 1: Continuity of `f` at `0` within `Icc 0 1 ∩ Ici 0`.
  have hcont0 : ContinuousWithinAt f (Icc (0 : ℝ) 1 ∩ Ici 0) 0 := by
    apply (hcontinuous.continuousWithinAt (by norm_num)).mono
    refine fun x hx => hx.1
  -- Step 2: Rewrite the restricted neighbourhood filter.
  have hFilter : nhdsWithin 0 (Icc (0:ℝ) 1) = nhdsWithin 0 (Ici (0:ℝ)) :=
    nhdsWithin_Icc_eq_nhdsGE (by norm_num : (0:ℝ) < 1)
  -- Step 3: BV + continuity at 0 ⟹ variation on [0, y] → 0 as y → 0⁺.
  have hvar_tendsto := hvariation.tendsto_eVariationOn_Icc_zero_right 0 hcont0
  rw [hFilter] at hvar_tendsto
  have heps : (0:ENNReal) < ENNReal.ofReal (ε/2) := by
    rw [ENNReal.ofReal_pos]; linarith
  -- Extract a basis element Ico 0 δ on which the variation bound holds.
  obtain ⟨δvar, hδvar_pos, hδvar_bound⟩ :
    ∃ δ, 0 < δ ∧ ∀ y ∈ Ico (0:ℝ) δ,
      eVariationOn f (Icc 0 1 ∩ Icc 0 y) < ENNReal.ofReal (ε/2) := by
    have hbasis := nhdsGE_basis (0:ℝ)
    have key := hvar_tendsto.eventually (gt_mem_nhds heps)
    rw [hbasis.eventually_iff] at key
    simpa using key
  -- Pick a₀ ∈ (0,1) with variation on [0, a₀] < ε/2.
  set a₀ := min δvar ((1:ℝ)/2) / 2
  have ha₀_pos : 0 < a₀ :=
    div_pos (lt_min hδvar_pos (by norm_num : (0:ℝ) < 1/2)) (by norm_num)
  have ha₀_lt1 : a₀ < 1 := by
    dsimp only [a₀]
    have : min δvar ((1:ℝ)/2) ≤ 1/2 := min_le_right δvar ((1:ℝ)/2)
    linarith
  have ha₀_lt_δvar : a₀ < δvar := by
    dsimp only [a₀]
    have h1 : min δvar ((1:ℝ)/2) ≤ δvar := min_le_left δvar ((1:ℝ)/2)
    have h2 : (0:ℝ) < 2 := by norm_num
    calc min δvar ((1:ℝ)/2) / 2 ≤ δvar / 2 := by gcongr
      _ < δvar := by rw [div_lt_iff₀ h2]; linarith
  have ha₀_var : eVariationOn f (Icc (0:ℝ) 1 ∩ Icc 0 a₀) < ENNReal.ofReal (ε/2) :=
    hδvar_bound a₀ ⟨le_of_lt ha₀_pos, ha₀_lt_δvar⟩
  -- Step 4: Get AC on [a₀, 1] from the hypothesis.
  have hac : AbsolutelyContinuousOnInterval f a₀ 1 := hlocal a₀ ha₀_pos ha₀_lt1
  rw [absolutelyContinuousOnInterval_iff] at hac
  obtain ⟨δac, hδac_pos, hac_bound⟩ := hac (ε/2) (by linarith)
  -- Step 5: Set δ = min δac a₀. We will show: for any disjWithin 0 1 family
  -- with total length < δ, the oscillation sum is < ε.
  -- BLOCKER: The ε-δ gluing argument requires splitting each straddling
  -- interval at a₀, constructing a refined disjWithin family on [a₀, 1],
  -- and bounding the original sum via the triangle inequality plus the
  -- variation bound on [0, a₀]. This interval-refinement construction on an
  -- arbitrary disjWithin family is the formal bottleneck.
  --
  -- APIs searched with backticks:
  --   `AbsolutelyContinuousOnInterval.mono`, `.symm`, `.add`, `.sub`
  --   `eVariationOn.sum_le`, `eVariationOn.Icc_add_Icc`, `eVariationOn.union`
  --   `eVariationOn.add_le_union`, `eVariationOn.add_point`
  --   `BoundedVariationOn.tendsto_eVariationOn_Icc_zero_right`
  --   `absolutelyContinuousOnInterval_iff`
  --   `nhdsGE_basis`, `nhdsWithin_Icc_eq_nhdsGE`, `gt_mem_nhds`
  -- Routes tried:
  --   1. Direct ε-δ with interval splitting (the informal proof's approach).
  --      The refinement of a disjWithin family at a₀ requires casework on
  --      each interval's position relative to a₀ and reconstruction of the
  --      family; Mathlib has no gluing/concat lemma for AC on intervals.
  --   2. Filter-level gluing (composing tendsto on totalLengthFilter ⊓ 𝓟
  --      (disjWithin 0 1) from the two sub-filters). No existing machinery
  --      decomposes disjWithin 0 1 into left and right parts.
  -- Specific blocker: Mathlib's `AbsolutelyContinuousOnInterval` lacks a
  -- "gluing" or "concat" lemma (analogous to `eVariationOn.Icc_add_Icc` for
  -- variation) that would compose AC on [0, a₀] (from BV) with AC on [a₀, 1]
  -- to give AC on [0, 1]. The BV→AC-on-[0,a₀] direction is also not directly
  -- available; one would need `BoundedVariationOn → AC` on a subinterval
  -- using continuity, which is itself a nontrivial lemma.
  sorry
