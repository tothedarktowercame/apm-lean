import Mathlib

noncomputable section

namespace t91J06Closure

open Set

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

/-- A continuous injection of the closed unit interval has one of its two
possible orientations. -/
theorem intervalEmbedding_orientation
    (t : UnitInterval → UnitInterval) (ht : Continuous t)
    (hi : Function.Injective t) :
    StrictMono t ∨ StrictAnti t :=
  ht.strictMono_of_inj_boundedOrder' hi

/-- The real coordinate of an interval homeomorphism is continuous and
injective. -/
theorem intervalHomeomorph_coe_continuous_injective
    {a b : ℝ} (q : UnitInterval ≃ₜ Set.Icc a b) :
    Continuous (fun x ↦ (q x : ℝ)) ∧
      Function.Injective (fun x ↦ (q x : ℝ)) := by
  constructor
  · exact continuous_subtype_val.comp q.continuous
  · intro x y hxy
    apply q.injective
    exact Subtype.ext hxy

/-- The underlying real coordinate of an interval homeomorphism also has a
definite orientation. -/
theorem intervalHomeomorph_orientation
    {a b : ℝ} (q : UnitInterval ≃ₜ Set.Icc a b) :
    StrictMono (fun x ↦ (q x : ℝ)) ∨
      StrictAnti (fun x ↦ (q x : ℝ)) := by
  obtain ⟨hc, hi⟩ := intervalHomeomorph_coe_continuous_injective q
  exact hc.strictMono_of_inj_boundedOrder' hi

/-- The two independent orientation decisions used by B1.  Expanding this
pair yields precisely the four cases required by the repaired blueprint. -/
theorem intervalEmbedding_homeomorph_four_orientations
    {a b : ℝ} (t : UnitInterval → UnitInterval)
    (ht : Continuous t) (hi : Function.Injective t)
    (q : UnitInterval ≃ₜ Set.Icc a b) :
    (StrictMono t ∨ StrictAnti t) ∧
      (StrictMono (fun x ↦ (q x : ℝ)) ∨
        StrictAnti (fun x ↦ (q x : ℝ))) :=
  ⟨intervalEmbedding_orientation t ht hi,
    intervalHomeomorph_orientation q⟩

end t91J06Closure

#print axioms t91J06Closure.intervalEmbedding_orientation
#print axioms t91J06Closure.intervalHomeomorph_coe_continuous_injective
#print axioms t91J06Closure.intervalHomeomorph_orientation
#print axioms t91J06Closure.intervalEmbedding_homeomorph_four_orientations
