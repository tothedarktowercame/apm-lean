import ConstructionTargets.ProductSimplexAdjacentSwapCommonFace

namespace ConstructionTargets.ProductSimplexInversionCardParity

/-- Powers of `-1` attached to finite sets have opposite signs when their
cardinalities differ by exactly one. -/
theorem neg_one_pow_card_eq_neg_of_unit_difference {α : Type*}
    (s t : Finset α)
    (hcard : s.card + 1 = t.card ∨ t.card + 1 = s.card) :
    (-1 : ℤ) ^ t.card = -((-1 : ℤ) ^ s.card) := by
  rcases hcard with h | h
  · rw [← h, pow_succ]
    ring
  · rw [← h, pow_succ]
    ring

#print axioms neg_one_pow_card_eq_neg_of_unit_difference

end ConstructionTargets.ProductSimplexInversionCardParity
