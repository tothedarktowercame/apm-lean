import ConstructionTargets.CoefficientFinsuppRangeLattice

noncomputable section
namespace ConstructionTargets.CoefficientSubcomplexSimplexRangeLattice

open CategoryTheory

variable {S : SSet} (P Q : S.Subcomplex)

theorem intersection_simplex_range (n : ℕ) :
    Set.range ((P ⊓ Q).ι.app (Opposite.op (SimplexCategory.mk n))) =
      Set.range (P.ι.app (Opposite.op (SimplexCategory.mk n))) ∩
        Set.range (Q.ι.app (Opposite.op (SimplexCategory.mk n))) := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨⟨⟨τ.1, τ.2.1⟩, rfl⟩, ⟨⟨τ.1, τ.2.2⟩, rfl⟩⟩
  · rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    subst σ
    have hpq : p.1 = q.1 := by simpa using hq.symm
    have hq' : p.1 ∈ Q.obj (Opposite.op (SimplexCategory.mk n)) := hpq ▸ q.2
    exact ⟨⟨p.1, p.2, hq'⟩, rfl⟩

theorem union_simplex_range (n : ℕ) :
    Set.range ((P ⊔ Q).ι.app (Opposite.op (SimplexCategory.mk n))) =
      Set.range (P.ι.app (Opposite.op (SimplexCategory.mk n))) ∪
        Set.range (Q.ι.app (Opposite.op (SimplexCategory.mk n))) := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rcases τ.2 with h | h
    · exact Or.inl ⟨⟨τ.1, h⟩, rfl⟩
    · exact Or.inr ⟨⟨τ.1, h⟩, rfl⟩
  · rintro (⟨p, rfl⟩ | ⟨q, rfl⟩)
    · exact ⟨⟨p.1, Or.inl p.2⟩, rfl⟩
    · exact ⟨⟨q.1, Or.inr q.2⟩, rfl⟩

#print axioms intersection_simplex_range
#print axioms union_simplex_range
end ConstructionTargets.CoefficientSubcomplexSimplexRangeLattice
