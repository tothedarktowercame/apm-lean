import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Negation naturality for connecting morphisms

This file isolates the sign calculation used when a morphism between short
exact sequences acts by `-𝟙` on the first term and by `𝟙` on the third term.
-/

open CategoryTheory

noncomputable section

namespace ConstructionTargets.ConnectingMapNegationNaturality

open HomologicalComplex

variable {C ι : Type*} [Category* C] [Abelian C]
  {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)}

/-- The elementary same-object sign calculation used after a connecting-map
naturality square has been transported to common source and target objects. -/
theorem eq_neg_of_comp_neg_id_eq_id_comp
    {X Y : C} (f g : X ⟶ Y)
    (h : f ≫ (-𝟙 Y) = (𝟙 X) ≫ g) : g = -f := by
  simpa only [Preadditive.comp_neg, Category.comp_id, Category.id_comp] using h.symm

/-- Iso-transported form of the same calculation.  This is the form needed
when swapping the intersection and union objects in a Mayer--Vietoris short
complex: the first component is the negative of an identification, while the
third component is an identification. -/
theorem delta_eq_neg_of_first_neg_iso_third_iso
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (e₁ : S₁.X₁ ≅ S₂.X₁) (e₃ : S₁.X₃ ≅ S₂.X₃)
    (h₁ : φ.τ₁ = -e₁.hom) (h₃ : φ.τ₃ = e₃.hom)
    (i j : ι) (hij : c.Rel i j) :
    hS₂.δ i j hij =
      HomologicalComplex.homologyMap e₃.inv i ≫
        (-hS₁.δ i j hij) ≫
          HomologicalComplex.homologyMap e₁.hom j := by
  have h := HomologicalComplex.HomologySequence.δ_naturality
    φ hS₁ hS₂ i j hij
  rw [h₁, h₃, HomologicalComplex.homologyMap_neg] at h
  apply (cancel_epi (HomologicalComplex.homologyMap e₃.hom i)).1
  rw [← HomologicalComplex.homologyMap_comp_assoc, e₃.hom_inv_id,
    HomologicalComplex.homologyMap_id, Category.id_comp]
  simpa only [Category.assoc, Preadditive.comp_neg,
    Preadditive.neg_comp] using h.symm

#print axioms eq_neg_of_comp_neg_id_eq_id_comp
#print axioms delta_eq_neg_of_first_neg_iso_third_iso

end ConstructionTargets.ConnectingMapNegationNaturality
