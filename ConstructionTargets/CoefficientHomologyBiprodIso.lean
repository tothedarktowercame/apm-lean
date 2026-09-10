import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Category.ModuleCat.Biproducts

open CategoryTheory CategoryTheory.Limits

noncomputable section
namespace ConstructionTargets.CoefficientHomologyBiprodIso

variable (R : Type) [CommRing R]

noncomputable def homologyBiprodIso
    (K L : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    (K ⊞ L).homology n ≅ K.homology n ⊞ L.homology n := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat R)
    (ComplexShape.down ℕ) n
  letI : F.Additive := inferInstance
  letI : PreservesFiniteBiproducts F :=
    Functor.preservesFiniteBiproductsOfAdditive F
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  exact F.mapBiprod K L

theorem homologyBiprodIso_hom
    (K L : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    (homologyBiprodIso R K L n).hom =
      biprod.lift
        (HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) n)
        (HomologicalComplex.homologyMap (biprod.snd : K ⊞ L ⟶ L) n) := by
  rfl

theorem homologyBiprodIso_inv
    (K L : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    (homologyBiprodIso R K L n).inv =
      biprod.desc
        (HomologicalComplex.homologyMap (biprod.inl : K ⟶ K ⊞ L) n)
        (HomologicalComplex.homologyMap (biprod.inr : L ⟶ K ⊞ L) n) := by
  rfl

#print axioms homologyBiprodIso
#print axioms homologyBiprodIso_hom
#print axioms homologyBiprodIso_inv
end ConstructionTargets.CoefficientHomologyBiprodIso
