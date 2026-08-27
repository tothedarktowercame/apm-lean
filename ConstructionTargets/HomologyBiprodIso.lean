import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Category.Grp.Biproducts

/-!
# Canonical homology comparison for binary biproducts

This module owns the single canonical additive-functor comparison between
homology of a binary biproduct of chain complexes and the binary biproduct of
their homology objects.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.HomologyBiprodIso

/-- The canonical additive-functor comparison between homology of a chain
complex biproduct and the biproduct of homology objects. -/
noncomputable def homologyBiprodIso
    (K L : ChainComplex AddCommGrpCat ℕ) (n : ℕ) :
    (K ⊞ L).homology n ≅ K.homology n ⊞ L.homology n := by
  let F := HomologicalComplex.homologyFunctor AddCommGrpCat
    (ComplexShape.down ℕ) n
  letI : F.Additive := inferInstance
  letI : PreservesFiniteBiproducts F :=
    Functor.preservesFiniteBiproductsOfAdditive F
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  exact F.mapBiprod K L

theorem homologyBiprodIso_hom
    (K L : ChainComplex AddCommGrpCat ℕ) (n : ℕ) :
    (homologyBiprodIso K L n).hom =
      biprod.lift
        (HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) n)
        (HomologicalComplex.homologyMap (biprod.snd : K ⊞ L ⟶ L) n) := by
  rfl

theorem homologyBiprodIso_inv
    (K L : ChainComplex AddCommGrpCat ℕ) (n : ℕ) :
    (homologyBiprodIso K L n).inv =
      biprod.desc
        (HomologicalComplex.homologyMap (biprod.inl : K ⟶ K ⊞ L) n)
        (HomologicalComplex.homologyMap (biprod.inr : L ⟶ K ⊞ L) n) := by
  rfl

#print axioms homologyBiprodIso_hom
#print axioms homologyBiprodIso_inv

end ConstructionTargets.HomologyBiprodIso
