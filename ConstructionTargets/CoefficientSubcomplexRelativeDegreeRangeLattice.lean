import ConstructionTargets.CoefficientSimplicialChainFinsuppRange
import ConstructionTargets.CoefficientSubcomplexSimplexRangeLattice
import ConstructionTargets.CoefficientFinsuppRangeLattice

noncomputable section
namespace ConstructionTargets.CoefficientSubcomplexRelativeDegreeRangeLattice

open CategoryTheory
open ConstructionTargets.CoefficientSubcomplexMayerVietoris
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows
open ConstructionTargets.CoefficientSigmaConstFinsuppComparison
open ConstructionTargets.CoefficientSimplicialChainFinsuppRange
open ConstructionTargets.CoefficientSubcomplexSimplexRangeLattice
open ConstructionTargets.CoefficientFinsuppRangeLattice

variable (R : Type) [CommRing R]
variable {S : SSet} (P Q : S.Subcomplex)

/-- In each degree, the intersection inclusion range is the infimum of the two
member inclusion ranges. -/
theorem intersectionRange_eq_inf (n : ℕ) :
    LinearMap.range ((intersectionAmbient R P Q).f n).hom =
      LinearMap.range ((leftAmbient R P).f n).hom ⊓
        LinearMap.range ((rightAmbient R Q).f n).hom := by
  let e := (sigmaConstFinsuppIso R
    (S.obj (Opposite.op (SimplexCategory.mk n)))).toLinearEquiv
  apply Submodule.map_injective_of_injective e.injective
  calc
    Submodule.map e.toLinearMap
        (LinearMap.range (((chains R).map (P ⊓ Q).ι).f n).hom) =
      Submodule.map e.toLinearMap
          (LinearMap.range (((chains R).map P.ι).f n).hom) ⊓
        Submodule.map e.toLinearMap
          (LinearMap.range (((chains R).map Q.ι).f n).hom) := by
            dsimp [e]
            calc
              _ = LinearMap.range (Finsupp.lmapDomain R R
                  ((P ⊓ Q).ι.app (Opposite.op (SimplexCategory.mk n)))) := by
                    simpa using chainsMap_component_range_finsupp R (P ⊓ Q).ι n
              _ = LinearMap.range (Finsupp.lmapDomain R R
                    (P.ι.app (Opposite.op (SimplexCategory.mk n)))) ⊓
                  LinearMap.range (Finsupp.lmapDomain R R
                    (Q.ι.app (Opposite.op (SimplexCategory.mk n)))) := by
                    rw [range_lmapDomain_inf, ← intersection_simplex_range,
                      ← range_lmapDomain_eq_supported_range]
              _ = _ := congrArg₂ (· ⊓ ·)
                (chainsMap_component_range_finsupp R P.ι n).symm
                (chainsMap_component_range_finsupp R Q.ι n).symm
    _ = Submodule.map e.toLinearMap
        (LinearMap.range (((chains R).map P.ι).f n).hom ⊓
          LinearMap.range (((chains R).map Q.ι).f n).hom) :=
      (Submodule.map_inf (f := e.toLinearMap) e.injective).symm

/-- In each degree, the union inclusion range is the supremum of the two
member inclusion ranges. -/
theorem unionRange_eq_sup (n : ℕ) :
    LinearMap.range ((unionAmbient R P Q).f n).hom =
      LinearMap.range ((leftAmbient R P).f n).hom ⊔
        LinearMap.range ((rightAmbient R Q).f n).hom := by
  let e := (sigmaConstFinsuppIso R
    (S.obj (Opposite.op (SimplexCategory.mk n)))).toLinearEquiv
  apply Submodule.map_injective_of_injective e.injective
  calc
    Submodule.map e.toLinearMap
        (LinearMap.range (((chains R).map (P ⊔ Q).ι).f n).hom) =
      Submodule.map e.toLinearMap
          (LinearMap.range (((chains R).map P.ι).f n).hom) ⊔
        Submodule.map e.toLinearMap
          (LinearMap.range (((chains R).map Q.ι).f n).hom) := by
            dsimp [e]
            calc
              _ = LinearMap.range (Finsupp.lmapDomain R R
                  ((P ⊔ Q).ι.app (Opposite.op (SimplexCategory.mk n)))) := by
                    simpa using chainsMap_component_range_finsupp R (P ⊔ Q).ι n
              _ = LinearMap.range (Finsupp.lmapDomain R R
                    (P.ι.app (Opposite.op (SimplexCategory.mk n)))) ⊔
                  LinearMap.range (Finsupp.lmapDomain R R
                    (Q.ι.app (Opposite.op (SimplexCategory.mk n)))) := by
                    rw [range_lmapDomain_sup, ← union_simplex_range,
                      ← range_lmapDomain_eq_supported_range]
              _ = _ := congrArg₂ (· ⊔ ·)
                (chainsMap_component_range_finsupp R P.ι n).symm
                (chainsMap_component_range_finsupp R Q.ι n).symm
    _ = Submodule.map e.toLinearMap
        (LinearMap.range (((chains R).map P.ι).f n).hom ⊔
          LinearMap.range (((chains R).map Q.ι).f n).hom) :=
      (Submodule.map_sup (f := e.toLinearMap) _ _).symm

#print axioms intersectionRange_eq_inf
#print axioms unionRange_eq_sup
end ConstructionTargets.CoefficientSubcomplexRelativeDegreeRangeLattice
