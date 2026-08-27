import ConstructionTargets.ModelPairLocalHomologyOne
import ConstructionTargets.SingularExcision

/-!
# Relative singular homology transport through a homeomorphism of pairs

A homeomorphism of ambient spaces which identifies two distinguished subsets
induces an isomorphism on relative singular homology.  The result is stated
without manifold or orientation assumptions: a chart consumer supplies the
homeomorphism and the exact subset-membership equivalence.
-/

noncomputable section

namespace ConstructionTargets.ChartPairRelativeHomologyTransport

open CategoryTheory
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.T02A06HemisphereExcision
open ConstructionTargets.T02A06DiskRadialComparison
open ConstructionTargets.ModelPairLocalHomologyOne

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Restriction of an ambient homeomorphism to subsets it identifies exactly. -/
def pairRestriction (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (hAB : ∀ x, x ∈ A ↔ e x ∈ B) : A ≃ₜ B :=
  e.subtype hAB

/-- The continuous ambient map underlying a homeomorphism of pairs. -/
def pairContinuousMap (e : X ≃ₜ Y) : C(X, Y) :=
  ⟨e, e.continuous⟩

theorem pairContinuousMap_mapsTo (e : X ≃ₜ Y)
    (A : Set X) (B : Set Y) (hAB : ∀ x, x ∈ A ↔ e x ∈ B) :
    Set.MapsTo (pairContinuousMap e) A B := by
  intro x hx
  exact (hAB x).1 hx

/-- The production subspace map of a homeomorphism of pairs is literally the
TopCat morphism induced by the restricted homeomorphism. -/
theorem subspaceMap_pairContinuousMap_eq_isoHom (e : X ≃ₜ Y)
    (A : Set X) (B : Set Y) (hAB : ∀ x, x ∈ A ↔ e x ∈ B) :
    subspaceMap A B (pairContinuousMap e)
        (pairContinuousMap_mapsTo e A B hAB) =
      (TopCat.isoOfHomeo (pairRestriction e A B hAB)).hom := by
  rfl

/-- A homeomorphism identifying the distinguished subsets induces an
isomorphism on relative singular homology in every degree. -/
theorem relativeSingularMap_homeomorphPair_isIso (e : X ≃ₜ Y)
    (A : Set X) (B : Set Y) (hAB : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap A B (pairContinuousMap e)
        (pairContinuousMap_mapsTo e A B hAB)) n) := by
  apply relativeSingularMap_homologyMap_isIso
  · change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
      (AddCommGrpCat.of ℤ)).map _)
    rw [subspaceMap_pairContinuousMap_eq_isoHom e A B hAB]
    infer_instance
  · change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat n).obj
      (AddCommGrpCat.of ℤ)).map _)
    rw [show TopCat.ofHom (pairContinuousMap e) =
      (TopCat.isoOfHomeo e).hom by rfl]
    infer_instance
  · intro j hj
    change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat j).obj
      (AddCommGrpCat.of ℤ)).map _)
    rw [subspaceMap_pairContinuousMap_eq_isoHom e A B hAB]
    infer_instance
  · intro j hj
    change IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat j).obj
      (AddCommGrpCat.of ℤ)).map _)
    rw [show TopCat.ofHom (pairContinuousMap e) =
      (TopCat.isoOfHomeo e).hom by rfl]
    infer_instance

/-- The relative-homology isomorphism induced by a homeomorphism of pairs. -/
noncomputable def relativeSingularHomologyIsoOfHomeomorphPair
    (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (hAB : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ) :
    (RelativeSingularChains A).homology n ≅
      (RelativeSingularChains B).homology n :=
  @asIso _ _ _ _
    (HomologicalComplex.homologyMap
      (relativeSingularMap A B (pairContinuousMap e)
        (pairContinuousMap_mapsTo e A B hAB)) n)
    (relativeSingularMap_homeomorphPair_isIso e A B hAB n)

/-- Transport an arbitrary relative class through a homeomorphism of pairs. -/
noncomputable def transportedRelativeClass
    (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (hAB : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ)
    (z : (RelativeSingularChains A).homology n) :
    (RelativeSingularChains B).homology n :=
  (relativeSingularHomologyIsoOfHomeomorphPair e A B hAB n).hom z

theorem transportedRelativeClass_ne_zero
    (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (hAB : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ)
    (z : (RelativeSingularChains A).homology n) (hz : z ≠ 0) :
    transportedRelativeClass e A B hAB n z ≠ 0 := by
  intro hzero
  apply hz
  have h := congrArg
    (fun q => (relativeSingularHomologyIsoOfHomeomorphPair e A B hAB n).inv q)
    hzero
  simpa [transportedRelativeClass] using h

/-- The oriented local generator transported from the punctured open
one-dimensional model through a supplied homeomorphism of pairs. -/
noncomputable def transportedOpenDiskOnePunctureGenerator
    (e : euclideanOpenDisk 1 ≃ₜ Y) (B : Set Y)
    (hB : ∀ x, x ∈ puncturedOpenDiskSet 1 ↔ e x ∈ B) :
    (RelativeSingularChains B).homology 1 :=
  transportedRelativeClass e (puncturedOpenDiskSet 1) B hB 1
    openDiskOnePunctureRelativeH1Generator

theorem transportedOpenDiskOnePunctureGenerator_eq_map
    (e : euclideanOpenDisk 1 ≃ₜ Y) (B : Set Y)
    (hB : ∀ x, x ∈ puncturedOpenDiskSet 1 ↔ e x ∈ B) :
    transportedOpenDiskOnePunctureGenerator e B hB =
      HomologicalComplex.homologyMap
        (relativeSingularMap (puncturedOpenDiskSet 1) B (pairContinuousMap e)
          (pairContinuousMap_mapsTo e (puncturedOpenDiskSet 1) B hB)) 1
        openDiskOnePunctureRelativeH1Generator := by
  rfl

theorem transportedOpenDiskOnePunctureGenerator_ne_zero
    (e : euclideanOpenDisk 1 ≃ₜ Y) (B : Set Y)
    (hB : ∀ x, x ∈ puncturedOpenDiskSet 1 ↔ e x ∈ B) :
    transportedOpenDiskOnePunctureGenerator e B hB ≠ 0 :=
  transportedRelativeClass_ne_zero e (puncturedOpenDiskSet 1) B hB 1
    openDiskOnePunctureRelativeH1Generator
    openDiskOnePunctureRelativeH1Generator_ne_zero

#print axioms relativeSingularMap_homeomorphPair_isIso
#print axioms relativeSingularHomologyIsoOfHomeomorphPair
#print axioms transportedRelativeClass_ne_zero
#print axioms transportedOpenDiskOnePunctureGenerator_eq_map
#print axioms transportedOpenDiskOnePunctureGenerator_ne_zero

end ConstructionTargets.ChartPairRelativeHomologyTransport
