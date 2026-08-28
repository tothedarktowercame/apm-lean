import ConstructionTargets.EmptyAndSumSingularHomology
import ConstructionTargets.T00A01MayerVietorisAdapters

/-!
# Integral singular homology of a topological sum

The two clopen summands form a production open cover.  Its empty intersection
turns the production reassembly arrow into an isomorphism in every degree.
-/

open Set Topology CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.TopologicalSumSingularHomology

open ConstructionTargets.EmptyAndSumSingularHomology
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.T00A01MayerVietorisAdapters

variable (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]

def leftSummand : Set (X ⊕ Y) := Set.range Sum.inl

def rightSummand : Set (X ⊕ Y) := Set.range Sum.inr

theorem leftSummand_isOpen : IsOpen (leftSummand X Y) := isOpen_range_inl

theorem rightSummand_isOpen : IsOpen (rightSummand X Y) := isOpen_range_inr

theorem leftSummand_union_rightSummand :
    leftSummand X Y ∪ rightSummand X Y = Set.univ := by
  ext z
  rcases z with x | y <;> simp [leftSummand, rightSummand]

noncomputable def leftSummandHomeomorph : leftSummand X Y ≃ₜ X :=
  Topology.IsEmbedding.inl.toHomeomorph.symm

noncomputable def rightSummandHomeomorph : rightSummand X Y ≃ₜ Y :=
  Topology.IsEmbedding.inr.toHomeomorph.symm

instance intersectionIsEmpty :
    IsEmpty (leftSummand X Y ∩ rightSummand X Y : Set (X ⊕ Y)) :=
  ⟨fun z => by
    rcases z with ⟨x | y, hx, hy⟩
    · rcases hy with ⟨y, h⟩
      contradiction
    · rcases hx with ⟨x, h⟩
      contradiction⟩

def intersectionHomeomorphEmpty :
    (leftSummand X Y ∩ rightSummand X Y : Set (X ⊕ Y)) ≃ₜ Empty where
  toFun z := isEmptyElim z
  invFun z := isEmptyElim z
  left_inv z := isEmptyElim z
  right_inv z := isEmptyElim z
  continuous_toFun := by
    rw [continuous_def]
    intro s hs
    convert isOpen_empty
    ext z
    exact isEmptyElim z
  continuous_invFun := by
    rw [continuous_def]
    intro s hs
    convert isOpen_empty
    ext z
    exact isEmptyElim z

abbrev H (k : ℕ) (Z : Type) [TopologicalSpace Z] :=
  SingularHomology k (TopCat.of Z)

noncomputable def leftSummandHomologyIso (k : ℕ) :
    H k (leftSummand X Y) ≅ H k X :=
  ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).mapIso (TopCat.isoOfHomeo (leftSummandHomeomorph X Y))

noncomputable def rightSummandHomologyIso (k : ℕ) :
    H k (rightSummand X Y) ≅ H k Y :=
  ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).mapIso (TopCat.isoOfHomeo (rightSummandHomeomorph X Y))

theorem intersectionHomology_isZero (k : ℕ) :
    IsZero (H k (leftSummand X Y ∩ rightSummand X Y : Set (X ⊕ Y))) :=
  (emptySingularHomology_isZero k).of_iso
    (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj
      (AddCommGrpCat.of ℤ)).mapIso
        (TopCat.isoOfHomeo (intersectionHomeomorphEmpty X Y)))

noncomputable instance productionReassembly_isIso (k : ℕ) :
    IsIso (productionReassemblyArrow (leftSummand X Y) (rightSummand X Y) k) := by
  haveI : Mono
      (productionReassemblyArrow (leftSummand X Y) (rightSummand X Y) k) :=
    (productionMayerVietoris_exact_pieces
      (leftSummand X Y) (rightSummand X Y)
      (leftSummand_isOpen X Y) (rightSummand_isOpen X Y)
      (leftSummand_union_rightSummand X Y) k).mono_g_iff.mpr
        ((intersectionHomology_isZero X Y k).eq_of_src _ _)
  haveI : Epi
      (productionReassemblyArrow (leftSummand X Y) (rightSummand X Y) k) := by
    rcases k with _ | k
    · exact productionReassemblyArrow_epi_zero
        (leftSummand X Y) (rightSummand X Y)
        (leftSummand_isOpen X Y) (rightSummand_isOpen X Y)
        (leftSummand_union_rightSummand X Y)
    · exact (productionMayerVietoris_exact_union
        (leftSummand X Y) (rightSummand X Y)
        (leftSummand_isOpen X Y) (rightSummand_isOpen X Y)
        (leftSummand_union_rightSummand X Y) k).epi_f_iff.mpr
          ((intersectionHomology_isZero X Y k).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Integral singular homology sends a binary topological sum to the
categorical biproduct of the two homologies. -/
noncomputable def sumHomologyIsoBiprod (k : ℕ) :=
  (asIso (productionReassemblyArrow
      (leftSummand X Y) (rightSummand X Y) k)).symm ≪≫
    biprod.mapIso (leftSummandHomologyIso X Y k)
      (rightSummandHomologyIso X Y k)

#print axioms leftSummand_union_rightSummand
#print axioms intersectionHomeomorphEmpty
#print axioms intersectionHomology_isZero
#print axioms productionReassembly_isIso
#print axioms sumHomologyIsoBiprod

end ConstructionTargets.TopologicalSumSingularHomology
