import ConstructionTargets.GenericPointWedgeOpenCoverComparison

open Set Topology
open scoped ContinuousMap
noncomputable section

namespace ConstructionTargets.GenericPointWedgeOverlapInclusionSquares

open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.PointWedgePointedContractionDescent
open ConstructionTargets.PointedPuncturedCircleContraction
open ConstructionTargets.GenericPointWedgeOpenCoverComparison
open ConstructionTargets.TorusCircleWedgeOpenCover

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

def overlapToLeft (x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X) :
    C({z // z ∈ leftOpen x₀ y₀ M ∩ rightOpen x₀ y₀ N},
      {z // z ∈ leftOpen x₀ y₀ M}) :=
  ⟨fun z => ⟨z.1, z.2.1⟩, continuous_subtype_val.subtype_mk _⟩

def overlapToRight (x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X) :
    C({z // z ∈ leftOpen x₀ y₀ M ∩ rightOpen x₀ y₀ N},
      {z // z ∈ rightOpen x₀ y₀ N}) :=
  ⟨fun z => ⟨z.1, z.2.2⟩, continuous_subtype_val.subtype_mk _⟩

theorem genericPointWedgeOverlapInclusionSquares
    (x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X)
    (hM : IsOpen M) (hN : IsOpen N) (hy : y₀ ∈ M) (hx : x₀ ∈ N)
    (cM : PointedContraction M ⟨y₀, hy⟩)
    (cN : PointedContraction N ⟨x₀, hx⟩) :
    let p := genericPointWedgeCoverPackage x₀ y₀ M N hM hN hy hx cM cN
    p.leftEquiv.toFun.comp
        ((overlapToLeft x₀ y₀ M N).comp p.intersectionEquiv.invFun) =
      ContinuousMap.const Unit x₀ ∧
    p.rightEquiv.toFun.comp
        ((overlapToRight x₀ y₀ M N).comp p.intersectionEquiv.invFun) =
      ContinuousMap.const Unit y₀ := by
  let p := genericPointWedgeCoverPackage x₀ y₀ M N hM hN hy hx cM cN
  let z₀ : {z // z ∈ leftOpen x₀ y₀ M ∩ rightOpen x₀ y₀ N} :=
    ⟨quotientMap x₀ y₀ (.inl x₀),
      ⟨⟨.inl x₀, trivial, rfl⟩, ⟨.inl x₀, hx, rfl⟩⟩⟩
  have hInv : p.intersectionEquiv.invFun () = z₀ := by
    dsimp [p, z₀, genericPointWedgeCoverPackage,
      genericPointWedgeIntersectionHomotopyEquiv,
      pointedContractionHomotopyEquivUnit, wedgeHomotopyEquivLeft, includeLeft,
      ContinuousMap.HomotopyEquiv.trans, ContinuousMap.HomotopyEquiv.symm,
      Homeomorph.toHomotopyEquiv]
    apply Subtype.ext
    rfl
  change p.leftEquiv.toFun.comp
        ((overlapToLeft x₀ y₀ M N).comp p.intersectionEquiv.invFun) =
      ContinuousMap.const Unit x₀ ∧
    p.rightEquiv.toFun.comp
        ((overlapToRight x₀ y₀ M N).comp p.intersectionEquiv.invFun) =
      ContinuousMap.const Unit y₀
  constructor <;> ext u <;> cases u
  · change p.leftEquiv.toFun
      (overlapToLeft x₀ y₀ M N (p.intersectionEquiv.invFun ())) = x₀
    rw [hInv]
    exact p.left_inclusion x₀
  · change p.rightEquiv.toFun
      (overlapToRight x₀ y₀ M N (p.intersectionEquiv.invFun ())) = y₀
    rw [hInv]
    have hz : overlapToRight x₀ y₀ M N z₀ =
        ⟨quotientMap x₀ y₀ (.inr y₀), ⟨.inr y₀, trivial, rfl⟩⟩ := by
      apply Subtype.ext
      exact Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)
    rw [hz]
    exact p.right_inclusion y₀

#print axioms genericPointWedgeOverlapInclusionSquares

end ConstructionTargets.GenericPointWedgeOverlapInclusionSquares
