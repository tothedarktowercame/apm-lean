import ConstructionTargets.DegreeOneHurewiczSurjectivityFinal
import Mathlib.Order.Extension.Well
import Mathlib.Data.Finset.Sort

/-!
# Surjectivity of degree-one Hurewicz on path-connected spaces
-/

noncomputable section

namespace ConstructionTargets.DegreeOneHurewiczSurjective

open CategoryTheory
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.SingularPathChain
open ConstructionTargets.DegreeOneHurewiczMap
open ConstructionTargets.DegreeOneHurewiczSurjectivity
open ConstructionTargets.DegreeOneHurewiczDirectClosing
open ConstructionTargets.DegreeOneHurewiczSurjectivityFinal

local instance falseWellFounded (α : Type) :
    IsWellFounded α (fun _ _ => False) :=
  ⟨⟨fun a => Acc.intro a (fun _ h => h.elim)⟩⟩

local instance arbitraryLinearOrder (α : Type) : LinearOrder α :=
  IsWellFounded.wellOrderExtension (fun _ _ : α => False)

def closedEdgeFundamentalGroupClass
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (σ : OneSimplex X) : FundamentalGroup X x0 :=
  Path.Homotopic.Quotient.mk (closedEdgeLoop x0 σ)

def weightedClosedEdgeFundamentalGroupElement
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (z : (SingularChains (TopCat.of X)).X 1) :
    FundamentalGroup X x0 :=
  ((oneChainSupport z).sort (· ≤ ·)).map (fun σ =>
    closedEdgeFundamentalGroupClass x0 σ ^ (oneChainCoefficients z σ)) |>.prod

theorem fundamentalGroupH1Hom_weightedClosedEdge
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (z : (SingularChains (TopCat.of X)).X 1) :
    Multiplicative.toAdd
        (fundamentalGroupH1Hom x0
          (weightedClosedEdgeFundamentalGroupElement x0 z)) =
      ∑ σ ∈ oneChainSupport z, (oneChainCoefficients z σ) •
        basedLoopH1Element (closedEdgeLoop x0 σ) := by
  classical
  let l := (oneChainSupport z).sort (· ≤ ·)
  have hmap :
      Multiplicative.toAdd
          (fundamentalGroupH1Hom x0
            ((l.map (fun σ => closedEdgeFundamentalGroupClass x0 σ ^
              (oneChainCoefficients z σ))).prod)) =
        (l.map (fun σ => (oneChainCoefficients z σ) •
          basedLoopH1Element (closedEdgeLoop x0 σ))).sum := by
    induction l with
    | nil => simp
    | cons σ l ih =>
        simp only [List.map_cons, List.prod_cons, map_mul, map_zpow,
          closedEdgeFundamentalGroupClass, fundamentalGroupH1Hom_mk,
          List.sum_cons]
        change (oneChainCoefficients z σ) •
            basedLoopH1Element (closedEdgeLoop x0 σ) +
              Multiplicative.toAdd
                (fundamentalGroupH1Hom x0
                  ((l.map (fun τ => closedEdgeFundamentalGroupClass x0 τ ^
                    oneChainCoefficients z τ)).prod)) = _
        rw [ih]
  rw [weightedClosedEdgeFundamentalGroupElement]
  change _ = ∑ σ ∈ oneChainSupport z, _
  rw [hmap]
  rw [← List.sum_toFinset _ (Finset.sort_nodup (oneChainSupport z) (· ≤ ·))]
  simp

theorem sum_basedLoopH1Element_eq_sum_classes_apply_one
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (z : (SingularChains (TopCat.of X)).X 1) :
    ∑ σ ∈ oneChainSupport z, (oneChainCoefficients z σ) •
        basedLoopH1Element (closedEdgeLoop x0 σ) =
      (∑ σ ∈ oneChainSupport z, (oneChainCoefficients z σ) •
        basedLoopH1Class (closedEdgeLoop x0 σ)) (1 : ℤ) := by
  classical
  rw [addCommGrp_hom_sum_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  change _ = ((oneChainCoefficients z σ) •
    basedLoopH1Class (closedEdgeLoop x0 σ)) (1 : ℤ)
  change _ = (oneChainCoefficients z σ) •
    basedLoopH1Class (closedEdgeLoop x0 σ) (1 : ℤ)
  rfl

theorem fundamentalGroupH1Hom_surjective
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (x0 : X) :
    Function.Surjective (fundamentalGroupH1Hom x0) := by
  intro h
  let K := SingularChains (TopCat.of X)
  let a : IntegralH1 X := Multiplicative.toAdd h
  obtain ⟨y, hy⟩ :=
    (AddCommGrpCat.epi_iff_surjective (K.homologyπ 1)).mp inferInstance a
  let z : K.X 1 := K.iCycles 1 y
  have hz : K.d 1 0 z = 0 := by
    dsimp [z]
    rw [← CategoryTheory.comp_apply, K.iCycles_d]
    rfl
  have hlift_apply :
      K.liftCycles (chainElementHom z) 0 (by simp)
          (chainElementHom_boundary_eq_zero z hz) (1 : ℤ) = y := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles 1)).mp inferInstance
    rw [← CategoryTheory.comp_apply, K.liftCycles_i]
    change chainElementHom z (1 : ℤ) = K.iCycles 1 y
    rw [chainElementHom_apply_one]
  have hrepresentative :
      (K.liftCycles (chainElementHom z) 0 (by simp)
          (chainElementHom_boundary_eq_zero z hz) ≫ K.homologyπ 1) (1 : ℤ) = a := by
    change K.homologyπ 1
      (K.liftCycles (chainElementHom z) 0 (by simp)
        (chainElementHom_boundary_eq_zero z hz) (1 : ℤ)) = a
    rw [hlift_apply]
    exact hy
  refine ⟨weightedClosedEdgeFundamentalGroupElement x0 z, ?_⟩
  change Multiplicative.toAdd (fundamentalGroupH1Hom x0
    (weightedClosedEdgeFundamentalGroupElement x0 z)) = Multiplicative.toAdd h
  rw [fundamentalGroupH1Hom_weightedClosedEdge]
  rw [sum_basedLoopH1Element_eq_sum_classes_apply_one]
  rw [← cycle_homology_eq_sum_closedEdge_classes x0 z hz]
  exact hrepresentative

theorem abelianizedFundamentalGroupToH1_surjective
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (x0 : X) :
    Function.Surjective (abelianizedFundamentalGroupToH1 x0) := by
  intro h
  obtain ⟨g, hg⟩ := fundamentalGroupH1Hom_surjective x0 h
  exact ⟨Abelianization.of g, by simpa using hg⟩

#print axioms fundamentalGroupH1Hom_weightedClosedEdge
#print axioms fundamentalGroupH1Hom_surjective
#print axioms abelianizedFundamentalGroupToH1_surjective

end ConstructionTargets.DegreeOneHurewiczSurjective
