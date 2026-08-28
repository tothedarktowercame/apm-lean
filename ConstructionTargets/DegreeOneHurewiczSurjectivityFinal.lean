import ConstructionTargets.DegreeOneHurewiczDirectClosing

/-!
# Direct closing-path assembly for degree-one Hurewicz

This file combines the two concatenation triangles and the unnormalized
backtracking filler into the individual closed-edge boundary formula used by
the finite support argument.
-/

noncomputable section

namespace ConstructionTargets.DegreeOneHurewiczSurjectivityFinal

open CategoryTheory
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.SingularPathChain
open ConstructionTargets.DegreeOneHurewiczSurjectivity
open ConstructionTargets.DegreeOneHurewiczDirectClosing
open ConstructionTargets.DegreeOneHurewiczMap

/-- Closing a single singular edge changes its path chain by the initial
connector minus the terminal connector, modulo an explicit production
boundary. -/
theorem closedEdgeLoop_chain_formula
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (σ : OneSimplex X) :
    ∃ b : AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X 2,
      pathChain (closedEdgeLoop x0 σ) - pathChain (singularEdgePath σ) -
          pathChain (connector x0 (edgeInitialPoint σ)) +
          pathChain (connector x0 (edgeTerminalPoint σ)) =
        b ≫ (SingularChains (TopCat.of X)).d 2 1 := by
  obtain ⟨⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩⟩ :=
    closedEdgeLoop_two_concatenation_boundaries x0 σ
  let b₃ := backtrackingBoundaryChain
    (connector x0 (edgeTerminalPoint σ))
  have hb₃ := backtrackingBoundaryChain_boundary
    (connector x0 (edgeTerminalPoint σ))
  refine ⟨b₁ + b₂ + b₃, ?_⟩
  rw [Preadditive.add_comp, Preadditive.add_comp, ← hb₁, ← hb₂]
  dsimp [b₃]
  rw [hb₃]
  abel

/-- A chosen boundary witness for the individual closed-edge formula. -/
def closedEdgeBoundaryWitness
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (σ : OneSimplex X) :
    AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X 2 :=
  (closedEdgeLoop_chain_formula x0 σ).choose

theorem closedEdgeBoundaryWitness_boundary
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (σ : OneSimplex X) :
    pathChain (closedEdgeLoop x0 σ) - pathChain (singularEdgePath σ) -
          pathChain (connector x0 (edgeInitialPoint σ)) +
          pathChain (connector x0 (edgeTerminalPoint σ)) =
      closedEdgeBoundaryWitness x0 σ ≫
        (SingularChains (TopCat.of X)).d 2 1 :=
  (closedEdgeLoop_chain_formula x0 σ).choose_spec

/-- The coefficient-weighted finite sum of all individual closing defects is
one production boundary.  This is the finite assembly before vertex-balance
regroups and cancels the connector terms. -/
theorem weighted_closedEdge_defects_boundary
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (z : (SingularChains (TopCat.of X)).X 1) :
    ∑ σ ∈ oneChainSupport z,
        (oneChainCoefficients z σ) •
          (pathChain (closedEdgeLoop x0 σ) -
            pathChain (singularEdgePath σ) -
            pathChain (connector x0 (edgeInitialPoint σ)) +
            pathChain (connector x0 (edgeTerminalPoint σ))) =
      (∑ σ ∈ oneChainSupport z,
          (oneChainCoefficients z σ) • closedEdgeBoundaryWitness x0 σ) ≫
        (SingularChains (TopCat.of X)).d 2 1 := by
  rw [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Preadditive.zsmul_comp, ← closedEdgeBoundaryWitness_boundary]

#print axioms closedEdgeLoop_chain_formula
#print axioms weighted_closedEdge_defects_boundary

end ConstructionTargets.DegreeOneHurewiczSurjectivityFinal
