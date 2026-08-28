import ConstructionTargets.DegreeOneHurewiczSurjectivity

/-!
# Direct closing paths for degree-one Hurewicz surjectivity

This file turns every production singular one-simplex back into its interval
path, chooses basepoint connectors in a path-connected space, and records the
literal chain comparison for concatenation.  These are the geometric inputs
to the direct closing-path proof; no circulation decomposition is used.
-/

noncomputable section

namespace ConstructionTargets.DegreeOneHurewiczDirectClosing

open CategoryTheory
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.SingularPathChain
open ConstructionTargets.DegreeOneHurewiczSurjectivity

def edgeInitialPoint {X : Type} [TopologicalSpace X] (σ : OneSimplex X) : X :=
  continuousMapOfSingularSimplex 1 σ
    (stdSimplexHomeomorphUnitInterval.symm 0)

def edgeTerminalPoint {X : Type} [TopologicalSpace X] (σ : OneSimplex X) : X :=
  continuousMapOfSingularSimplex 1 σ
    (stdSimplexHomeomorphUnitInterval.symm 1)

/-- A production singular edge read as a path by the inverse of the standard
simplex/interval homeomorphism. -/
def singularEdgePath {X : Type} [TopologicalSpace X] (σ : OneSimplex X) :
    Path (edgeInitialPoint σ) (edgeTerminalPoint σ) where
  toContinuousMap := (continuousMapOfSingularSimplex 1 σ).comp
    ⟨stdSimplexHomeomorphUnitInterval.symm,
      stdSimplexHomeomorphUnitInterval.symm.continuous⟩
  source' := rfl
  target' := rfl

/-- Reading a singular edge as a path and then using the standard path
simplex returns the original continuous simplex literally. -/
theorem pathSimplex_singularEdgePath {X : Type} [TopologicalSpace X]
    (σ : OneSimplex X) :
    pathSimplex (singularEdgePath σ) = continuousMapOfSingularSimplex 1 σ := by
  ext u
  simp [pathSimplex, singularEdgePath,
    ConstructionTargets.T02A06SphereH0.singularEdgeOfPath]

/-- Consequently the production generator of an arbitrary singular edge is
the path-chain generator of its recovered path. -/
theorem pathChain_singularEdgePath {X : Type} [TopologicalSpace X]
    (σ : OneSimplex X) :
    pathChain (singularEdgePath σ) =
      singularGenerator (TopCat.of X) 1 σ := by
  rw [pathChain, pathSimplex_singularEdgePath]
  congr 2

/-- A proof-insensitive chosen path from the fixed basepoint to any point. -/
def connector {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 y : X) : Path x0 y :=
  PathConnectedSpace.somePath x0 y

/-- Close one singular edge at `x0` using the chosen paths to its two
endpoints.  The traversal order is connector-to-initial, edge, then the
reverse connector-from-terminal. -/
def closedEdgeLoop {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (σ : OneSimplex X) : Path x0 x0 :=
  (connector x0 (edgeInitialPoint σ)).trans
    ((singularEdgePath σ).trans (connector x0 (edgeTerminalPoint σ)).symm)

/-- The direct concatenation triangle works for arbitrary composable paths,
not only based loops. -/
theorem pathTrans_chain_difference_boundary
    {X : Type} [TopologicalSpace X] {x y z : X}
    (γ : Path x y) (δ : Path y z) :
    ∃ b : AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X 2,
      pathChain (γ.trans δ) - pathChain γ - pathChain δ =
        b ≫ (SingularChains (TopCat.of X)).d 2 1 := by
  refine ⟨-singularGenerator (TopCat.of X) 2
    (singularSimplexOfContinuousMap _ 2 (pathTransTriangle γ δ)), ?_⟩
  rw [Preadditive.neg_comp, pathTransTriangle_boundary]
  abel

/-- The two concatenation comparisons needed to expand a directly closed
edge into its connector, edge, and reverse-connector chains. -/
theorem closedEdgeLoop_two_concatenation_boundaries
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (σ : OneSimplex X) :
    (∃ b, pathChain (closedEdgeLoop x0 σ) -
          pathChain (connector x0 (edgeInitialPoint σ)) -
          pathChain ((singularEdgePath σ).trans
            (connector x0 (edgeTerminalPoint σ)).symm) =
        b ≫ (SingularChains (TopCat.of X)).d 2 1) ∧
      (∃ b, pathChain ((singularEdgePath σ).trans
              (connector x0 (edgeTerminalPoint σ)).symm) -
            pathChain (singularEdgePath σ) -
            pathChain (connector x0 (edgeTerminalPoint σ)).symm =
          b ≫ (SingularChains (TopCat.of X)).d 2 1) := by
  constructor
  · exact pathTrans_chain_difference_boundary
      (connector x0 (edgeInitialPoint σ))
      ((singularEdgePath σ).trans
        (connector x0 (edgeTerminalPoint σ)).symm)
  · exact pathTrans_chain_difference_boundary (singularEdgePath σ)
      (connector x0 (edgeTerminalPoint σ)).symm

#print axioms pathSimplex_singularEdgePath
#print axioms pathChain_singularEdgePath
#print axioms pathTrans_chain_difference_boundary
#print axioms closedEdgeLoop_two_concatenation_boundaries

end ConstructionTargets.DegreeOneHurewiczDirectClosing
