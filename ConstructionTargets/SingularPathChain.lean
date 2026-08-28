import ConstructionTargets.T02A06SphereH0

/-!
# Singular chains associated to paths

This file packages the degree-one generator represented by a continuous path
and its literal boundary in Mathlib's production singular chain complex.
-/

noncomputable section

namespace ConstructionTargets.SingularPathChain

open CategoryTheory
open ConstructionTargets.SingularSubdivision

/-- The singular one-simplex obtained from a path by the standard
one-simplex/unit-interval homeomorphism. -/
def pathSimplex {X : Type} [TopologicalSpace X] {x y : X} (gamma : Path x y) :
    C(stdSimplex ℝ (Fin 2), X) :=
  ConstructionTargets.T02A06SphereH0.singularEdgeOfPath gamma

/-- The singular zero-simplex supported at `x`. -/
def pointSimplex {X : Type} [TopologicalSpace X] (x : X) :
    C(stdSimplex ℝ (Fin 1), X) :=
  ConstructionTargets.T02A06SphereH0.singularVertexAt x

/-- The degree-one singular chain generator represented by a path. -/
def pathChain {X : Type} [TopologicalSpace X] {x y : X} (gamma : Path x y) :
    AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X 1 :=
  singularGenerator (TopCat.of X) 1
    (singularSimplexOfContinuousMap (TopCat.of X) 1 (pathSimplex gamma))

/-- The degree-zero singular chain generator supported at a point. -/
def pointChain {X : Type} [TopologicalSpace X] (x : X) :
    AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X 0 :=
  singularGenerator (TopCat.of X) 0
    (singularSimplexOfContinuousMap (TopCat.of X) 0 (pointSimplex x))

/-- The boundary of a path chain is its terminal vertex minus its initial
vertex. -/
theorem pathChain_boundary {X : Type} [TopologicalSpace X] {x y : X}
    (gamma : Path x y) :
    pathChain gamma ≫ (SingularChains (TopCat.of X)).d 1 0 =
      pointChain y - pointChain x := by
  exact ConstructionTargets.T02A06SphereH0.singularEdgeOfPath_boundary gamma

/-- A based loop represents a degree-one cycle. -/
@[simp] theorem pathChain_cycle {X : Type} [TopologicalSpace X] {x : X}
    (gamma : Path x x) :
    pathChain gamma ≫ (SingularChains (TopCat.of X)).d 1 0 = 0 := by
  rw [pathChain_boundary]
  simp

/-- The path chain regarded as an actual object of degree-one cycles. -/
noncomputable def basedLoopCycle {X : Type} [TopologicalSpace X] {x : X}
  (gamma : Path x x) :
    AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).cycles 1 :=
  (SingularChains (TopCat.of X)).liftCycles (pathChain gamma) 0 (by simp)
    (pathChain_cycle gamma)

@[reassoc (attr := simp)] theorem basedLoopCycle_i {X : Type}
    [TopologicalSpace X] {x : X} (gamma : Path x x) :
    basedLoopCycle gamma ≫ (SingularChains (TopCat.of X)).iCycles 1 =
      pathChain gamma := by
  exact (SingularChains (TopCat.of X)).liftCycles_i _ _ _ _

/-- Postcomposition takes a path simplex to the simplex of the mapped path. -/
theorem pathSimplex_postcomp {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {x y : X} (gamma : Path x y) (f : C(X, Y)) :
    f.comp (pathSimplex gamma) = pathSimplex (gamma.map f.continuous) := by
  rfl

/-- Path chains are natural under continuous postcomposition. -/
theorem pathChain_postcomp {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {x y : X} (gamma : Path x y) (f : C(X, Y)) :
    pathChain gamma ≫ (singularPostcomposition f).f 1 =
      pathChain (gamma.map f.continuous) := by
  rw [pathChain, singularGenerator_singularPostcomposition]
  congr 2

/-- Point chains are natural under continuous postcomposition. -/
theorem pointChain_postcomp {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (x : X) (f : C(X, Y)) :
    pointChain x ≫ (singularPostcomposition f).f 0 = pointChain (f x) := by
  rw [pointChain, singularGenerator_singularPostcomposition]
  rfl

/-! ## The two triangles of the path-homotopy square

The following maps record the standard triangulation
`(0,0),(1,0),(1,1)` and `(0,0),(1,1),(0,1)` of the unit square.  Keeping
these maps explicit makes the remaining face-normalization obligation
independent of any choice of a general singular-prism operator.
-/

/-- The lower/right triangle of the standard triangulation of `I × I`. -/
def lowerSquareTriangle : C(stdSimplex ℝ (Fin 3), unitInterval × unitInterval) :=
  ⟨fun z ↦
    (⟨z.1 1 + z.1 2, by
        constructor
        · exact add_nonneg (z.2.1 1) (z.2.1 2)
        · have hs := z.2.2
          rw [Fin.sum_univ_three] at hs
          linarith [z.2.1 0]⟩,
     ⟨z.1 2, by
        constructor
        · exact z.2.1 2
        · have hs := z.2.2
          rw [Fin.sum_univ_three] at hs
          linarith [z.2.1 0, z.2.1 1]⟩),
   by
    apply Continuous.prodMk
    · exact Continuous.subtype_mk
        ((continuous_apply 1).comp continuous_subtype_val |>.add
          ((continuous_apply 2).comp continuous_subtype_val)) _
    · exact Continuous.subtype_mk
        ((continuous_apply 2).comp continuous_subtype_val) _⟩

/-- The upper/left triangle of the standard triangulation of `I × I`. -/
def upperSquareTriangle : C(stdSimplex ℝ (Fin 3), unitInterval × unitInterval) :=
  ⟨fun z ↦
    (⟨z.1 1, by
        constructor
        · exact z.2.1 1
        · have hs := z.2.2
          rw [Fin.sum_univ_three] at hs
          linarith [z.2.1 0, z.2.1 2]⟩,
     ⟨z.1 1 + z.1 2, by
        constructor
        · exact add_nonneg (z.2.1 1) (z.2.1 2)
        · have hs := z.2.2
          rw [Fin.sum_univ_three] at hs
          linarith [z.2.1 0]⟩),
   by
    apply Continuous.prodMk
    · exact Continuous.subtype_mk
        ((continuous_apply 1).comp continuous_subtype_val) _
    · exact Continuous.subtype_mk
        ((continuous_apply 1).comp continuous_subtype_val |>.add
          ((continuous_apply 2).comp continuous_subtype_val)) _⟩

/-- The two singular two-simplices obtained by postcomposing a path homotopy
with the standard square triangulation. -/
def lowerHomotopySimplex {X : Type} [TopologicalSpace X] {x y : X}
    {gamma delta : Path x y} (H : Path.Homotopy gamma delta) :
    C(stdSimplex ℝ (Fin 3), X) := H.toContinuousMap.comp lowerSquareTriangle

def upperHomotopySimplex {X : Type} [TopologicalSpace X] {x y : X}
    {gamma delta : Path x y} (H : Path.Homotopy gamma delta) :
    C(stdSimplex ℝ (Fin 3), X) := H.toContinuousMap.comp upperSquareTriangle

/-- The collision-safe production two-chain associated to the two triangles.
The sign is the orientation induced by the diagonal from `(0,0)` to `(1,1)`. -/
def pathHomotopyPrismChain {X : Type} [TopologicalSpace X] {x y : X}
    {gamma delta : Path x y} (H : Path.Homotopy gamma delta) :
    AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X 2 :=
  singularGenerator (TopCat.of X) 2
      (singularSimplexOfContinuousMap _ 2 (lowerHomotopySimplex H)) +
    singularGenerator (TopCat.of X) 2
      (singularSimplexOfContinuousMap _ 2 (upperHomotopySimplex H))

/-- Raw production boundary formula for the two-triangle prism.  The residual
is now only normalization of its six affine faces; no homology or homotopy
invariance is used here. -/
theorem pathHomotopyPrismChain_boundary_raw {X : Type} [TopologicalSpace X]
    {x y : X} {gamma delta : Path x y} (H : Path.Homotopy gamma delta) :
    pathHomotopyPrismChain H ≫ (SingularChains (TopCat.of X)).d 2 1 =
      (∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) •
        singularGenerator (TopCat.of X) 1
          ((TopCat.toSSet.obj (TopCat.of X)).δ i
            (singularSimplexOfContinuousMap _ 2 (lowerHomotopySimplex H)))) +
      (∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) •
        singularGenerator (TopCat.of X) 1
          ((TopCat.toSSet.obj (TopCat.of X)).δ i
            (singularSimplexOfContinuousMap _ 2 (upperHomotopySimplex H)))) := by
  rw [pathHomotopyPrismChain, Preadditive.add_comp]
  rw [singularGenerator_boundary, singularGenerator_boundary]

#print axioms pathChain_boundary
#print axioms pathChain_cycle
#print axioms pathChain_postcomp
#print axioms pathHomotopyPrismChain_boundary_raw

end ConstructionTargets.SingularPathChain
