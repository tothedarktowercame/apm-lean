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

theorem lowerHomotopySimplex_face_zero {X : Type} [TopologicalSpace X]
    {x y : X} {gamma delta : Path x y} (H : Path.Homotopy gamma delta) :
    (TopCat.toSSet.obj (TopCat.of X)).δ (0 : Fin 3)
        (singularSimplexOfContinuousMap _ 2 (lowerHomotopySimplex H)) =
      singularSimplexOfContinuousMap _ 1 (pathSimplex delta) := by
  rw [singularSimplexOfContinuousMap_face]
  congr 1
  ext z
  simp [lowerHomotopySimplex, lowerSquareTriangle, pathSimplex,
    ConstructionTargets.T02A06SphereH0.singularEdgeOfPath, affineSimplex]
  calc
    _ = H (1, stdSimplexHomeomorphUnitInterval z) := by
      apply congrArg H
      apply Prod.ext <;> apply Subtype.ext
      · simpa [Fin.sum_univ_two] using z.2.2
      · change z.1 1 = z.1 1
        rfl
    _ = _ := H.map_one_left _

theorem upperHomotopySimplex_face_one {X : Type} [TopologicalSpace X]
    {x y : X} {gamma delta : Path x y} (H : Path.Homotopy gamma delta) :
    (TopCat.toSSet.obj (TopCat.of X)).δ (1 : Fin 3)
        (singularSimplexOfContinuousMap _ 2 (upperHomotopySimplex H)) =
      singularSimplexOfContinuousMap _ 1 (pathSimplex gamma) := by
  rw [singularSimplexOfContinuousMap_face]
  congr 1
  ext z
  simp [upperHomotopySimplex, upperSquareTriangle, pathSimplex,
    ConstructionTargets.T02A06SphereH0.singularEdgeOfPath, affineSimplex]
  apply congrArg gamma
  apply Subtype.ext
  simp [stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc, Fin.succAbove]
  rfl

theorem homotopySimplex_diagonal_faces {X : Type} [TopologicalSpace X]
    {x y : X} {gamma delta : Path x y} (H : Path.Homotopy gamma delta) :
    (TopCat.toSSet.obj (TopCat.of X)).δ (1 : Fin 3)
        (singularSimplexOfContinuousMap _ 2 (lowerHomotopySimplex H)) =
      (TopCat.toSSet.obj (TopCat.of X)).δ (2 : Fin 3)
        (singularSimplexOfContinuousMap _ 2 (upperHomotopySimplex H)) := by
  rw [singularSimplexOfContinuousMap_face,
    singularSimplexOfContinuousMap_face]
  congr 1
  ext z
  simp [lowerHomotopySimplex, upperHomotopySimplex, lowerSquareTriangle,
    upperSquareTriangle, affineSimplex]
  apply congrArg H
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [Fin.succAbove]

theorem lowerHomotopySimplex_face_two {X : Type} [TopologicalSpace X]
    {x y : X} {gamma delta : Path x y} (H : Path.Homotopy gamma delta) :
    (TopCat.toSSet.obj (TopCat.of X)).δ (2 : Fin 3)
        (singularSimplexOfContinuousMap _ 2 (lowerHomotopySimplex H)) =
      singularSimplexOfContinuousMap _ 1 (pathSimplex (Path.refl x)) := by
  rw [singularSimplexOfContinuousMap_face]
  congr 1
  ext z
  simp [lowerHomotopySimplex, lowerSquareTriangle, pathSimplex,
    ConstructionTargets.T02A06SphereH0.singularEdgeOfPath, affineSimplex]

theorem upperHomotopySimplex_face_zero {X : Type} [TopologicalSpace X]
    {x y : X} {gamma delta : Path x y} (H : Path.Homotopy gamma delta) :
    (TopCat.toSSet.obj (TopCat.of X)).δ (0 : Fin 3)
        (singularSimplexOfContinuousMap _ 2 (upperHomotopySimplex H)) =
      singularSimplexOfContinuousMap _ 1 (pathSimplex (Path.refl y)) := by
  rw [singularSimplexOfContinuousMap_face]
  congr 1
  ext z
  simp [upperHomotopySimplex, upperSquareTriangle, pathSimplex,
    ConstructionTargets.T02A06SphereH0.singularEdgeOfPath, affineSimplex]
  calc
    _ = H (⟨z.1 0, by
          constructor
          · exact z.2.1 0
          · have hs := z.2.2
            rw [Fin.sum_univ_two] at hs
            linarith [z.2.1 1]⟩, 1) := by
      apply congrArg H
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        simpa [Fin.sum_univ_two] using z.2.2
    _ = y := H.target _

/-- The completely degenerate singular two-simplex at a point. -/
def constantTwoSimplex {X : Type} [TopologicalSpace X] (x : X) :
    C(stdSimplex ℝ (Fin 3), X) := ContinuousMap.const _ x

/-- In the unnormalized singular complex, the alternating boundary of a
constant two-simplex is the constant one-simplex. -/
theorem constantTwoSimplex_boundary {X : Type} [TopologicalSpace X] (x : X) :
    singularGenerator (TopCat.of X) 2
        (singularSimplexOfContinuousMap _ 2 (constantTwoSimplex x)) ≫
        (SingularChains (TopCat.of X)).d 2 1 =
      pathChain (Path.refl x) := by
  rw [singularGenerator_boundary]
  rw [Fin.sum_univ_three]
  simp [pathChain, pathSimplex, constantTwoSimplex,
    singularSimplexOfContinuousMap_face,
    ConstructionTargets.T02A06SphereH0.singularEdgeOfPath]
  congr 2

/-- The six prism faces normalize to top minus bottom, the two constant side
edges, and two opposite copies of the diagonal. -/
theorem pathHomotopyPrismChain_boundary {X : Type} [TopologicalSpace X]
    {x y : X} {gamma delta : Path x y} (H : Path.Homotopy gamma delta) :
    pathHomotopyPrismChain H ≫ (SingularChains (TopCat.of X)).d 2 1 =
      pathChain delta - pathChain gamma + pathChain (Path.refl x) +
        pathChain (Path.refl y) := by
  rw [pathHomotopyPrismChain_boundary_raw]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  rw [lowerHomotopySimplex_face_zero H,
    upperHomotopySimplex_face_one H,
    lowerHomotopySimplex_face_two H,
    upperHomotopySimplex_face_zero H,
    homotopySimplex_diagonal_faces H]
  simp [pathChain, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Subtracting the two explicit degenerate fillers removes the constant side
edges without passing to normalized chains. -/
def pathHomotopyBoundaryChain {X : Type} [TopologicalSpace X]
    {x y : X} {gamma delta : Path x y} (H : Path.Homotopy gamma delta) :
    AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X 2 :=
  pathHomotopyPrismChain H -
    singularGenerator (TopCat.of X) 2
      (singularSimplexOfContinuousMap _ 2 (constantTwoSimplex x)) -
    singularGenerator (TopCat.of X) 2
      (singularSimplexOfContinuousMap _ 2 (constantTwoSimplex y))

theorem pathHomotopyBoundaryChain_boundary {X : Type} [TopologicalSpace X]
    {x y : X} {gamma delta : Path x y} (H : Path.Homotopy gamma delta) :
    pathHomotopyBoundaryChain H ≫ (SingularChains (TopCat.of X)).d 2 1 =
      pathChain delta - pathChain gamma := by
  rw [pathHomotopyBoundaryChain, Preadditive.sub_comp, Preadditive.sub_comp,
    pathHomotopyPrismChain_boundary H, constantTwoSimplex_boundary,
    constantTwoSimplex_boundary]
  abel

/-- The integral first-homology class represented by a based loop. -/
noncomputable def basedLoopH1Class {X : Type} [TopologicalSpace X] {x : X}
    (gamma : Path x x) :
    AddCommGrpCat.of ℤ ⟶
      ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
        (TopCat.of X) :=
  basedLoopCycle gamma ≫ (SingularChains (TopCat.of X)).homologyπ 1

/-- Path-homotopic based loops determine the same integral first-homology
class.  The proof uses the explicit unnormalized filler above. -/
theorem basedLoopH1Class_eq_of_homotopy {X : Type} [TopologicalSpace X]
    {x : X} {gamma delta : Path x x} (H : Path.Homotopy gamma delta) :
    basedLoopH1Class gamma = basedLoopH1Class delta := by
  let K := SingularChains (TopCat.of X)
  let c := pathChain delta - pathChain gamma
  have hc : c ≫ K.d 1 0 = 0 := by
    dsimp [c, K]
    rw [Preadditive.sub_comp, pathChain_cycle, pathChain_cycle, sub_zero]
  have hboundary : c = pathHomotopyBoundaryChain H ≫ K.d 2 1 := by
    exact (pathHomotopyBoundaryChain_boundary H).symm
  have hzero : K.liftCycles c 0 (by simp) hc ≫ K.homologyπ 1 = 0 :=
    K.liftCycles_homologyπ_eq_zero_of_boundary c 0 (by simp)
      (pathHomotopyBoundaryChain H) hboundary
  have hlift : K.liftCycles c 0 (by simp) hc =
      basedLoopCycle delta - basedLoopCycle gamma := by
    apply (cancel_mono (K.iCycles 1)).1
    rw [K.liftCycles_i, Preadditive.sub_comp, basedLoopCycle_i,
      basedLoopCycle_i]
  have hclasses : basedLoopH1Class delta - basedLoopH1Class gamma = 0 := by
    rw [basedLoopH1Class, basedLoopH1Class]
    rw [← Preadditive.sub_comp, ← hlift]
    exact hzero
  exact (sub_eq_zero.mp hclasses).symm

/-! ## Reduction of concatenation additivity to the oriented edge split -/

/-- The production barycentric subdivision of the singular edge represented
by a path. -/
def subdividedPathChain {X : Type} [TopologicalSpace X] {x y : X}
    (gamma : Path x y) :
    AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X 1 :=
  pathChain gamma ≫ singularSubdivisionDegree 1

/-- For a based loop, the production subdivision differs from the original
edge by the boundary of the production singular prism. -/
theorem basedLoop_subdivision_difference_boundary {X : Type}
    [TopologicalSpace X] {x : X} (gamma : Path x x) :
    ∃ b : AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X 2,
      subdividedPathChain gamma - pathChain gamma =
        b ≫ (SingularChains (TopCat.of X)).d 2 1 := by
  simpa [subdividedPathChain] using
    productionCycle_homologous_to_subdivision 0 (pathChain gamma)
      (pathChain_cycle gamma)

/-- The exact remaining degree-one normalization statement.  It is kept as a
predicate because the recursive production subdivision orders the first half
as a barycentre-first edge; identifying it with the forward first path needs
an explicit edge-reversal two-simplex. -/
def PathTransSubdivisionFormula {X : Type} [TopologicalSpace X]
    {x y z : X} (gamma : Path x y) (delta : Path y z) : Prop :=
  subdividedPathChain (gamma.trans delta) =
    pathChain gamma + pathChain delta

/-- Once the explicit oriented-edge normalization is supplied, the already
compiled production prism gives the desired concatenation difference as an
actual boundary.  No homology or subdivision invariance is assumed. -/
theorem pathTrans_difference_boundary_of_subdivision_formula
    {X : Type} [TopologicalSpace X] {x : X}
    (gamma delta : Path x x) (h : PathTransSubdivisionFormula gamma delta) :
    ∃ b : AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X 2,
      pathChain (gamma.trans delta) - pathChain gamma - pathChain delta =
        b ≫ (SingularChains (TopCat.of X)).d 2 1 := by
  obtain ⟨b, hb⟩ := basedLoop_subdivision_difference_boundary
    (gamma.trans delta)
  refine ⟨-b, ?_⟩
  rw [Preadditive.neg_comp, ← hb]
  dsimp [PathTransSubdivisionFormula] at h
  rw [h]
  abel

/-- Conditional homology additivity in Mathlib's actual path-composition
order: `gamma.trans delta` traverses `gamma` first and `delta` second. -/
theorem basedLoopH1Class_trans_of_subdivision_formula
    {X : Type} [TopologicalSpace X] {x : X}
    (gamma delta : Path x x) (h : PathTransSubdivisionFormula gamma delta) :
    basedLoopH1Class (gamma.trans delta) =
      basedLoopH1Class gamma + basedLoopH1Class delta := by
  let K := SingularChains (TopCat.of X)
  let c := pathChain (gamma.trans delta) - pathChain gamma - pathChain delta
  have hc : c ≫ K.d 1 0 = 0 := by
    dsimp [c, K]
    rw [Preadditive.sub_comp, Preadditive.sub_comp, pathChain_cycle,
      pathChain_cycle, pathChain_cycle]
    simp
  obtain ⟨b, hb⟩ :=
    pathTrans_difference_boundary_of_subdivision_formula gamma delta h
  have hzero : K.liftCycles c 0 (by simp) hc ≫ K.homologyπ 1 = 0 :=
    K.liftCycles_homologyπ_eq_zero_of_boundary c 0 (by simp) b hb
  have hlift : K.liftCycles c 0 (by simp) hc =
      basedLoopCycle (gamma.trans delta) - basedLoopCycle gamma -
        basedLoopCycle delta := by
    apply (cancel_mono (K.iCycles 1)).1
    rw [K.liftCycles_i, Preadditive.sub_comp, Preadditive.sub_comp,
      basedLoopCycle_i, basedLoopCycle_i, basedLoopCycle_i]
  have hclasses : basedLoopH1Class (gamma.trans delta) -
      basedLoopH1Class gamma - basedLoopH1Class delta = 0 := by
    rw [basedLoopH1Class, basedLoopH1Class, basedLoopH1Class]
    rw [← Preadditive.sub_comp, ← Preadditive.sub_comp, ← hlift]
    exact hzero
  apply sub_eq_zero.mp
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hclasses

/-! ## Direct concatenation-triangle coordinates -/

/-- The affine parameter with ordered vertex values `0`, `1/2`, and `1`. -/
def intervalConcatenationTriangle : C(stdSimplex ℝ (Fin 3), unitInterval) :=
  ⟨fun z ↦ ⟨z.1 1 / 2 + z.1 2, by
      constructor
      · exact add_nonneg (div_nonneg (z.2.1 1) (by norm_num)) (z.2.1 2)
      · have hs := z.2.2
        rw [Fin.sum_univ_three] at hs
        nlinarith [z.2.1 0, z.2.1 1, z.2.1 2]⟩,
    Continuous.subtype_mk
      (((continuous_apply 1).comp continuous_subtype_val).div_const 2 |>.add
        ((continuous_apply 2).comp continuous_subtype_val)) (fun z ↦ by
          constructor
          · exact add_nonneg (div_nonneg (z.2.1 1) (by norm_num)) (z.2.1 2)
          · change z.1 1 / 2 + z.1 2 ≤ 1
            have hs := z.2.2
            rw [Fin.sum_univ_three] at hs
            nlinarith [z.2.1 0, z.2.1 1, z.2.1 2])⟩

private theorem faceAffine_one_zero_coord_one
    (u : stdSimplex ℝ (Fin 2)) : (faceAffine 1 0 u).1 1 = u.1 0 := by
  change ∑ j : Fin 2, u.1 j *
      (Pi.single ((0 : Fin 3).succAbove j) 1 : Fin 3 → ℝ) 1 = u.1 0
  rw [Fin.sum_univ_two]
  simp

private theorem faceAffine_one_zero_coord_two
    (u : stdSimplex ℝ (Fin 2)) : (faceAffine 1 0 u).1 2 = u.1 1 := by
  change ∑ j : Fin 2, u.1 j *
      (Pi.single ((0 : Fin 3).succAbove j) 1 : Fin 3 → ℝ) 2 = u.1 1
  rw [Fin.sum_univ_two]
  simp

private theorem faceAffine_one_one_coord_one
    (u : stdSimplex ℝ (Fin 2)) : (faceAffine 1 1 u).1 1 = 0 := by
  change ∑ j : Fin 2, u.1 j *
      (Pi.single ((1 : Fin 3).succAbove j) 1 : Fin 3 → ℝ) 1 = 0
  rw [Fin.sum_univ_two]
  simp [Fin.succAbove]

private theorem faceAffine_one_one_coord_two
    (u : stdSimplex ℝ (Fin 2)) : (faceAffine 1 1 u).1 2 = u.1 1 := by
  change ∑ j : Fin 2, u.1 j *
      (Pi.single ((1 : Fin 3).succAbove j) 1 : Fin 3 → ℝ) 2 = u.1 1
  rw [Fin.sum_univ_two]
  simp [Fin.succAbove]

private theorem faceAffine_one_two_coord_one
    (u : stdSimplex ℝ (Fin 2)) : (faceAffine 1 2 u).1 1 = u.1 1 := by
  change ∑ j : Fin 2, u.1 j *
      (Pi.single ((2 : Fin 3).succAbove j) 1 : Fin 3 → ℝ) 1 = u.1 1
  rw [Fin.sum_univ_two]
  simp [Fin.succAbove]

private theorem faceAffine_one_two_coord_two
    (u : stdSimplex ℝ (Fin 2)) : (faceAffine 1 2 u).1 2 = 0 := by
  change ∑ j : Fin 2, u.1 j *
      (Pi.single ((2 : Fin 3).succAbove j) 1 : Fin 3 → ℝ) 2 = 0
  rw [Fin.sum_univ_two]
  simp [Fin.succAbove]

/-- On face zero, the concatenation parameter runs from `1/2` to `1`. -/
theorem intervalConcatenationTriangle_face_zero_val
    (u : stdSimplex ℝ (Fin 2)) :
    ((intervalConcatenationTriangle.comp (faceAffine 1 0)) u : ℝ) =
      (1 + u.1 1) / 2 := by
  change (faceAffine 1 0 u).1 1 / 2 + (faceAffine 1 0 u).1 2 = _
  rw [faceAffine_one_zero_coord_one, faceAffine_one_zero_coord_two]
  have hu := u.2.2
  rw [Fin.sum_univ_two] at hu
  linarith

/-- On face one, the concatenation parameter is the full interval parameter. -/
theorem intervalConcatenationTriangle_face_one_val
    (u : stdSimplex ℝ (Fin 2)) :
    ((intervalConcatenationTriangle.comp (faceAffine 1 1)) u : ℝ) = u.1 1 := by
  change (faceAffine 1 1 u).1 1 / 2 + (faceAffine 1 1 u).1 2 = _
  rw [faceAffine_one_one_coord_one, faceAffine_one_one_coord_two]
  ring

/-- On face two, the concatenation parameter runs from `0` to `1/2`. -/
theorem intervalConcatenationTriangle_face_two_val
    (u : stdSimplex ℝ (Fin 2)) :
    ((intervalConcatenationTriangle.comp (faceAffine 1 2)) u : ℝ) = u.1 1 / 2 := by
  change (faceAffine 1 2 u).1 1 / 2 + (faceAffine 1 2 u).1 2 = _
  rw [faceAffine_one_two_coord_one, faceAffine_one_two_coord_two]
  ring

/-! ## The direct concatenation boundary -/

/-- The singular triangle obtained by evaluating the concatenated path at the
affine parameter with vertex values `0`, `1/2`, and `1`. -/
def pathTransTriangle {X : Type} [TopologicalSpace X] {x y z : X}
    (gamma : Path x y) (delta : Path y z) :
    C(stdSimplex ℝ (Fin 3), X) :=
  (gamma.trans delta).toContinuousMap.comp intervalConcatenationTriangle

theorem pathTransTriangle_face_zero {X : Type} [TopologicalSpace X]
    {x y z : X} (gamma : Path x y) (delta : Path y z) :
    (TopCat.toSSet.obj (TopCat.of X)).δ (0 : Fin 3)
        (singularSimplexOfContinuousMap _ 2 (pathTransTriangle gamma delta)) =
      singularSimplexOfContinuousMap _ 1 (pathSimplex delta) := by
  rw [singularSimplexOfContinuousMap_face]
  congr 1
  ext u
  change (gamma.trans delta)
      (intervalConcatenationTriangle (faceAffine 1 0 u)) =
    delta (stdSimplexHomeomorphUnitInterval u)
  rw [Path.trans_apply]
  split_ifs with h
  · have hu := u.2.2
    rw [Fin.sum_univ_two] at hu
    have hval := intervalConcatenationTriangle_face_zero_val u
    have hu1 : u.1 1 = 0 := by
      change ((intervalConcatenationTriangle.comp (faceAffine 1 0)) u : ℝ) ≤ 1 / 2 at h
      rw [hval] at h
      nlinarith [u.2.1 0, u.2.1 1]
    have hp : (intervalConcatenationTriangle
        (faceAffine 1 0 u) : ℝ) = 1 / 2 := by
      change ((intervalConcatenationTriangle.comp
        (faceAffine 1 0)) u : ℝ) = 1 / 2
      rw [hval, hu1]
      norm_num
    have huparam : (stdSimplexHomeomorphUnitInterval u : ℝ) = 0 := by
      simp [stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc, hu1]
    calc
      gamma ⟨2 * (intervalConcatenationTriangle
          (faceAffine 1 0 u) : ℝ), _⟩ = gamma 1 := by
        apply congrArg gamma
        apply Subtype.ext
        change 2 * (intervalConcatenationTriangle
          (faceAffine 1 0 u) : ℝ) = 1
        linarith
      _ = y := gamma.target
      _ = delta 0 := delta.source.symm
      _ = delta (stdSimplexHomeomorphUnitInterval u) := by
        apply congrArg delta
        apply Subtype.ext
        exact huparam.symm
  · apply congrArg delta
    apply Subtype.ext
    have hval := intervalConcatenationTriangle_face_zero_val u
    change 2 * ((intervalConcatenationTriangle.comp
      (faceAffine 1 0)) u : ℝ) - 1 = _
    rw [hval]
    simp [stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc]
    ring

theorem pathTransTriangle_face_one {X : Type} [TopologicalSpace X]
    {x y z : X} (gamma : Path x y) (delta : Path y z) :
    (TopCat.toSSet.obj (TopCat.of X)).δ (1 : Fin 3)
        (singularSimplexOfContinuousMap _ 2 (pathTransTriangle gamma delta)) =
      singularSimplexOfContinuousMap _ 1
        (pathSimplex (gamma.trans delta)) := by
  rw [singularSimplexOfContinuousMap_face]
  congr 1
  ext u
  apply congrArg (gamma.trans delta)
  apply Subtype.ext
  exact intervalConcatenationTriangle_face_one_val u

theorem pathTransTriangle_face_two {X : Type} [TopologicalSpace X]
    {x y z : X} (gamma : Path x y) (delta : Path y z) :
    (TopCat.toSSet.obj (TopCat.of X)).δ (2 : Fin 3)
        (singularSimplexOfContinuousMap _ 2 (pathTransTriangle gamma delta)) =
      singularSimplexOfContinuousMap _ 1 (pathSimplex gamma) := by
  rw [singularSimplexOfContinuousMap_face]
  congr 1
  ext u
  change (gamma.trans delta)
      (intervalConcatenationTriangle (faceAffine 1 2 u)) =
    gamma (stdSimplexHomeomorphUnitInterval u)
  rw [Path.trans_apply]
  split_ifs with h
  · apply congrArg gamma
    apply Subtype.ext
    have hval := intervalConcatenationTriangle_face_two_val u
    change 2 * ((intervalConcatenationTriangle.comp
      (faceAffine 1 2)) u : ℝ) = _
    rw [hval]
    simp [stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc]
    ring
  · have hval := intervalConcatenationTriangle_face_two_val u
    exfalso
    apply h
    change ((intervalConcatenationTriangle.comp (faceAffine 1 2)) u : ℝ) ≤ 1 / 2
    rw [hval]
    have hu := u.2.2
    rw [Fin.sum_univ_two] at hu
    nlinarith [u.2.1 0, u.2.1 1]

/-- The production differential of the direct concatenation triangle has the
standard oriented boundary `delta - (gamma.trans delta) + gamma`. -/
theorem pathTransTriangle_boundary {X : Type} [TopologicalSpace X]
    {x y z : X} (gamma : Path x y) (delta : Path y z) :
    singularGenerator (TopCat.of X) 2
        (singularSimplexOfContinuousMap _ 2
          (pathTransTriangle gamma delta)) ≫
        (SingularChains (TopCat.of X)).d 2 1 =
      pathChain delta - pathChain (gamma.trans delta) + pathChain gamma := by
  rw [singularGenerator_boundary, Fin.sum_univ_three,
    pathTransTriangle_face_zero, pathTransTriangle_face_one,
    pathTransTriangle_face_two]
  simp [pathChain, sub_eq_add_neg]

theorem pathTrans_difference_boundary {X : Type} [TopologicalSpace X]
    {x : X} (gamma delta : Path x x) :
    ∃ b : AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X 2,
      pathChain (gamma.trans delta) - pathChain gamma - pathChain delta =
        b ≫ (SingularChains (TopCat.of X)).d 2 1 := by
  refine ⟨-singularGenerator (TopCat.of X) 2
    (singularSimplexOfContinuousMap _ 2 (pathTransTriangle gamma delta)), ?_⟩
  rw [Preadditive.neg_comp, pathTransTriangle_boundary]
  abel

theorem basedLoopH1Class_trans {X : Type} [TopologicalSpace X] {x : X}
    (gamma delta : Path x x) :
    basedLoopH1Class (gamma.trans delta) =
      basedLoopH1Class gamma + basedLoopH1Class delta := by
  let K := SingularChains (TopCat.of X)
  let c := pathChain (gamma.trans delta) - pathChain gamma - pathChain delta
  have hc : c ≫ K.d 1 0 = 0 := by
    dsimp [c, K]
    rw [Preadditive.sub_comp, Preadditive.sub_comp, pathChain_cycle,
      pathChain_cycle, pathChain_cycle]
    simp
  obtain ⟨b, hb⟩ := pathTrans_difference_boundary gamma delta
  have hzero : K.liftCycles c 0 (by simp) hc ≫ K.homologyπ 1 = 0 :=
    K.liftCycles_homologyπ_eq_zero_of_boundary c 0 (by simp) b hb
  have hlift : K.liftCycles c 0 (by simp) hc =
      basedLoopCycle (gamma.trans delta) - basedLoopCycle gamma -
        basedLoopCycle delta := by
    apply (cancel_mono (K.iCycles 1)).1
    rw [K.liftCycles_i, Preadditive.sub_comp, Preadditive.sub_comp,
      basedLoopCycle_i, basedLoopCycle_i, basedLoopCycle_i]
  have hclasses : basedLoopH1Class (gamma.trans delta) -
      basedLoopH1Class gamma - basedLoopH1Class delta = 0 := by
    rw [basedLoopH1Class, basedLoopH1Class, basedLoopH1Class]
    rw [← Preadditive.sub_comp, ← Preadditive.sub_comp, ← hlift]
    exact hzero
  apply sub_eq_zero.mp
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hclasses

#print axioms pathChain_boundary
#print axioms pathChain_cycle
#print axioms pathChain_postcomp
#print axioms pathHomotopyPrismChain_boundary_raw
#print axioms pathHomotopyBoundaryChain_boundary
#print axioms basedLoopH1Class_eq_of_homotopy
#print axioms basedLoop_subdivision_difference_boundary
#print axioms pathTrans_difference_boundary_of_subdivision_formula
#print axioms basedLoopH1Class_trans_of_subdivision_formula
#print axioms intervalConcatenationTriangle_face_zero_val
#print axioms intervalConcatenationTriangle_face_one_val
#print axioms intervalConcatenationTriangle_face_two_val
#print axioms pathTransTriangle_boundary
#print axioms pathTrans_difference_boundary
#print axioms basedLoopH1Class_trans

end ConstructionTargets.SingularPathChain
