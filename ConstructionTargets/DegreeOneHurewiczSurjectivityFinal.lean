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

/-! ## Endpoint coherence -/

/-- The point represented by a production zero-simplex.  The source standard
zero-simplex is a singleton, so the choice of its displayed point is
irrelevant. -/
def zeroSimplexPoint {X : Type} [TopologicalSpace X]
    (v : ZeroSimplex X) : X :=
  continuousMapOfSingularSimplex 0 v (standardSimplexVertices 0 0)

theorem zeroSimplexPoint_eq_apply {X : Type} [TopologicalSpace X]
    (v : ZeroSimplex X) (u : stdSimplex ℝ (Fin 1)) :
    zeroSimplexPoint v = continuousMapOfSingularSimplex 0 v u := by
  apply congrArg (continuousMapOfSingularSimplex 0 v)
  ext i
  fin_cases i
  simpa [standardSimplexVertices] using
    (stdSimplex.eq_one_of_unique u (0 : Fin 1)).symm

theorem zeroSimplexPoint_initialZeroSimplex
    {X : Type} [TopologicalSpace X] (σ : OneSimplex X) :
    zeroSimplexPoint (initialZeroSimplex σ) = edgeInitialPoint σ := by
  let f := continuousMapOfSingularSimplex 1 σ
  have hσ : singularSimplexOfContinuousMap (TopCat.of X) 1 f = σ := by
    change (TopCat.toSSetObjEquiv (TopCat.of X) _).symm f = σ
    dsimp [f, continuousMapOfSingularSimplex]
    exact Equiv.symm_apply_apply _ σ
  rw [← hσ, initialZeroSimplex_ofContinuousMap]
  change (f.comp (faceAffine 0 1)) (standardSimplexVertices 0 0) =
    f (stdSimplexHomeomorphUnitInterval.symm 0)
  apply congrArg f
  have hface : faceAffine 0 1 (standardSimplexVertices 0 0) =
      standardSimplexVertices 1 0 := by
    simpa [Function.comp_apply] using
      congrFun (faceAffine_standardSimplexVertices 0 (1 : Fin 2)) 0
  rw [hface]
  apply stdSimplexHomeomorphUnitInterval.injective
  simp [standardSimplexVertices]

theorem zeroSimplexPoint_terminalZeroSimplex
    {X : Type} [TopologicalSpace X] (σ : OneSimplex X) :
    zeroSimplexPoint (terminalZeroSimplex σ) = edgeTerminalPoint σ := by
  let f := continuousMapOfSingularSimplex 1 σ
  have hσ : singularSimplexOfContinuousMap (TopCat.of X) 1 f = σ := by
    change (TopCat.toSSetObjEquiv (TopCat.of X) _).symm f = σ
    dsimp [f, continuousMapOfSingularSimplex]
    exact Equiv.symm_apply_apply _ σ
  rw [← hσ, terminalZeroSimplex_ofContinuousMap]
  change (f.comp (faceAffine 0 0)) (standardSimplexVertices 0 0) =
    f (stdSimplexHomeomorphUnitInterval.symm 1)
  apply congrArg f
  have hface : faceAffine 0 0 (standardSimplexVertices 0 0) =
      standardSimplexVertices 1 1 := by
    simpa [Function.comp_apply] using
      congrFun (faceAffine_standardSimplexVertices 0 (0 : Fin 2)) 0
  rw [hface]
  apply stdSimplexHomeomorphUnitInterval.injective
  simp [standardSimplexVertices]

def endpointConnectorChain {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] (x0 : X) (p : ZeroSimplex X) :
    AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X 1 :=
  pathChain (connector x0 (zeroSimplexPoint p))

theorem initialConnectorChain_eq_endpointConnectorChain
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (σ : OneSimplex X) :
    pathChain (connector x0 (edgeInitialPoint σ)) =
      endpointConnectorChain x0 (initialZeroSimplex σ) := by
  rw [endpointConnectorChain, zeroSimplexPoint_initialZeroSimplex]

theorem terminalConnectorChain_eq_endpointConnectorChain
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (σ : OneSimplex X) :
    pathChain (connector x0 (edgeTerminalPoint σ)) =
      endpointConnectorChain x0 (terminalZeroSimplex σ) := by
  rw [endpointConnectorChain, zeroSimplexPoint_terminalZeroSimplex]

noncomputable def endpointSupport {X : Type} [TopologicalSpace X]
    (z : (SingularChains (TopCat.of X)).X 1) : Finset (ZeroSimplex X) := by
  classical
  exact (oneChainSupport z).image initialZeroSimplex ∪
    (oneChainSupport z).image terminalZeroSimplex

theorem initialZeroSimplex_mem_endpointSupport
    {X : Type} [TopologicalSpace X]
    (z : (SingularChains (TopCat.of X)).X 1) (σ : OneSimplex X)
    (hσ : σ ∈ oneChainSupport z) :
    initialZeroSimplex σ ∈ endpointSupport z := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨σ, hσ, rfl⟩)

theorem terminalZeroSimplex_mem_endpointSupport
    {X : Type} [TopologicalSpace X]
    (z : (SingularChains (TopCat.of X)).X 1) (σ : OneSimplex X)
    (hσ : σ ∈ oneChainSupport z) :
    terminalZeroSimplex σ ∈ endpointSupport z := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨σ, hσ, rfl⟩)

theorem weighted_initial_connectors_regroup
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (z : (SingularChains (TopCat.of X)).X 1) :
    ∑ σ ∈ oneChainSupport z, (oneChainCoefficients z σ) •
        pathChain (connector x0 (edgeInitialPoint σ)) =
      ∑ p ∈ endpointSupport z,
        (∑ σ ∈ outgoingSupport z p, oneChainCoefficients z σ) •
          endpointConnectorChain x0 p := by
  classical
  simp_rw [initialConnectorChain_eq_endpointConnectorChain]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun σ hσ ↦ initialZeroSimplex_mem_endpointSupport z σ hσ)
    (fun σ ↦ (oneChainCoefficients z σ) •
      endpointConnectorChain x0 (initialZeroSimplex σ))]
  apply Finset.sum_congr rfl
  intro p hp
  change ∑ σ ∈ (oneChainSupport z).filter (initialZeroSimplex · = p),
      (oneChainCoefficients z σ) •
        endpointConnectorChain x0 (initialZeroSimplex σ) = _
  calc
    _ = ∑ σ ∈ outgoingSupport z p,
        (oneChainCoefficients z σ) • endpointConnectorChain x0 p := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [(Finset.mem_filter.mp hσ).2]
    _ = _ := by rw [← Finset.sum_smul]

theorem weighted_terminal_connectors_regroup
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (z : (SingularChains (TopCat.of X)).X 1) :
    ∑ σ ∈ oneChainSupport z, (oneChainCoefficients z σ) •
        pathChain (connector x0 (edgeTerminalPoint σ)) =
      ∑ p ∈ endpointSupport z,
        (∑ σ ∈ incomingSupport z p, oneChainCoefficients z σ) •
          endpointConnectorChain x0 p := by
  classical
  simp_rw [terminalConnectorChain_eq_endpointConnectorChain]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun σ hσ ↦ terminalZeroSimplex_mem_endpointSupport z σ hσ)
    (fun σ ↦ (oneChainCoefficients z σ) •
      endpointConnectorChain x0 (terminalZeroSimplex σ))]
  apply Finset.sum_congr rfl
  intro p hp
  change ∑ σ ∈ (oneChainSupport z).filter (terminalZeroSimplex · = p),
      (oneChainCoefficients z σ) •
        endpointConnectorChain x0 (terminalZeroSimplex σ) = _
  calc
    _ = ∑ σ ∈ incomingSupport z p,
        (oneChainCoefficients z σ) • endpointConnectorChain x0 p := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [(Finset.mem_filter.mp hσ).2]
    _ = _ := by rw [← Finset.sum_smul]

theorem weighted_connector_cancellation
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (z : (SingularChains (TopCat.of X)).X 1)
    (hz : (SingularChains (TopCat.of X)).d 1 0 z = 0) :
    ∑ σ ∈ oneChainSupport z, (oneChainCoefficients z σ) •
        pathChain (connector x0 (edgeInitialPoint σ)) =
      ∑ σ ∈ oneChainSupport z, (oneChainCoefficients z σ) •
        pathChain (connector x0 (edgeTerminalPoint σ)) := by
  rw [weighted_initial_connectors_regroup,
    weighted_terminal_connectors_regroup]
  apply Finset.sum_congr rfl
  intro p hp
  rw [cycle_vertex_balance z hz p]

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

/-! ## Finite closed-loop assembly -/

theorem addCommGrp_hom_sum_apply {A B : AddCommGrpCat}
    {ι : Type} (s : Finset ι) (f : ι → (A ⟶ B)) (x : A) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih]

theorem addMonoidHom_sum_apply {A B : Type} [AddCommMonoid A]
    [AddCommMonoid B] {ι : Type} (s : Finset ι)
    (f : ι → (A →+ B)) (x : A) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

/-- The homomorphism from `ℤ` selecting a chain element. -/
def chainElementHom {X : Type} [TopologicalSpace X] {n : ℕ}
    (z : (SingularChains (TopCat.of X)).X n) :
    AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X n :=
  AddCommGrpCat.ofHom (zmultiplesHom _ z)

@[simp] theorem chainElementHom_apply_one
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (z : (SingularChains (TopCat.of X)).X n) :
    chainElementHom z (1 : ℤ) = z := by
  change (1 : ℤ) • z = z
  exact one_zsmul z

/-- The finite coefficient reconstruction, now expressed as an equality of
homomorphisms out of `ℤ`. -/
theorem chainElementHom_eq_sum_generators
    {X : Type} [TopologicalSpace X]
    (z : (SingularChains (TopCat.of X)).X 1) :
    chainElementHom z =
      ∑ σ ∈ oneChainSupport z, (oneChainCoefficients z σ) •
        singularGenerator (TopCat.of X) 1 σ := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext_int
  rw [chainElementHom_apply_one]
  change z = _
  calc
    z = oneChainOfCoefficients (oneChainCoefficients z) :=
      (oneChainOfCoefficients_coefficients z).symm
    _ = oneChainOfCoefficients
        (∑ σ ∈ oneChainSupport z,
          oneCoefficientGenerator σ (oneChainCoefficients z σ)) := by
      exact congrArg oneChainOfCoefficients
        (oneChainCoefficients_eq_sum_support z)
    _ = _ := by
      change (oneChainCoefficientsIso X).inv
          (∑ σ ∈ oneChainSupport z,
            oneCoefficientGenerator σ (oneChainCoefficients z σ)) =
        (∑ σ ∈ oneChainSupport z,
          ((oneChainCoefficients z σ) •
            singularGenerator (TopCat.of X) 1 σ)) 1
      rw [map_sum]
      change _ = (AddCommGrpCat.homAddEquiv
        (∑ σ ∈ oneChainSupport z,
          ((oneChainCoefficients z σ) •
            singularGenerator (TopCat.of X) 1 σ))) 1
      rw [map_sum, addMonoidHom_sum_apply]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [← CategoryTheory.comp_apply,
        oneCoefficientGenerator_iso_inv]
      change singularGenerator (TopCat.of X) 1 σ
          (oneChainCoefficients z σ) =
        (oneChainCoefficients z σ) •
          singularGenerator (TopCat.of X) 1 σ (1 : ℤ)
      simpa using map_zsmul (singularGenerator (TopCat.of X) 1 σ).hom
        (oneChainCoefficients z σ) (1 : ℤ)

theorem chainElementHom_boundary_eq_zero
    {X : Type} [TopologicalSpace X]
    (z : (SingularChains (TopCat.of X)).X 1)
    (hz : (SingularChains (TopCat.of X)).d 1 0 z = 0) :
    chainElementHom z ≫ (SingularChains (TopCat.of X)).d 1 0 = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext_int
  change (SingularChains (TopCat.of X)).d 1 0 (chainElementHom z 1) = 0
  rw [chainElementHom_apply_one]
  exact hz

def weightedClosedLoopChain
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (z : (SingularChains (TopCat.of X)).X 1) :
    AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X 1 :=
  ∑ σ ∈ oneChainSupport z, (oneChainCoefficients z σ) •
    pathChain (closedEdgeLoop x0 σ)

def weightedClosedEdgeBoundaryWitness
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (z : (SingularChains (TopCat.of X)).X 1) :
    AddCommGrpCat.of ℤ ⟶ (SingularChains (TopCat.of X)).X 2 :=
  ∑ σ ∈ oneChainSupport z,
    (oneChainCoefficients z σ) • closedEdgeBoundaryWitness x0 σ

/-- For a cycle, the finite sum of its directly closed edge loops differs
from the original chain by the assembled production boundary. -/
theorem weightedClosedLoopChain_sub_chainElementHom_eq_boundary
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (z : (SingularChains (TopCat.of X)).X 1)
    (hz : (SingularChains (TopCat.of X)).d 1 0 z = 0) :
    weightedClosedLoopChain x0 z - chainElementHom z =
      weightedClosedEdgeBoundaryWitness x0 z ≫
        (SingularChains (TopCat.of X)).d 2 1 := by
  rw [weightedClosedEdgeBoundaryWitness,
    ← weighted_closedEdge_defects_boundary]
  rw [chainElementHom_eq_sum_generators]
  have hc := weighted_connector_cancellation x0 z hz
  simp_rw [pathChain_singularEdgePath]
  dsimp [weightedClosedLoopChain]
  have hdist :
      (∑ σ ∈ oneChainSupport z, (oneChainCoefficients z σ) •
        (pathChain (closedEdgeLoop x0 σ) -
          singularGenerator (TopCat.of X) 1 σ -
          pathChain (connector x0 (edgeInitialPoint σ)) +
          pathChain (connector x0 (edgeTerminalPoint σ)))) =
        (∑ σ ∈ oneChainSupport z,
          (oneChainCoefficients z σ) • pathChain (closedEdgeLoop x0 σ)) -
        (∑ σ ∈ oneChainSupport z,
          (oneChainCoefficients z σ) • singularGenerator (TopCat.of X) 1 σ) -
        (∑ σ ∈ oneChainSupport z,
          (oneChainCoefficients z σ) •
            pathChain (connector x0 (edgeInitialPoint σ))) +
        (∑ σ ∈ oneChainSupport z,
          (oneChainCoefficients z σ) •
            pathChain (connector x0 (edgeTerminalPoint σ))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ hσ
    simp only [sub_eq_add_neg, zsmul_add, zsmul_neg]
  rw [hdist]
  calc
    _ = (∑ σ ∈ oneChainSupport z,
          (oneChainCoefficients z σ) • pathChain (closedEdgeLoop x0 σ)) -
        (∑ σ ∈ oneChainSupport z,
          (oneChainCoefficients z σ) • singularGenerator (TopCat.of X) 1 σ) -
        (∑ σ ∈ oneChainSupport z,
          (oneChainCoefficients z σ) •
            pathChain (connector x0 (edgeInitialPoint σ))) +
        (∑ σ ∈ oneChainSupport z,
          (oneChainCoefficients z σ) •
            pathChain (connector x0 (edgeTerminalPoint σ))) := by
          rw [hc]
          abel
    _ = _ := rfl

theorem weightedClosedLoopChain_boundary_eq_zero
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (z : (SingularChains (TopCat.of X)).X 1) :
    weightedClosedLoopChain x0 z ≫
        (SingularChains (TopCat.of X)).d 1 0 = 0 := by
  rw [weightedClosedLoopChain, Preadditive.sum_comp]
  apply Finset.sum_eq_zero
  intro σ hσ
  rw [Preadditive.zsmul_comp, pathChain_cycle, smul_zero]

/-- The homology class of the weighted closed-loop chain is literally the
finite coefficient-weighted sum of the individual based-loop classes. -/
theorem weightedClosedLoop_homology_eq_sum_classes
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (z : (SingularChains (TopCat.of X)).X 1) :
    let K := SingularChains (TopCat.of X)
    K.liftCycles (weightedClosedLoopChain x0 z) 0 (by simp)
          (weightedClosedLoopChain_boundary_eq_zero x0 z) ≫ K.homologyπ 1 =
      ∑ σ ∈ oneChainSupport z, (oneChainCoefficients z σ) •
        basedLoopH1Class (closedEdgeLoop x0 σ) := by
  dsimp only
  let K := SingularChains (TopCat.of X)
  have hlift :
      K.liftCycles (weightedClosedLoopChain x0 z) 0 (by simp)
          (weightedClosedLoopChain_boundary_eq_zero x0 z) =
        ∑ σ ∈ oneChainSupport z, (oneChainCoefficients z σ) •
          basedLoopCycle (closedEdgeLoop x0 σ) := by
    apply (cancel_mono (K.iCycles 1)).1
    rw [K.liftCycles_i, Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [Preadditive.zsmul_comp, basedLoopCycle_i]
  rw [hlift, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Preadditive.zsmul_comp]
  rfl

/-- The original cycle and the finite coefficient-weighted sum of its closed
edge loops determine the same production H1 class. -/
theorem cycle_homology_eq_weightedClosedLoop
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (z : (SingularChains (TopCat.of X)).X 1)
    (hz : (SingularChains (TopCat.of X)).d 1 0 z = 0) :
    let K := SingularChains (TopCat.of X)
    K.liftCycles (chainElementHom z) 0 (by simp)
          (chainElementHom_boundary_eq_zero z hz) ≫ K.homologyπ 1 =
      K.liftCycles (weightedClosedLoopChain x0 z) 0 (by simp)
          (weightedClosedLoopChain_boundary_eq_zero x0 z) ≫ K.homologyπ 1 := by
  dsimp only
  let K := SingularChains (TopCat.of X)
  let c := weightedClosedLoopChain x0 z - chainElementHom z
  have hc : c ≫ K.d 1 0 = 0 := by
    dsimp [c, K]
    rw [Preadditive.sub_comp, weightedClosedLoopChain_boundary_eq_zero,
      chainElementHom_boundary_eq_zero z hz, sub_zero]
  have hb : c = weightedClosedEdgeBoundaryWitness x0 z ≫ K.d 2 1 := by
    exact weightedClosedLoopChain_sub_chainElementHom_eq_boundary x0 z hz
  have hzero : K.liftCycles c 0 (by simp) hc ≫ K.homologyπ 1 = 0 :=
    K.liftCycles_homologyπ_eq_zero_of_boundary c 0 (by simp)
      (weightedClosedEdgeBoundaryWitness x0 z) hb
  have hlift : K.liftCycles c 0 (by simp) hc =
      K.liftCycles (weightedClosedLoopChain x0 z) 0 (by simp)
          (weightedClosedLoopChain_boundary_eq_zero x0 z) -
        K.liftCycles (chainElementHom z) 0 (by simp)
          (chainElementHom_boundary_eq_zero z hz) := by
    apply (cancel_mono (K.iCycles 1)).1
    rw [K.liftCycles_i, Preadditive.sub_comp, K.liftCycles_i,
      K.liftCycles_i]
  have hclasses :
      (K.liftCycles (weightedClosedLoopChain x0 z) 0 (by simp)
          (weightedClosedLoopChain_boundary_eq_zero x0 z) ≫ K.homologyπ 1) -
        (K.liftCycles (chainElementHom z) 0 (by simp)
          (chainElementHom_boundary_eq_zero z hz) ≫ K.homologyπ 1) = 0 := by
    rw [← Preadditive.sub_comp, ← hlift]
    exact hzero
  exact (sub_eq_zero.mp hclasses).symm

/-- Explicit finite-sum form of the closing-path calculation: every
production one-cycle has the same H1 class as the coefficient-weighted sum of
the based loops obtained by closing each supported singular edge. -/
theorem cycle_homology_eq_sum_closedEdge_classes
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (x0 : X) (z : (SingularChains (TopCat.of X)).X 1)
    (hz : (SingularChains (TopCat.of X)).d 1 0 z = 0) :
    let K := SingularChains (TopCat.of X)
    K.liftCycles (chainElementHom z) 0 (by simp)
          (chainElementHom_boundary_eq_zero z hz) ≫ K.homologyπ 1 =
      ∑ σ ∈ oneChainSupport z, (oneChainCoefficients z σ) •
        basedLoopH1Class (closedEdgeLoop x0 σ) := by
  exact (cycle_homology_eq_weightedClosedLoop x0 z hz).trans
    (weightedClosedLoop_homology_eq_sum_classes x0 z)

#print axioms closedEdgeLoop_chain_formula
#print axioms weighted_closedEdge_defects_boundary
#print axioms zeroSimplexPoint_initialZeroSimplex
#print axioms zeroSimplexPoint_terminalZeroSimplex
#print axioms weighted_connector_cancellation
#print axioms chainElementHom_eq_sum_generators
#print axioms weightedClosedLoopChain_sub_chainElementHom_eq_boundary
#print axioms cycle_homology_eq_weightedClosedLoop
#print axioms cycle_homology_eq_sum_closedEdge_classes

end ConstructionTargets.DegreeOneHurewiczSurjectivityFinal
