import ConstructionTargets.T02A06SphereShift

/-!
# Path-connected zeroth homology for the sphere endpoint

This file supplies the chain-level path relation needed to compute the
degree-zero kernel at the end of the disk-pair long exact sequence.
-/

noncomputable section

namespace ConstructionTargets.T02A06SphereH0

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.SingularSubdivision
open T02A06

/-- The singular one-simplex represented by a path. -/
def singularEdgeOfPath {X : Type} [TopologicalSpace X] {x y : X}
    (γ : Path x y) : C(stdSimplex ℝ (Fin 2), X) :=
  γ.toContinuousMap.comp
    ⟨stdSimplexHomeomorphUnitInterval,
      stdSimplexHomeomorphUnitInterval.continuous⟩

/-- The zero-simplex at a point. -/
def singularVertexAt {X : Type} [TopologicalSpace X] (x : X) :
    C(stdSimplex ℝ (Fin 1), X) := ContinuousMap.const _ x

/-- A path gives a singular edge whose boundary is endpoint minus startpoint. -/
theorem singularEdgeOfPath_boundary
    {X : Type} [TopologicalSpace X] {x y : X} (γ : Path x y) :
    singularGenerator (TopCat.of X) 1
        (singularSimplexOfContinuousMap (TopCat.of X) 1
          (singularEdgeOfPath γ)) ≫
        (SingularChains (TopCat.of X)).d 1 0 =
      singularGenerator (TopCat.of X) 0
          (singularSimplexOfContinuousMap (TopCat.of X) 0
            (singularVertexAt y)) -
        singularGenerator (TopCat.of X) 0
          (singularSimplexOfContinuousMap (TopCat.of X) 0
            (singularVertexAt x)) := by
  have hface0 :
      (TopCat.toSSet.obj (TopCat.of X)).δ (0 : Fin 2)
          (singularSimplexOfContinuousMap (TopCat.of X) 1
            (singularEdgeOfPath γ)) =
        singularSimplexOfContinuousMap (TopCat.of X) 0
          (singularVertexAt y) := by
    rw [singularSimplexOfContinuousMap_face]
    congr 1
    ext z
    simp [singularEdgeOfPath, singularVertexAt, affineSimplex]
  have hface1 :
      (TopCat.toSSet.obj (TopCat.of X)).δ (1 : Fin 2)
          (singularSimplexOfContinuousMap (TopCat.of X) 1
            (singularEdgeOfPath γ)) =
        singularSimplexOfContinuousMap (TopCat.of X) 0
          (singularVertexAt x) := by
    rw [singularSimplexOfContinuousMap_face]
    congr 1
    ext z
    simp [singularEdgeOfPath, singularVertexAt, affineSimplex]
    change γ 0 = x
    exact γ.source
  rw [singularGenerator_boundary]
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ,
    Finset.sum_range_succ]
  simp [hface0, hface1, sub_eq_add_neg]

/-- The homology class of the singular zero-simplex at a point. -/
noncomputable def singularVertexH0Class
    {X : Type} [TopologicalSpace X] (x : X) :
    AddCommGrpCat.of ℤ ⟶
      ConstructionTargets.SingularHomologyConcrete.SingularHomology 0
        (TopCat.of X) :=
  (SingularChains (TopCat.of X)).liftCycles
      (singularGenerator (TopCat.of X) 0
        (singularSimplexOfContinuousMap (TopCat.of X) 0
          (singularVertexAt x))) 0 (by simp) (by simp) ≫
    (SingularChains (TopCat.of X)).homologyπ 0

/-- Path-connected points determine the same class in zeroth singular
homology. -/
theorem singularVertexH0Class_eq_of_path
    {X : Type} [TopologicalSpace X] {x y : X} (γ : Path x y) :
    singularVertexH0Class x = singularVertexH0Class y := by
  let K := SingularChains (TopCat.of X)
  let vx := singularGenerator (TopCat.of X) 0
    (singularSimplexOfContinuousMap (TopCat.of X) 0 (singularVertexAt x))
  let vy := singularGenerator (TopCat.of X) 0
    (singularSimplexOfContinuousMap (TopCat.of X) 0 (singularVertexAt y))
  let e := singularGenerator (TopCat.of X) 1
    (singularSimplexOfContinuousMap (TopCat.of X) 1 (singularEdgeOfPath γ))
  have hboundary : vy - vx = e ≫ K.d 1 0 := by
    rw [singularEdgeOfPath_boundary γ]
  have hz : (vy - vx) ≫ K.d 0 0 = 0 := by simp
  have hzero : K.liftCycles (vy - vx) 0 (by simp) hz ≫ K.homologyπ 0 = 0 :=
    K.liftCycles_homologyπ_eq_zero_of_boundary
      (vy - vx) 0 (by simp) e hboundary
  have hlift : K.liftCycles (vy - vx) 0 (by simp) hz =
      K.liftCycles vy 0 (by simp) (by simp) -
        K.liftCycles vx 0 (by simp) (by simp) := by
    apply (cancel_mono (K.iCycles 0)).1
    rw [K.liftCycles_i, Preadditive.sub_comp, K.liftCycles_i, K.liftCycles_i]
  have hclasses : singularVertexH0Class y - singularVertexH0Class x = 0 := by
    rw [singularVertexH0Class, singularVertexH0Class]
    rw [← Preadditive.sub_comp, ← hlift]
    exact hzero
  exact (sub_eq_zero.mp hclasses).symm

/-- In degree zero every chain is a cycle. -/
noncomputable def zeroChainsToCycles
    {X : Type} [TopologicalSpace X] :
    (SingularChains (TopCat.of X)).X 0 ⟶
      (SingularChains (TopCat.of X)).cycles 0 :=
  (SingularChains (TopCat.of X)).liftCycles (𝟙 _) 0 (by simp) (by simp)

@[reassoc (attr := simp)] theorem zeroChainsToCycles_i
    {X : Type} [TopologicalSpace X] :
    zeroChainsToCycles (X := X) ≫
      (SingularChains (TopCat.of X)).iCycles 0 = 𝟙 _ := by
  rw [zeroChainsToCycles, (SingularChains (TopCat.of X)).liftCycles_i]

theorem iCycles_zeroChainsToCycles
    {X : Type} [TopologicalSpace X] :
    (SingularChains (TopCat.of X)).iCycles 0 ≫
      zeroChainsToCycles (X := X) = 𝟙 _ := by
  apply (cancel_mono ((SingularChains (TopCat.of X)).iCycles 0)).1
  rw [Category.assoc, zeroChainsToCycles_i, Category.comp_id,
    Category.id_comp]

noncomputable instance zeroChainsToCycles_epi
    {X : Type} [TopologicalSpace X] :
    Epi (zeroChainsToCycles (X := X)) := by
  constructor
  intro Z g h w
  have hw := congrArg
    (fun k => (SingularChains (TopCat.of X)).iCycles 0 ≫ k) w
  simpa only [← Category.assoc, iCycles_zeroChainsToCycles,
    Category.id_comp] using hw

/-- The canonical projection from singular zero-chains to zeroth homology. -/
noncomputable def zeroChainH0Class
    {X : Type} [TopologicalSpace X] :
    (SingularChains (TopCat.of X)).X 0 ⟶
      ConstructionTargets.SingularHomologyConcrete.SingularHomology 0
        (TopCat.of X) :=
  zeroChainsToCycles ≫ (SingularChains (TopCat.of X)).homologyπ 0

set_option backward.isDefEq.respectTransparency false in
noncomputable instance zeroChainH0Class_epi
    {X : Type} [TopologicalSpace X] :
    Epi (zeroChainH0Class (X := X)) := by
  dsimp [zeroChainH0Class]
  infer_instance

/-- The unique point represented by a singular zero-simplex. -/
def singularZeroSimplexPoint
    {X : Type} [TopologicalSpace X]
    (s : SingularSimplex (TopCat.of X) 0) : X :=
  continuousMapOfSingularSimplex 0 s (standardSimplexVertices 0 0)

theorem singularZeroSimplex_eq_vertex
    {X : Type} [TopologicalSpace X]
    (s : SingularSimplex (TopCat.of X) 0) :
    s = singularSimplexOfContinuousMap (TopCat.of X) 0
      (singularVertexAt (singularZeroSimplexPoint s)) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X)
    (Opposite.op (SimplexCategory.mk 0))).injective
  simp only [singularSimplexOfContinuousMap, Equiv.apply_symm_apply]
  ext z
  let v : stdSimplex ℝ (Fin 1) := standardSimplexVertices 0 0
  letI : Subsingleton (Fin (0 + 1)) := ⟨fun i j => Fin.ext (by omega)⟩
  rw [Subsingleton.elim z v]
  rfl

theorem singularGenerator_zeroChainH0Class
    {X : Type} [TopologicalSpace X]
    (s : SingularSimplex (TopCat.of X) 0) :
    singularGenerator (TopCat.of X) 0 s ≫ zeroChainH0Class =
      singularVertexH0Class (singularZeroSimplexPoint s) := by
  let p := singularZeroSimplexPoint s
  have hs : s = singularSimplexOfContinuousMap (TopCat.of X) 0
      (singularVertexAt p) := singularZeroSimplex_eq_vertex s
  change singularGenerator (TopCat.of X) 0 s ≫ zeroChainH0Class =
    singularVertexH0Class p
  rw [hs]
  let g := singularGenerator (TopCat.of X) 0
    (singularSimplexOfContinuousMap (TopCat.of X) 0
      (singularVertexAt p))
  have hg : g ≫ zeroChainsToCycles =
      (SingularChains (TopCat.of X)).liftCycles g 0 (by simp) (by simp) := by
    apply (cancel_mono ((SingularChains (TopCat.of X)).iCycles 0)).1
    rw [Category.assoc, zeroChainsToCycles_i,
      (SingularChains (TopCat.of X)).liftCycles_i,
      Category.comp_id]
  change (g ≫ zeroChainsToCycles) ≫
      (SingularChains (TopCat.of X)).homologyπ 0 =
    (SingularChains (TopCat.of X)).liftCycles g 0 (by simp) (by simp) ≫
      (SingularChains (TopCat.of X)).homologyπ 0
  rw [hg]

/-- Sum all coefficients of a singular zero-chain. -/
noncomputable def zeroChainAugmentation
    {X : Type} [TopologicalSpace X] :
    (SingularChains (TopCat.of X)).X 0 ⟶ AddCommGrpCat.of ℤ := by
  change (∐ fun _ : SingularSimplex (TopCat.of X) 0 ↦
    AddCommGrpCat.of ℤ) ⟶ AddCommGrpCat.of ℤ
  exact Limits.Sigma.desc fun _ => 𝟙 _

/-- On a path-connected space, every zero-chain class is its coefficient sum
times the class of one chosen basepoint. -/
theorem zeroChainH0Class_eq_augmentation_comp_vertex
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (p : X) :
    zeroChainH0Class (X := X) =
      zeroChainAugmentation ≫ singularVertexH0Class p := by
  apply Limits.Sigma.hom_ext
  intro s
  change singularGenerator (TopCat.of X) 0 s ≫ zeroChainH0Class =
    (singularGenerator (TopCat.of X) 0 s ≫ zeroChainAugmentation) ≫
      singularVertexH0Class p
  rw [singularGenerator_zeroChainH0Class]
  change singularVertexH0Class (singularZeroSimplexPoint s) =
    (Limits.Sigma.ι (fun _ : SingularSimplex (TopCat.of X) 0 ↦
      AddCommGrpCat.of ℤ) s ≫ Limits.Sigma.desc (fun _ => 𝟙 _)) ≫
        singularVertexH0Class p
  rw [Limits.Sigma.ι_desc, Category.id_comp]
  exact (singularVertexH0Class_eq_of_path
    (PathConnectedSpace.joined p (singularZeroSimplexPoint s)).somePath).symm

/-- A basepoint class generates zeroth homology of a path-connected space. -/
theorem singularVertexH0Class_epi
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (p : X) :
    Epi (singularVertexH0Class p) := by
  have h := zeroChainH0Class_eq_augmentation_comp_vertex p
  haveI : Epi (zeroChainAugmentation ≫ singularVertexH0Class p) := by
    rw [← h]
    infer_instance
  exact epi_of_epi (zeroChainAugmentation (X := X))
    (singularVertexH0Class p)

/-- A surjective endomorphism of the additive group of integers is injective. -/
theorem intGroup_epi_endomorphism_mono
    (f : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) [Epi f] : Mono f := by
  rw [AddCommGrpCat.mono_iff_injective]
  have hsurj : Function.Surjective f :=
    (AddCommGrpCat.epi_iff_surjective f).1 inferInstance
  obtain ⟨n, hn⟩ := hsurj (1 : ℤ)
  intro a b hab
  have hform (z : ℤ) : f z = z * f 1 := by
    simpa [smul_eq_mul] using
      map_zsmul (ConcreteCategory.hom f) z (1 : ℤ)
  rw [hform n] at hn
  rw [hform a, hform b] at hab
  calc
    a = a * 1 := by ring
    _ = a * (n * f 1) := by rw [hn]
    _ = n * (a * f 1) := by ring
    _ = n * (b * f 1) := by rw [hab]
    _ = b * (n * f 1) := by ring
    _ = b * 1 := by rw [hn]
    _ = b := by ring

/-- On a path-connected space, a basepoint class is also monic. -/
theorem singularVertexH0Class_mono
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (p : X) :
    Mono (singularVertexH0Class p) := by
  let F := (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 0).obj
    (AddCommGrpCat.of ℤ)
  let collapse : TopCat.of X ⟶ TopCat.of Unit :=
    TopCat.ofHom (ContinuousMap.const X ())
  let incl : TopCat.of Unit ⟶ TopCat.of X :=
    ConstructionTargets.SingularHomologyConcrete.pointInclusion p
  have hsplit : F.map incl ≫ F.map collapse = 𝟙 _ := by
    rw [← F.map_comp]
    have hcomp : incl ≫ collapse = 𝟙 _ := by
      ext x
    rw [hcomp, F.map_id]
  haveI : Epi (F.map collapse) :=
    (SplitEpi.mk (F.map incl) hsplit).epi
  let f : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ :=
    singularVertexH0Class p ≫ F.map collapse ≫
      ConstructionTargets.SingularHomologyConcrete.pointH0IsoInt.hom
  haveI : Epi f := by
    change Epi ((singularVertexH0Class p ≫ F.map collapse) ≫
      ConstructionTargets.SingularHomologyConcrete.pointH0IsoInt.hom)
    exact epi_comp'
      (epi_comp' (singularVertexH0Class_epi p) inferInstance)
      inferInstance
  haveI : Mono f := intGroup_epi_endomorphism_mono f
  exact mono_of_mono_fac
    (f := F.map collapse ≫
      ConstructionTargets.SingularHomologyConcrete.pointH0IsoInt.hom)
    (h := f) rfl

/-- Vertex classes are natural under continuous maps. -/
theorem singularVertexH0Class_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    singularVertexH0Class x ≫
        HomologicalComplex.homologyMap (singularPostcomposition f) 0 =
      singularVertexH0Class (f x) := by
  let KX := SingularChains (TopCat.of X)
  let z := singularGenerator (TopCat.of X) 0
    (singularSimplexOfContinuousMap (TopCat.of X) 0 (singularVertexAt x))
  have hz : z ≫ KX.d 0 0 = 0 := by simp
  rw [singularVertexH0Class, singularVertexH0Class]
  have hnat := HomologicalComplex.homologyπ_naturality
    (singularPostcomposition f) 0
  slice_lhs 2 3 => exact hnat
  rw [← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
  have hgen : z ≫ (singularPostcomposition f).f 0 =
      singularGenerator (TopCat.of Y) 0
        (singularSimplexOfContinuousMap (TopCat.of Y) 0
          (singularVertexAt (f x))) := by
    rw [singularGenerator_singularPostcomposition]
    congr 2
  rw [hgen]
  rfl

/-- For a path-connected subspace of a path-connected space, inclusion is
injective on zeroth singular homology. -/
theorem pathConnectedSubspace_homologyMap_mono_zero
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (A : Set X) [Nonempty A] [PathConnectedSpace A] :
    Mono (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) 0) := by
  let p : A := Classical.choice (inferInstance : Nonempty A)
  let q := singularVertexH0Class p
  let hinc := HomologicalComplex.homologyMap
    (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A) 0
  let i : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  haveI : Epi q := singularVertexH0Class_epi p
  haveI : Mono q := singularVertexH0Class_mono p
  haveI : IsIso q := isIso_of_mono_of_epi q
  have hcomp : q ≫ hinc = singularVertexH0Class p.1 := by
    have hmap :
        ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap A =
          singularPostcomposition i := rfl
    dsimp only [q, hinc]
    rw [hmap]
    exact singularVertexH0Class_naturality i p
  haveI : Mono (q ≫ hinc) := hcomp ▸ singularVertexH0Class_mono p.1
  have hretract : hinc = inv q ≫ (q ≫ hinc) := by simp
  change Mono hinc
  rw [hretract]
  exact mono_comp (inv q) (q ≫ hinc)

/-- The boundary inclusion of the three-dimensional closed disk is injective
on zeroth singular homology. -/
theorem closedDiskBoundary_homologyMap_mono_zero :
    Mono (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap
        (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundarySet 3)) 0) := by
  letI : ContractibleSpace
      (euclideanClosedDisk 3) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  letI : PathConnectedSpace
      (euclideanUnitSphere 3) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere (by rw [← Module.finrank_eq_rank']; norm_num) 0
        (by norm_num))
  letI : PathConnectedSpace
      (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundarySet 3) :=
    (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundaryHomeomorph 3).symm.surjective.pathConnectedSpace
      (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundaryHomeomorph 3).symm.continuous
  exact pathConnectedSubspace_homologyMap_mono_zero _

/-- Consequently, the degree-zero kernel at the end of the native disk-pair
long exact sequence is zero. -/
theorem closedDiskBoundary_homologyKernel_isZero :
    IsZero (kernel (HomologicalComplex.homologyMap
      (ConstructionTargets.SingularHomologyConcrete.singularSubspaceMap
        (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundarySet 3)) 0)) := by
  rw [← Preadditive.mono_iff_isZero_kernel]
  exact closedDiskBoundary_homologyMap_mono_zero

/-- The disk-pair calculation now gives the required endpoint
`H₁(S³) = 0`. -/
theorem sphereThree_homology_one_isZero :
    IsZero (ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
      (TopCat.of (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 3))) :=
  (ConstructionTargets.T02A06SphereShift.sphereH1IsoNativeDiskH0Kernel 3).isZero_iff.mpr
    closedDiskBoundary_homologyKernel_isZero

/-- One suspension shift transports the endpoint calculation to
`H₂(S⁴) = 0`. -/
theorem sphereFour_homology_two_isZero :
    IsZero (ConstructionTargets.SingularHomologyConcrete.SingularHomology 2
      (TopCat.of (ConstructionTargets.T02A06HemisphereExcision.ambientSphere 4))) := by
  apply (ConstructionTargets.T02A06SphereShift.spherePositiveHomologyShift
    4 1 (by decide)).isZero_iff.mpr
  exact sphereThree_homology_one_isZero

#print axioms singularEdgeOfPath_boundary
#print axioms singularVertexH0Class_eq_of_path
#print axioms zeroChainH0Class_epi
#print axioms singularGenerator_zeroChainH0Class
#print axioms singularVertexH0Class_epi
#print axioms singularVertexH0Class_mono
#print axioms singularVertexH0Class_naturality
#print axioms pathConnectedSubspace_homologyMap_mono_zero
#print axioms closedDiskBoundary_homologyMap_mono_zero
#print axioms closedDiskBoundary_homologyKernel_isZero
#print axioms sphereThree_homology_one_isZero
#print axioms sphereFour_homology_two_isZero

end ConstructionTargets.T02A06SphereH0
