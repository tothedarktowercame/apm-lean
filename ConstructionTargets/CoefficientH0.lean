import ConstructionTargets.SingularH0Augmentation
import ConstructionTargets.SphereHomology
noncomputable section
namespace ConstructionTargets.CoefficientH0
open CategoryTheory CategoryTheory.Limits
open SingularSubdivision T02A06SphereH0
variable (R : Type) [CommRing R]
abbrev SingularChains (X : TopCat) :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).obj X
abbrev SingularHomology (k : ℕ) (X : TopCat) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat R) k).obj (ModuleCat.of R R)).obj X
private abbrev Chains (X : Type) [TopologicalSpace X] := SingularChains R (TopCat.of X)
def singularGenerator (X : TopCat) (n : ℕ) (σ : SingularSimplex X n) :
    ModuleCat.of R R ⟶ (SingularChains R X).X n :=
  by
    change ModuleCat.of R R ⟶
      ∐ fun _ : SingularSimplex X n ↦ ModuleCat.of R R
    exact Limits.Sigma.ι (fun _ : SingularSimplex X n ↦ ModuleCat.of R R) σ

theorem singularGenerator_boundary (X : TopCat) (n : ℕ)
    (σ : SingularSimplex X (n + 1)) :
    singularGenerator R X (n + 1) σ ≫ (SingularChains R X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        singularGenerator R X n ((TopCat.toSSet.obj X).δ i σ) := by
  dsimp [singularGenerator , SingularChains ,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  unfold AlgebraicTopology.AlternatingFaceMapComplex.objD
  calc
    _ = ∑ i : Fin (n + 2), Limits.Sigma.ι
          (fun _ : SingularSimplex X (n + 1) ↦ ModuleCat.of R R) σ ≫
        ((-1 : ℤ) ^ (i : ℕ) •
          ((((SimplicialObject.whiskering Type (ModuleCat R)).obj
              (CategoryTheory.Limits.sigmaConst.obj (ModuleCat.of R R))).obj
                (TopCat.toSSet.obj X)).δ i)) := by
      simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte]
        using Preadditive.comp_sum (Finset.univ : Finset (Fin (n + 2)))
          (Limits.Sigma.ι
            (fun _ : SingularSimplex X (n + 1) ↦ ModuleCat.of R R) σ)
          (fun i ↦ (-1 : ℤ) ^ (i : ℕ) •
            ((((SimplicialObject.whiskering Type (ModuleCat R)).obj
                (CategoryTheory.Limits.sigmaConst.obj (ModuleCat.of R R))).obj
                  (TopCat.toSSet.obj X)).δ i))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = (-1 : ℤ) ^ (i : ℕ) •
            (Limits.Sigma.ι
              (fun _ : SingularSimplex X (n + 1) ↦ ModuleCat.of R R) σ ≫
              ((((SimplicialObject.whiskering Type (ModuleCat R)).obj
                (CategoryTheory.Limits.sigmaConst.obj (ModuleCat.of R R))).obj
                  (TopCat.toSSet.obj X)).δ i)) := by
          exact CategoryTheory.Preadditive.comp_zsmul
            (Limits.Sigma.ι
              (fun _ : SingularSimplex X (n + 1) ↦ ModuleCat.of R R) σ)
            (((((SimplicialObject.whiskering Type (ModuleCat R)).obj
              (CategoryTheory.Limits.sigmaConst.obj (ModuleCat.of R R))).obj
                (TopCat.toSSet.obj X)).δ i))
            ((-1 : ℤ) ^ (i : ℕ))
        _ = _ := by
          congr 1
          dsimp [singularGenerator , SimplicialObject.δ,
            SimplicialObject.whiskering, CategoryTheory.Limits.sigmaConst]
          rw [Limits.Sigma.ι_comp_map']
          simp
def singularPostcomposition {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    SingularChains R (TopCat.of X) ⟶ SingularChains R (TopCat.of Y) :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat R)).obj
    (ModuleCat.of R R)).map (TopCat.ofHom f)

theorem singularGenerator_singularPostcomposition {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (τ : C(stdSimplex ℝ (Fin (n + 1)), X)) (f : C(X, Y)) :
    singularGenerator R (TopCat.of X) n
        (singularSimplexOfContinuousMap _ n τ) ≫
        (singularPostcomposition R f).f n =
      singularGenerator R (TopCat.of Y) n
        (singularSimplexOfContinuousMap _ n (f.comp τ)) := by
  dsimp [singularGenerator , singularPostcomposition , SingularChains ,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  rw [Limits.Sigma.ι_comp_map']
  congr 1

/-- A path gives a singular edge whose boundary is endpoint minus startpoint. -/
theorem singularEdgeOfPath_boundary
    {X : Type} [TopologicalSpace X] {x y : X} (γ : Path x y) :
    singularGenerator R (TopCat.of X) 1
        (singularSimplexOfContinuousMap (TopCat.of X) 1
          (singularEdgeOfPath γ)) ≫
        (SingularChains R (TopCat.of X)).d 1 0 =
      singularGenerator R (TopCat.of X) 0
          (singularSimplexOfContinuousMap (TopCat.of X) 0
            (singularVertexAt y)) -
        singularGenerator R (TopCat.of X) 0
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
  rw [singularGenerator_boundary R]
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ,
    Finset.sum_range_succ]
  simp [hface0, hface1, sub_eq_add_neg]

/-- The homology class of the singular zero-simplex at a point. -/
noncomputable def singularVertexH0Class
    {X : Type} [TopologicalSpace X] (x : X) :
    ModuleCat.of R R ⟶
      SingularHomology R 0
        (TopCat.of X) :=
  (SingularChains R (TopCat.of X)).liftCycles
      (singularGenerator R (TopCat.of X) 0
        (singularSimplexOfContinuousMap (TopCat.of X) 0
          (singularVertexAt x))) 0 (by simp) (by simp) ≫
    (SingularChains R (TopCat.of X)).homologyπ 0

/-- Path-connected points determine the same class in zeroth singular
homology. -/
theorem singularVertexH0Class_eq_of_path
    {X : Type} [TopologicalSpace X] {x y : X} (γ : Path x y) :
    singularVertexH0Class R x = singularVertexH0Class R y := by
  let K := SingularChains R (TopCat.of X)
  let vx := singularGenerator R (TopCat.of X) 0
    (singularSimplexOfContinuousMap (TopCat.of X) 0 (singularVertexAt x))
  let vy := singularGenerator R (TopCat.of X) 0
    (singularSimplexOfContinuousMap (TopCat.of X) 0 (singularVertexAt y))
  let e := singularGenerator R (TopCat.of X) 1
    (singularSimplexOfContinuousMap (TopCat.of X) 1 (singularEdgeOfPath γ))
  have hboundary : vy - vx = e ≫ K.d 1 0 := by
    rw [singularEdgeOfPath_boundary R γ]
  have hz : (vy - vx) ≫ K.d 0 0 = 0 := by simp
  have hzero : K.liftCycles (vy - vx) 0 (by simp) hz ≫ K.homologyπ 0 = 0 :=
    K.liftCycles_homologyπ_eq_zero_of_boundary
      (vy - vx) 0 (by simp) e hboundary
  have hlift : K.liftCycles (vy - vx) 0 (by simp) hz =
      K.liftCycles vy 0 (by simp) (by simp) -
        K.liftCycles vx 0 (by simp) (by simp) := by
    apply (cancel_mono (K.iCycles 0)).1
    rw [K.liftCycles_i, Preadditive.sub_comp, K.liftCycles_i, K.liftCycles_i]
  have hclasses : singularVertexH0Class R y - singularVertexH0Class R x = 0 := by
    rw [singularVertexH0Class, singularVertexH0Class]
    rw [← Preadditive.sub_comp, ← hlift]
    exact hzero
  exact (sub_eq_zero.mp hclasses).symm

/-- In degree zero every chain is a cycle. -/
noncomputable def zeroChainsToCycles
    {X : Type} [TopologicalSpace X] :
    (SingularChains R (TopCat.of X)).X 0 ⟶
      (SingularChains R (TopCat.of X)).cycles 0 :=
  (SingularChains R (TopCat.of X)).liftCycles (𝟙 _) 0 (by simp) (by simp)

@[reassoc (attr := simp)] theorem zeroChainsToCycles_i
    {X : Type} [TopologicalSpace X] :
    zeroChainsToCycles R (X := X) ≫
      (SingularChains R (TopCat.of X)).iCycles 0 = 𝟙 _ := by
  rw [zeroChainsToCycles, (SingularChains R (TopCat.of X)).liftCycles_i]

theorem iCycles_zeroChainsToCycles
    {X : Type} [TopologicalSpace X] :
    (SingularChains R (TopCat.of X)).iCycles 0 ≫
      zeroChainsToCycles R (X := X) = 𝟙 _ := by
  apply (cancel_mono ((SingularChains R (TopCat.of X)).iCycles 0)).1
  rw [Category.assoc, zeroChainsToCycles_i R, Category.comp_id,
    Category.id_comp]

noncomputable instance zeroChainsToCycles_epi
    {X : Type} [TopologicalSpace X] :
    Epi (zeroChainsToCycles R (X := X)) := by
  constructor
  intro Z g h w
  have hw := congrArg
    (fun k => (SingularChains R (TopCat.of X)).iCycles 0 ≫ k) w
  simpa only [← Category.assoc, iCycles_zeroChainsToCycles R,
    Category.id_comp] using hw

/-- The canonical projection from singular zero-chains to zeroth homology. -/
noncomputable def zeroChainH0Class
    {X : Type} [TopologicalSpace X] :
    (SingularChains R (TopCat.of X)).X 0 ⟶
      SingularHomology R 0
        (TopCat.of X) :=
  zeroChainsToCycles R ≫ (SingularChains R (TopCat.of X)).homologyπ 0

noncomputable instance zeroChainH0Class_epi
    {X : Type} [TopologicalSpace X] :
    Epi (zeroChainH0Class R (X := X)) := by
  letI : Epi ((SingularChains R (TopCat.of X)).homologyπ 0) :=
    Limits.epi_of_isColimit_cofork ((SingularChains R (TopCat.of X)).homologyIsCokernel 1 0 (by simp))
  change Epi (zeroChainsToCycles R (X := X) ≫ (SingularChains R (TopCat.of X)).homologyπ 0)
  exact epi_comp (zeroChainsToCycles R (X := X)) ((SingularChains R (TopCat.of X)).homologyπ 0)

theorem singularGenerator_zeroChainH0Class
    {X : Type} [TopologicalSpace X]
    (s : SingularSimplex (TopCat.of X) 0) :
    singularGenerator R (TopCat.of X) 0 s ≫ zeroChainH0Class R =
      singularVertexH0Class R (singularZeroSimplexPoint s) := by
  let p := singularZeroSimplexPoint s
  have hs : s = singularSimplexOfContinuousMap (TopCat.of X) 0
      (singularVertexAt p) := singularZeroSimplex_eq_vertex s
  change singularGenerator R (TopCat.of X) 0 s ≫ zeroChainH0Class R =
    singularVertexH0Class R p
  rw [hs]
  let g := singularGenerator R (TopCat.of X) 0
    (singularSimplexOfContinuousMap (TopCat.of X) 0
      (singularVertexAt p))
  have hg : g ≫ zeroChainsToCycles R =
      (SingularChains R (TopCat.of X)).liftCycles g 0 (by simp) (by simp) := by
    apply (cancel_mono ((SingularChains R (TopCat.of X)).iCycles 0)).1
    rw [Category.assoc, zeroChainsToCycles_i R,
      (SingularChains R (TopCat.of X)).liftCycles_i,
      Category.comp_id]
  change (g ≫ zeroChainsToCycles R) ≫
      (SingularChains R (TopCat.of X)).homologyπ 0 =
    (SingularChains R (TopCat.of X)).liftCycles g 0 (by simp) (by simp) ≫
      (SingularChains R (TopCat.of X)).homologyπ 0
  rw [hg]

/-- Sum all coefficients of a singular zero-chain. -/
noncomputable def zeroChainAugmentation
    {X : Type} [TopologicalSpace X] :
    (SingularChains R (TopCat.of X)).X 0 ⟶ ModuleCat.of R R := by
  change (∐ fun _ : SingularSimplex (TopCat.of X) 0 ↦
    ModuleCat.of R R) ⟶ ModuleCat.of R R
  exact Limits.Sigma.desc fun _ => 𝟙 _

/-- On a path-connected space, every zero-chain class is its coefficient sum
times the class of one chosen basepoint. -/
theorem zeroChainH0Class_eq_augmentation_comp_vertex
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (p : X) :
    zeroChainH0Class R (X := X) =
      zeroChainAugmentation R ≫ singularVertexH0Class R p := by
  apply Limits.Sigma.hom_ext
  intro s
  change singularGenerator R (TopCat.of X) 0 s ≫ zeroChainH0Class R =
    (singularGenerator R (TopCat.of X) 0 s ≫ zeroChainAugmentation R) ≫
      singularVertexH0Class R p
  rw [singularGenerator_zeroChainH0Class R]
  change singularVertexH0Class R (singularZeroSimplexPoint s) =
    (Limits.Sigma.ι (fun _ : SingularSimplex (TopCat.of X) 0 ↦
      ModuleCat.of R R) s ≫ Limits.Sigma.desc (fun _ => 𝟙 _)) ≫
        singularVertexH0Class R p
  rw [Limits.Sigma.ι_desc, Category.id_comp]
  exact (singularVertexH0Class_eq_of_path R
    (PathConnectedSpace.joined p (singularZeroSimplexPoint s)).somePath).symm

/-- The coefficient sum of the boundary of every singular one-chain is zero. -/
theorem boundary_comp_zeroChainAugmentation_eq_zero
    {X : Type} [TopologicalSpace X] :
    (Chains R X).d 1 0 ≫
        zeroChainAugmentation R (X := X) = 0 := by
  apply Limits.Sigma.hom_ext
  intro s
  change singularGenerator R
      (TopCat.of X) 1 s ≫ (Chains R X).d 1 0 ≫
        zeroChainAugmentation R = 0
  rw [← Category.assoc,
    singularGenerator_boundary R,
    Fin.sum_univ_two, Preadditive.add_comp, Preadditive.zsmul_comp]
  simp only [singularGenerator,
    zeroChainAugmentation]
  simp only [id_eq]
  norm_num
  erw [Limits.Sigma.ι_desc
      (fun _ : SingularSimplex
        (TopCat.of X) 0 ↦ 𝟙 (ModuleCat.of R R)) _,
    Limits.Sigma.ι_desc
      (fun _ : SingularSimplex
        (TopCat.of X) 0 ↦ 𝟙 (ModuleCat.of R R)) _]
  simp

/-- The coefficient sum on zero-cycles. -/
noncomputable def cyclesAugmentation
    {X : Type} [TopologicalSpace X] :
    (Chains R X).cycles 0 ⟶ ModuleCat.of R R :=
  (Chains R X).iCycles 0 ≫ zeroChainAugmentation R

theorem toCycles_comp_cyclesAugmentation_eq_zero
    {X : Type} [TopologicalSpace X] :
    (Chains R X).toCycles 1 0 ≫
        cyclesAugmentation R (X := X) = 0 := by
  rw [cyclesAugmentation, ← Category.assoc,
    HomologicalComplex.toCycles_i,
    boundary_comp_zeroChainAugmentation_eq_zero R]

/-- The canonical integral augmentation `H₀(X) ⟶ ℤ`, defined for every
topological space and without a connectedness hypothesis. -/
noncomputable def h0Augmentation
    {X : Type} [TopologicalSpace X] :
    SingularHomology R 0 (TopCat.of X) ⟶ ModuleCat.of R R :=
  ((Chains R X).homologyIsCokernel 1 0 (by simp)).desc
    (CokernelCofork.ofπ (cyclesAugmentation R (X := X))
      (toCycles_comp_cyclesAugmentation_eq_zero R (X := X)))

@[reassoc]
theorem homologyπ_comp_h0Augmentation
    {X : Type} [TopologicalSpace X] :
    (Chains R X).homologyπ 0 ≫ h0Augmentation R =
      cyclesAugmentation R (X := X) := by
  dsimp [h0Augmentation ]
  exact Cofork.IsColimit.π_desc
    ((Chains R X).homologyIsCokernel 1 0 (by simp))

theorem zeroChainH0Class_comp_h0Augmentation
    {X : Type} [TopologicalSpace X] :
    zeroChainH0Class R (X := X) ≫ h0Augmentation R =
      zeroChainAugmentation R := by
  change zeroChainsToCycles R ≫ (Chains R X).homologyπ 0 ≫
      h0Augmentation R = zeroChainAugmentation R
  rw [homologyπ_comp_h0Augmentation R]
  simp [cyclesAugmentation ]

/-- Postcomposition of singular zero-chains preserves coefficient sum. -/
theorem chainMap_comp_zeroChainAugmentation
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    (singularPostcomposition R f).f 0 ≫ zeroChainAugmentation R (X := Y) =
      zeroChainAugmentation R (X := X) := by
  apply Limits.Sigma.hom_ext
  intro s
  let τ := continuousMapOfSingularSimplex
    0 s
  change singularGenerator R
      (TopCat.of X) 0 s ≫ (singularPostcomposition R f).f 0 ≫
        zeroChainAugmentation R =
    singularGenerator R
      (TopCat.of X) 0 s ≫ zeroChainAugmentation R
  rw [← Category.assoc]
  change singularGenerator R
      (TopCat.of X) 0
        (singularSimplexOfContinuousMap
          (TopCat.of X) 0 τ) ≫ (singularPostcomposition R f).f 0 ≫
          zeroChainAugmentation R = _
  rw [← Category.assoc,
    singularGenerator_singularPostcomposition R]
  simp only [singularGenerator,
    zeroChainAugmentation]
  erw [Limits.Sigma.ι_desc
      (fun _ : SingularSimplex
        (TopCat.of Y) 0 ↦ 𝟙 (ModuleCat.of R R)) _,
    Limits.Sigma.ι_desc
      (fun _ : SingularSimplex
        (TopCat.of X) 0 ↦ 𝟙 (ModuleCat.of R R)) _]

/-- The canonical zero-chain class is natural under continuous maps. -/
theorem zeroChainH0Class_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    zeroChainH0Class R (X := X) ≫
        HomologicalComplex.homologyMap (singularPostcomposition R f) 0 =
      (singularPostcomposition R f).f 0 ≫ zeroChainH0Class R (X := Y) := by
  let KX := Chains R X
  let KY := Chains R Y
  have hcycles :
      zeroChainsToCycles R (X := X) ≫
          HomologicalComplex.cyclesMap (singularPostcomposition R f) 0 =
        (singularPostcomposition R f).f 0 ≫ zeroChainsToCycles R (X := Y) := by
    apply (cancel_mono (KY.iCycles 0)).1
    calc
      (zeroChainsToCycles R ≫
          HomologicalComplex.cyclesMap (singularPostcomposition R f) 0) ≫
          KY.iCycles 0 =
        zeroChainsToCycles R ≫
          (HomologicalComplex.cyclesMap (singularPostcomposition R f) 0 ≫
            KY.iCycles 0) := by rw [Category.assoc]
      _ = zeroChainsToCycles R ≫
          (KX.iCycles 0 ≫ (singularPostcomposition R f).f 0) := by
        rw [HomologicalComplex.cyclesMap_i]
      _ = (zeroChainsToCycles R ≫ KX.iCycles 0) ≫
          (singularPostcomposition R f).f 0 := by rw [Category.assoc]
      _ = (singularPostcomposition R f).f 0 := by
        rw [zeroChainsToCycles_i R, Category.id_comp]
      _ = ((singularPostcomposition R f).f 0 ≫ zeroChainsToCycles R) ≫
          KY.iCycles 0 := by
        rw [Category.assoc, zeroChainsToCycles_i R, Category.comp_id]
  change zeroChainsToCycles R ≫ KX.homologyπ 0 ≫
      HomologicalComplex.homologyMap (singularPostcomposition R f) 0 =
    (singularPostcomposition R f).f 0 ≫ zeroChainsToCycles R ≫
      KY.homologyπ 0
  calc
    _ = (zeroChainsToCycles R ≫
          HomologicalComplex.cyclesMap (singularPostcomposition R f) 0) ≫
        KY.homologyπ 0 := by
      rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
    _ = ((singularPostcomposition R f).f 0 ≫ zeroChainsToCycles R) ≫
        KY.homologyπ 0 := by rw [hcycles]
    _ = _ := by rw [Category.assoc]

/-- The integral `H₀` augmentation is natural under every continuous map. -/
theorem h0Augmentation_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    HomologicalComplex.homologyMap (singularPostcomposition R f) 0 ≫
        h0Augmentation R (X := Y) =
      h0Augmentation R (X := X) := by
  apply (cancel_epi (zeroChainH0Class R (X := X))).1
  calc
    zeroChainH0Class R (X := X) ≫
          (HomologicalComplex.homologyMap (singularPostcomposition R f) 0 ≫
            h0Augmentation R (X := Y)) =
        (zeroChainH0Class R (X := X) ≫
          HomologicalComplex.homologyMap (singularPostcomposition R f) 0) ≫
            h0Augmentation R (X := Y) := by rw [Category.assoc]
    _ = ((singularPostcomposition R f).f 0 ≫
          zeroChainH0Class R (X := Y)) ≫ h0Augmentation R (X := Y) := by
      rw [zeroChainH0Class_naturality R]
      rfl
    _ = (singularPostcomposition R f).f 0 ≫
          (zeroChainH0Class R (X := Y) ≫ h0Augmentation R (X := Y)) := by
      rw [Category.assoc]
    _ = (singularPostcomposition R f).f 0 ≫
          zeroChainAugmentation R (X := Y) := by
      rw [zeroChainH0Class_comp_h0Augmentation R]
    _ = zeroChainAugmentation R (X := X) := chainMap_comp_zeroChainAugmentation R f
    _ = zeroChainH0Class R (X := X) ≫ h0Augmentation R (X := X) :=
      (zeroChainH0Class_comp_h0Augmentation R).symm

/-- A chosen point splits the unrestricted `H₀` augmentation. -/
theorem singularVertexH0Class_comp_h0Augmentation
    {X : Type} [TopologicalSpace X] (x : X) :
    singularVertexH0Class R x ≫ h0Augmentation R = 𝟙 _ := by
  let s := singularSimplexOfContinuousMap
    (TopCat.of X) 0 (singularVertexAt x)
  let g := singularGenerator R
    (TopCat.of X) 0 s
  have hg : g ≫ zeroChainH0Class R = singularVertexH0Class R x :=
    singularGenerator_zeroChainH0Class R s
  rw [← hg, Category.assoc, zeroChainH0Class_comp_h0Augmentation R]
  change Limits.Sigma.ι
      (fun _ : SingularSimplex
        (TopCat.of X) 0 ↦ ModuleCat.of R R) s ≫
      Limits.Sigma.desc (fun _ ↦ 𝟙 (ModuleCat.of R R)) = 𝟙 _
  exact Limits.Sigma.ι_desc _ _



theorem augmentation_comp_vertex {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] (p : X) :
    h0Augmentation R (X := X) ≫ singularVertexH0Class R p = 𝟙 _ := by
  apply (cancel_epi (zeroChainH0Class R (X := X))).mp
  rw [← Category.assoc, zeroChainH0Class_comp_h0Augmentation, Category.comp_id]
  exact (zeroChainH0Class_eq_augmentation_comp_vertex R p).symm

def h0Iso {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (p : X) :
    SingularHomology R 0 (TopCat.of X) ≅ ModuleCat.of R R where
  hom := h0Augmentation R
  inv := singularVertexH0Class R p
  hom_inv_id := augmentation_comp_vertex R p
  inv_hom_id := singularVertexH0Class_comp_h0Augmentation R p

def sphereH0 (n : ℕ) [NeZero n] :
    SingularHomology R 0 (TopCat.of (SphereHomology.Sphere n)) ≅ ModuleCat.of R R :=
  h0Iso R (Classical.choice inferInstance)

def rationalS2H0 :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) 0).obj
      (ModuleCat.of ℚ ℚ)).obj
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))) ≅ ModuleCat.of ℚ ℚ :=
  sphereH0 ℚ 2

def integralS2H0 := sphereH0 ℤ 2

theorem identity_induced {X : Type} [TopologicalSpace X] :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat R) 0).obj
      (ModuleCat.of R R)).map (𝟙 (TopCat.of X)) = 𝟙 _ := CategoryTheory.Functor.map_id _ _

#print axioms singularEdgeOfPath_boundary
#print axioms singularVertexH0Class_eq_of_path
#print axioms h0Augmentation_naturality
#print axioms augmentation_comp_vertex
#print axioms h0Iso
#print axioms sphereH0
#print axioms rationalS2H0
#print axioms integralS2H0
#print axioms identity_induced
end ConstructionTargets.CoefficientH0
