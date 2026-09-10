import ConstructionTargets.CoefficientPairSequence
noncomputable section
namespace ConstructionTargets.CoefficientContractiblePair
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SingularHomologyConcrete
open CoefficientPairSequence
variable (R : Type) [CommRing R]
abbrev H (n : ℕ) (X : TopCat) := (((AlgebraicTopology.singularHomologyFunctor (ModuleCat R) n).obj (ModuleCat.of R R)).obj X)
theorem singularHomology_map_eq_of_topCatHomotopy
    {X Y : TopCat} {f g : X ⟶ Y} (h : X ⊗ TopCat.I ⟶ Y)
    (h₀ : TopCat.ι₀ ≫ h = f) (h₁ : TopCat.ι₁ ≫ h = g) (n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat R) n).obj
        (ModuleCat.of R R)).map f =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat R) n).obj
        (ModuleCat.of R R)).map g := by
  simpa [AlgebraicTopology.singularHomologyFunctor,
    AlgebraicTopology.singularChainComplexFunctor] using
    singularChainComplexFunctor_map_homology_eq_of_simplicialHomotopy
      (C := ModuleCat R) (R := ModuleCat.of R R)
      (f := TopCat.toSSet.map f) (g := TopCat.toSSet.map g)
      (H := (topCatHomotopyToSSet h h₀ h₁).toSimplicialObjectHomotopy) n

/-- A topological homotopy equivalence, presented by explicit cylinder
homotopies, induces an isomorphism on ordinary singular homology. -/
noncomputable def singularHomologyIsoOfTopCatHomotopyEquivalence
    {X Y : TopCat} (f : X ⟶ Y) (g : Y ⟶ X)
    (hX : X ⊗ TopCat.I ⟶ X)
    (hX₀ : TopCat.ι₀ ≫ hX = f ≫ g) (hX₁ : TopCat.ι₁ ≫ hX = 𝟙 X)
    (hY : Y ⊗ TopCat.I ⟶ Y)
    (hY₀ : TopCat.ι₀ ≫ hY = g ≫ f) (hY₁ : TopCat.ι₁ ≫ hY = 𝟙 Y)
    (n : ℕ) : H R n X ≅ H R n Y := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat R) n).obj
    (ModuleCat.of R R)
  letI : IsIso (F.map f) := IsIso.mk ⟨F.map g, by
    rw [← F.map_comp, singularHomology_map_eq_of_topCatHomotopy R hX hX₀ hX₁,
      F.map_id], by
    rw [← F.map_comp, singularHomology_map_eq_of_topCatHomotopy R hY hY₀ hY₁,
      F.map_id]⟩
  exact asIso (F.map f)

noncomputable def singularHomologyIsoOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    H R n (TopCat.of X) ≅ H R n (TopCat.of Y) :=
  singularHomologyIsoOfTopCatHomotopyEquivalence R
    (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)
    (continuousMapHomotopyCylinder (Classical.choice e.left_inv))
    (continuousMapHomotopyCylinder_zero (Classical.choice e.left_inv))
    (continuousMapHomotopyCylinder_one (Classical.choice e.left_inv))
    (continuousMapHomotopyCylinder (Classical.choice e.right_inv))
    (continuousMapHomotopyCylinder_zero (Classical.choice e.right_inv))
    (continuousMapHomotopyCylinder_one (Classical.choice e.right_inv)) n


def contractibleIsoPoint (X : Type) [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) :
    H R n (TopCat.of X) ≅ H R n (TopCat.of Unit) :=
  singularHomologyIsoOfHomotopyEquiv R (Classical.choice (ContractibleSpace.hequiv_unit X)) n

theorem higher_zero (X : Type) [TopologicalSpace X] [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero (H R n (TopCat.of X)) :=
  (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat R) n (ModuleCat.of R R) (TopCat.of Unit) hn).of_iso (contractibleIsoPoint R X n)

theorem contractibleSubspaceInclusion_homology_mono
    {X : Type} [TopologicalSpace X] (A : Set X) [ContractibleSpace A]
    (q : ℕ) :
    Mono (HomologicalComplex.homologyMap (inclusion R A) q) := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat R) q).obj
    (ModuleCat.of R R)
  obtain ⟨p, hp⟩ := id_nullhomotopic A
  obtain ⟨H⟩ := hp
  let r : C(X, A) := ContinuousMap.const X p
  have hcomp : F.map (subspaceInclusion A) ≫ F.map (TopCat.ofHom r) = 𝟙 _ := by
    rw [← F.map_comp]
    have hmaps : subspaceInclusion A ≫ TopCat.ofHom r =
        TopCat.ofHom (ContinuousMap.const A p) := by
      ext x
      rfl
    rw [hmaps]
    have heq := singularHomology_map_eq_of_topCatHomotopy R
      (continuousMapHomotopyCylinder H)
      (continuousMapHomotopyCylinder_zero H)
      (continuousMapHomotopyCylinder_one H) q
    rw [← heq]
    rw [show TopCat.ofHom (ContinuousMap.id A) = 𝟙 (TopCat.of A) by rfl,
      F.map_id]
  haveI : Mono (F.map (subspaceInclusion A) ≫ F.map (TopCat.ofHom r)) :=
    hcomp ▸ inferInstance
  change Mono (F.map (subspaceInclusion A))
  exact mono_of_mono_fac (f := F.map (TopCat.ofHom r))
    (h := F.map (subspaceInclusion A) ≫ F.map (TopCat.ofHom r)) rfl

/-- For a contractible subspace, the absolute-to-relative projection in
degree one is an isomorphism.  The only extra ingredient beyond higher
degrees is injectivity of the subspace map on `H₀`. -/
theorem singularPairProjection_degreeOne_isIso_of_contractible
    {X : Type} [TopologicalSpace X] (A : Set X) [ContractibleSpace A] :
    IsIso (HomologicalComplex.homologyMap (projection R A) 1) := by
  letI : Mono (HomologicalComplex.homologyMap
      (projection R A) 1) :=
    (exact_absolute R A 1).mono_g
      ((higher_zero R A 1 (by decide)).eq_of_src _ _)
  letI hinc : Mono (HomologicalComplex.homologyMap (inclusion R A) 0) :=
    contractibleSubspaceInclusion_homology_mono R A 0
  have hconn : connecting R A 0 = 0 :=
    (exact_subspace R A 0).mono_g_iff.mp hinc
  letI : Epi (HomologicalComplex.homologyMap
      (projection R A) 1) :=
    (exact_relative R A 0).epi_f hconn
  exact isIso_of_mono_of_epi _



variable {X : Type} [TopologicalSpace X] (A : Set X)

def contractibleConnectingIso [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    (relative R A).homology (n+1) ≅ (absolute R (X := A)).homology n :=
  connectingIso R A n (higher_zero R X (n+1) (by omega)) (higher_zero R X n hn)

def contractibleH1KernelIso [ContractibleSpace X] :
    (relative R A).homology 1 ≅ kernel (HomologicalComplex.homologyMap (inclusion R A) 0) :=
  relativeH1IsoKernel R A (higher_zero R X 1 (by decide))

theorem contractibleH1Kernel_projection [ContractibleSpace X] :
    (contractibleH1KernelIso R A).hom ≫ kernel.ι (HomologicalComplex.homologyMap (inclusion R A) 0) =
    connecting R A 0 := relativeH1IsoKernel_projection R A _

theorem projection_isIso [ContractibleSpace A] (q : ℕ) (hq : q ≠ 0) :
    IsIso (HomologicalComplex.homologyMap (projection R A) q) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  by_cases hn : n = 0
  · subst n
    exact singularPairProjection_degreeOne_isIso_of_contractible R A
  · letI : Mono (HomologicalComplex.homologyMap (projection R A) (n+1)) :=
      (exact_absolute R A (n+1)).mono_g ((higher_zero R A (n+1) (by omega)).eq_of_src _ _)
    letI : Epi (HomologicalComplex.homologyMap (projection R A) (n+1)) :=
      (exact_relative R A n).epi_f ((higher_zero R A n hn).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _

def projectionIso [ContractibleSpace A] (q : ℕ) (hq : q ≠ 0) :
    (absolute R (X := X)).homology q ≅ (relative R A).homology q := by
  exact @asIso _ _ _ _ (HomologicalComplex.homologyMap (projection R A) q) (projection_isIso R A q hq)

theorem projectionIso_hom [ContractibleSpace A] (q : ℕ) (hq : q ≠ 0) :
    (projectionIso R A q hq).hom = HomologicalComplex.homologyMap (projection R A) q := rfl

theorem projection_inverse_left [ContractibleSpace A] (q : ℕ) (hq : q ≠ 0) :
    (projectionIso R A q hq).inv ≫ HomologicalComplex.homologyMap (projection R A) q = 𝟙 _ :=
  (projectionIso R A q hq).inv_hom_id

theorem projection_inverse_right [ContractibleSpace A] (q : ℕ) (hq : q ≠ 0) :
    HomologicalComplex.homologyMap (projection R A) q ≫ (projectionIso R A q hq).inv = 𝟙 _ :=
  (projectionIso R A q hq).hom_inv_id

theorem connecting_hom [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    (contractibleConnectingIso R A n hn).hom = connecting R A n := rfl

theorem connecting_left [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    (contractibleConnectingIso R A n hn).inv ≫ connecting R A n = 𝟙 _ :=
  (contractibleConnectingIso R A n hn).inv_hom_id

theorem connecting_right [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    connecting R A n ≫ (contractibleConnectingIso R A n hn).inv = 𝟙 _ :=
  (contractibleConnectingIso R A n hn).hom_inv_id

/-- R and spaces are Type 0. Disk dimension zero and its empty boundary are retained. -/
def integral_disk (m n : ℕ) (hn : n ≠ 0) :=
  contractibleConnectingIso ℤ (T02A06DiskPairShift.diskBoundarySubset m) n hn

def rational_disk (m n : ℕ) (hn : n ≠ 0) :=
  contractibleConnectingIso ℚ (T02A06DiskPairShift.diskBoundarySubset m) n hn

def integral_disk_endpoint (m : ℕ) :=
  contractibleH1KernelIso ℤ (T02A06DiskPairShift.diskBoundarySubset m)

def rational_disk_endpoint (m : ℕ) :=
  contractibleH1KernelIso ℚ (T02A06DiskPairShift.diskBoundarySubset m)

def ballBoundary (m : ℕ) : Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) :=
  {x | ‖x.val‖ = 1}

def integral_native_ball (m n : ℕ) (hn : n ≠ 0) := by
  letI := Metric.contractibleSpace_closedBall (E := EuclideanSpace ℝ (Fin m)) (x := 0) (r := 1) (by norm_num)
  exact contractibleConnectingIso ℤ (ballBoundary m) n hn

def rational_native_ball (m n : ℕ) (hn : n ≠ 0) := by
  letI := Metric.contractibleSpace_closedBall (E := EuclideanSpace ℝ (Fin m)) (x := 0) (r := 1) (by norm_num)
  exact contractibleConnectingIso ℚ (ballBoundary m) n hn

def rational_native_endpoint (m : ℕ) := by
  letI := Metric.contractibleSpace_closedBall (E := EuclideanSpace ℝ (Fin m)) (x := 0) (r := 1) (by norm_num)
  exact contractibleH1KernelIso ℚ (ballBoundary m)

#print axioms higher_zero
#print axioms contractibleSubspaceInclusion_homology_mono
#print axioms contractibleH1Kernel_projection
#print axioms projection_isIso
#print axioms projectionIso_hom
#print axioms projection_inverse_left
#print axioms projection_inverse_right
#print axioms connecting_hom
#print axioms connecting_left
#print axioms connecting_right
#print axioms integral_disk
#print axioms rational_disk
#print axioms integral_disk_endpoint
#print axioms rational_disk_endpoint
#print axioms integral_native_ball
#print axioms rational_native_ball
#print axioms rational_native_endpoint
end ConstructionTargets.CoefficientContractiblePair
