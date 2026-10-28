import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.PointWedgePathConnected
import ConstructionTargets.GenericPointWedgeOpenCoverComparison
import ConstructionTargets.GenericPointWedgeOverlapInclusionSquares
import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.CoefficientH0
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.PolygonInnerOpenPointedContraction
import ConstructionTargets.RationalPolygonSurfaceHomology
import ConstructionTargets.CP2RationalHomology

/-! Rational homology and Lefschetz-number interfaces for finite point wedges
of the polygon model of the real projective plane. -/

open CategoryTheory CategoryTheory.Limits Set Topology
open scoped ContinuousMap

noncomputable section

namespace ConstructionTargets.ProjectivePlaneWedgeRationalHomology

open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.PointWedgePathConnected
open ConstructionTargets.PointedPuncturedCircleContraction
open ConstructionTargets.StatementSurfaceModels
open ConstructionTargets.RationalLefschetz

/-- The unreduced rational homology of `X` is that of a point. -/
def RationallyPointlike (X : Type) [TopologicalSpace X] : Prop :=
  Nonempty (Homology X 0 ≅ ModuleCat.of ℚ ℚ) ∧
    ∀ k : ℕ, 0 < k → IsZero (Homology X k)

/-- A basepoint has an open neighbourhood contracted to that basepoint. -/
def HasPointedContractibleNeighbourhood
    {X : Type} [TopologicalSpace X] (x : X) : Prop :=
  ∃ U : Set X, ∃ hx : x ∈ U, IsOpen U ∧
    Nonempty (PointedContraction U ⟨x, hx⟩)

/-- L1 (LIBRARY): the polygon `aa` calculation over `ℚ`. -/
theorem realProjectivePlane_rationallyPointlike :
    RationallyPointlike RealProjectivePlane := by
  open ConstructionTargets.RationalPolygonSurfaceHomology
    ConstructionTargets.PolygonSurfacePiOne ConstructionTargets.PolygonSurfaceHomology in
  let P := standardPairingData false 1 one_pos
  let φ : P.Space ≃ₜ RealProjectivePlane := standardPairingData_space_homeomorph false 1 one_pos
  have hiso : ∀ k, Homology RealProjectivePlane k ≅ Homology P.Space k := fun k =>
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).mapIso (TopCat.isoOfHomeo φ).symm
  obtain ⟨⟨h0⟩, ⟨h1⟩, ⟨h2⟩, h3⟩ := polygonQuotient_homology P
  obtain ⟨hfin1, hr1, hr2⟩ := polygonNF_standard_boundary_ranks false 1 one_pos
  have r0 := ratUC_rationalHomology_finrank P.Space 0 ℤ h0
  have r1 := ratUC_rationalHomology_finrank P.Space 1 _ h1
  have r2 := ratUC_rationalHomology_finrank P.Space 2 _ h2
  have zero_of : ∀ k, FiniteDimensional ℚ (Homology P.Space k) →
      Module.finrank ℚ (Homology P.Space k) = 0 →
      IsZero (Homology RealProjectivePlane k) := by
    intro k hfd hr
    have : Subsingleton (Homology P.Space k) := Module.finrank_zero_iff.mp hr
    exact (ModuleCat.isZero_of_subsingleton _).of_iso (hiso k)
  refine ⟨?_, ?_⟩
  · haveI := r0.1
    have hr : Module.finrank ℚ (Homology P.Space 0) =
        Module.finrank ℚ (ModuleCat.of ℚ ℚ) := by
      rw [r0.2]; simp
    exact ⟨hiso 0 ≪≫ (LinearEquiv.ofFinrankEq _ _ hr).toModuleIso⟩
  · intro k hk
    rcases k with _ | _ | _ | k
    · omega
    · exact zero_of 1 r1.1 (by rw [r1.2, hr1]; rfl)
    · exact zero_of 2 r2.1 (by rw [r2.2, hr2]; rfl)
    · have z := ratUC_rationalHomology_finrank P.Space (k + 3) PUnit
        ((h3 (k + 3) (by omega)).iso
          (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℤ PUnit)))
      exact zero_of _ z.1 (by simpa using z.2)

/-- L2: the polygon quotient is path connected. -/
theorem realProjectivePlane_pathConnected :
    PathConnectedSpace RealProjectivePlane := by
  letI : PathConnectedSpace ConstructionTargets.Surfaces.Disk :=
    isPathConnected_iff_pathConnectedSpace.mp
      (Metric.isPathConnected_closedBall (by norm_num : (0 : ℝ) ≤ 1))
  exact
    (ConstructionTargets.Surfaces.surjective_surfaceQuotient false 1).pathConnectedSpace
      (ConstructionTargets.Surfaces.continuous_surfaceQuotient false 1)

/-- L3: the image of the polygon centre has a small pointed contractible
neighbourhood. -/
theorem surfacePoint_hasPointedContractibleNeighbourhood :
    HasPointedContractibleNeighbourhood (surfacePoint false 1) := by
  open ConstructionTargets.PolygonRadialOpenCover
    ConstructionTargets.PolygonInnerOpenPointedContraction in
  exact ⟨innerOpen (Surfaces.SurfaceRel false 1), (innerBase _).2,
    innerOpen_isOpen _ (fun {_ _} h => surfaceRel_radius_eq false 1 h),
    ⟨innerOpenPointedContraction _
      (fun {_ _} h => surfaceRel_radius_eq false 1 h)
      (fun {_ _} h => ConstructionTargets.PolygonOuterRadialRelation.surfaceRel_boundary false 1 h)⟩⟩

/-- (Wb) Rational pointlikeness is a homotopy invariant (homotopy invariance
of singular homology: `SingularHomologyHomotopy`). -/
noncomputable def rationallyPointlike_of_homotopyEquiv_aux_iso
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₕ B) (k : ℕ) : Homology A k ≅ Homology B k where
  hom := induced e.toFun k
  inv := induced e.invFun k
  hom_inv_id := by
    dsimp only [induced]
    rw [← Functor.map_comp]
    change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom (e.invFun.comp e.toFun)) = _
    rw [ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℚ) (ModuleCat.of ℚ ℚ) e.left_inv k]
    exact ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).map_id (TopCat.of A)
  inv_hom_id := by
    dsimp only [induced]
    rw [← Functor.map_comp]
    change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom (e.toFun.comp e.invFun)) = _
    rw [ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℚ) (ModuleCat.of ℚ ℚ) e.right_inv k]
    exact ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).map_id (TopCat.of B)

theorem rationallyPointlike_of_homotopyEquiv {A B : Type}
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₕ B)
    (h : RationallyPointlike B) : RationallyPointlike A := by
  rcases h with ⟨⟨h0⟩, hp⟩
  refine ⟨⟨rationallyPointlike_of_homotopyEquiv_aux_iso e 0 ≪≫ h0⟩, ?_⟩
  intro k hk
  exact (hp k hk).of_iso (rationallyPointlike_of_homotopyEquiv_aux_iso e k)

/-- (Wc) A point has the rational homology of a point. -/
theorem rationallyPointlike_unit : RationallyPointlike Unit := by
  refine ⟨?_, ?_⟩
  · exact ⟨(
      AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace
          (ModuleCat ℚ) (ModuleCat.of ℚ ℚ) (TopCat.of Unit) ≪≫
        Limits.coproductUniqueIso (fun _ : Unit ↦ ModuleCat.of ℚ ℚ))⟩
  · intro k hk
    exact
      AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
        (ModuleCat ℚ) k (ModuleCat.of ℚ ℚ) (TopCat.of Unit)
        (Nat.ne_of_gt hk)

/-- (Wa) Two open pieces with nonempty intersection, all three rationally
pointlike, give a rationally pointlike union.  Use the generic rational
Mayer--Vietoris `RP3Homology.rationalMayerVietoris`
(`ConstructionTargets/CP2RationalHomology.lean`); degree-zero surjectivity of
`H₀ U ⊕ H₀ V → H₀ Z` is not part of that theorem and comes from points: every
point lies in `U` or `V`. -/
lemma rationallyPointlike_of_openCover_aux_h0Map_bijective
    {A B : Type} [TopologicalSpace A] [TopologicalSpace B] [Nonempty A]
    (f : C(A, B)) (hA : RationallyPointlike A) (hB : RationallyPointlike B) :
    Function.Bijective
      (HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientH0.singularPostcomposition ℚ f) 0).hom := by
  obtain ⟨eA⟩ := hA.1
  obtain ⟨eB⟩ := hB.1
  letI : FiniteDimensional ℚ (Homology A 0) :=
    Module.Finite.equiv eA.toLinearEquiv.symm
  letI : FiniteDimensional ℚ (Homology B 0) :=
    Module.Finite.equiv eB.toLinearEquiv.symm
  let εA : Homology A 0 ⟶ ModuleCat.of ℚ ℚ :=
    ConstructionTargets.CoefficientH0.h0Augmentation ℚ
  let εB : Homology B 0 ⟶ ModuleCat.of ℚ ℚ :=
    ConstructionTargets.CoefficientH0.h0Augmentation ℚ
  have hsA : Function.Surjective εA.hom := by
    intro a
    refine ⟨(ConstructionTargets.CoefficientH0.singularVertexH0Class ℚ
      (Classical.choice (inferInstance : Nonempty A))).hom a, ?_⟩
    exact congrArg (fun g => g.hom a)
      (ConstructionTargets.CoefficientH0.singularVertexH0Class_comp_h0Augmentation
        ℚ (Classical.choice (inferInstance : Nonempty A)))
  have hdA : Module.finrank ℚ (Homology A 0) =
      Module.finrank ℚ (ModuleCat.of ℚ ℚ) := by
    simpa using eA.toLinearEquiv.finrank_eq
  have hiA : Function.Injective εA.hom :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdA).2 hsA
  let F := HomologicalComplex.homologyMap
    (ConstructionTargets.CoefficientH0.singularPostcomposition ℚ f) 0
  have hiF : Function.Injective F.hom := by
    intro x y hxy
    apply hiA
    have hn := ConstructionTargets.CoefficientH0.h0Augmentation_naturality ℚ f
    have hx := congrArg (fun g => g.hom x) hn
    have hy := congrArg (fun g => g.hom y) hn
    simp only [CategoryTheory.comp_apply] at hx hy
    exact hx.symm.trans (congrArg εB.hom hxy |>.trans hy)
  have hd : Module.finrank ℚ (Homology A 0) = Module.finrank ℚ (Homology B 0) := by
    rw [eA.toLinearEquiv.finrank_eq, eB.toLinearEquiv.finrank_eq]
  exact ⟨hiF, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1 hiF⟩

lemma rationallyPointlike_of_openCover_aux_elem_zero
    {M : ModuleCat ℚ} (hM : IsZero M) (x : M) : x = 0 := by
  have h := congrArg (fun f : M ⟶ M => f.hom x) (hM.eq_of_tgt (𝟙 M) 0)
  simpa using h

lemma rationallyPointlike_of_openCover_aux_biprod_zero
    {M N : ModuleCat ℚ} (hM : IsZero M) (hN : IsZero N) : IsZero (M ⊞ N) := by
  rw [biprod_isZero_iff]
  exact ⟨hM, hN⟩

lemma rationallyPointlike_of_openCover_aux_exact_zero
    {A B C : ModuleCat ℚ} (f : A ⟶ B) (g : B ⟶ C)
    (hA : IsZero A) (hC : IsZero C)
    (hex : LinearMap.range f.hom = LinearMap.ker g.hom) : IsZero B := by
  letI : Subsingleton B := ⟨by
    intro x y
    suffices hz : ∀ z : B, z = 0 by exact (hz x).trans (hz y).symm
    intro z
    have hgz : g.hom z = 0 := rationallyPointlike_of_openCover_aux_elem_zero hC _
    have hzker : z ∈ LinearMap.ker g.hom := hgz
    rw [← hex] at hzker
    obtain ⟨a, ha⟩ := hzker
    rw [← ha, rationallyPointlike_of_openCover_aux_elem_zero hA a, map_zero]⟩
  exact ModuleCat.isZero_of_subsingleton _

def rationallyPointlike_of_openCover_aux_codiagonal
    {I P Q : ModuleCat ℚ} (i : I ≅ P) (j : I ≅ Q) : P ⊞ Q ⟶ I :=
  biprod.desc i.inv j.inv

def rationallyPointlike_of_openCover_aux_cokernelCofork
    {I P Q : ModuleCat ℚ} (i : I ≅ P) (j : I ≅ Q) :
    CokernelCofork (biprod.lift i.hom (-j.hom)) :=
  CokernelCofork.ofπ (rationallyPointlike_of_openCover_aux_codiagonal i j) (by
    simp [rationallyPointlike_of_openCover_aux_codiagonal])

def rationallyPointlike_of_openCover_aux_cokernelIsColimit
    {I P Q : ModuleCat ℚ} (i : I ≅ P) (j : I ≅ Q) :
    IsColimit (rationallyPointlike_of_openCover_aux_cokernelCofork i j) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨i.hom ≫ biprod.inl ≫ s.π, by
      have hs : biprod.lift i.hom (-j.hom) ≫ s.π = 0 := by
        simpa only [zero_comp] using s.condition
      have hdecomp : s.π =
          biprod.desc (biprod.inl ≫ s.π) (biprod.inr ≫ s.π) := by
        apply biprod.hom_ext' <;> simp
      have hs' : i.hom ≫ biprod.inl ≫ s.π = j.hom ≫ biprod.inr ≫ s.π := by
        rw [← sub_eq_zero]
        rw [hdecomp, biprod.lift_desc] at hs
        simpa only [Category.assoc, Preadditive.neg_comp, sub_eq_add_neg] using hs
      apply biprod.hom_ext'
      · simp [rationallyPointlike_of_openCover_aux_cokernelCofork,
          rationallyPointlike_of_openCover_aux_codiagonal]
      · have h := congrArg (fun k => j.inv ≫ k) hs'
        simpa [rationallyPointlike_of_openCover_aux_cokernelCofork,
          rationallyPointlike_of_openCover_aux_codiagonal, Category.assoc] using h,
    fun {m} hm => by
      rw [← hm]
      simp [rationallyPointlike_of_openCover_aux_cokernelCofork,
        rationallyPointlike_of_openCover_aux_codiagonal]⟩

def rationallyPointlike_of_openCover_aux_targetIso
    {I P Q X : ModuleCat ℚ} (i : I ≅ P) (j : I ≅ Q) (r : P ⊞ Q ⟶ X)
    (hr : biprod.lift i.hom (-j.hom) ≫ r = 0)
    (hex : (ShortComplex.mk (biprod.lift i.hom (-j.hom)) r hr).Exact)
    [Epi r] : X ≅ I := by
  let S := ShortComplex.mk (biprod.lift i.hom (-j.hom)) r hr
  let hR : IsColimit (CokernelCofork.ofπ r hr) :=
    (S.exact_and_epi_g_iff_g_is_cokernel.mp ⟨hex, inferInstance⟩).some
  exact hR.coconePointUniqueUpToIso
    (rationallyPointlike_of_openCover_aux_cokernelIsColimit i j)

theorem rationallyPointlike_of_openCover {Z : Type} [TopologicalSpace Z]
    (U V : Set Z) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hne : (U ∩ V).Nonempty)
    (hUp : RationallyPointlike U) (hVp : RationallyPointlike V)
    (hIp : RationallyPointlike ↥(U ∩ V)) : RationallyPointlike Z := by
  open RP3Homology in
    letI : Nonempty ↥(U ∩ V) := hne.to_subtype
    letI : Nonempty U := ⟨⟨hne.choose, hne.choose_spec.1⟩⟩
    letI : Nonempty V := ⟨⟨hne.choose, hne.choose_spec.2⟩⟩
    obtain ⟨δ, e1, e2, e3⟩ := rationalMayerVietoris U V hU hV hcov
    let iU : C(↥(U ∩ V), U) :=
      ⟨Set.inclusion Set.inter_subset_left, continuous_inclusion _⟩
    let iV : C(↥(U ∩ V), V) :=
      ⟨Set.inclusion Set.inter_subset_right, continuous_inclusion _⟩
    have biU := rationallyPointlike_of_openCover_aux_h0Map_bijective iU hIp hUp
    have biV := rationallyPointlike_of_openCover_aux_h0Map_bijective iV hIp hVp
    have hi0 : Function.Injective (mvI U V 0).hom := by
      intro x y hxy
      apply biU.1
      have h := congrArg (fun z =>
        ((biprod.fst : Homology U 0 ⊞ Homology V 0 ⟶ Homology U 0).hom z)) hxy
      have hc : ((mvI U V 0 ≫
          (biprod.fst : Homology U 0 ⊞ Homology V 0 ⟶ Homology U 0)).hom x) =
          ((mvI U V 0 ≫ biprod.fst).hom y) := by
        simpa [ModuleCat.comp_apply] using h
      rw [show mvI U V 0 ≫ biprod.fst = mvIncl Set.inter_subset_left 0 by
        simp [mvI]] at hc
      simpa [mvIncl, iU] using hc
    have hJ0epi : Epi (mvJ U V 0) := by
      haveI : Epi (rationalMayerVietoris_aux_SC U V).g :=
        (ConstructionTargets.CoefficientSubcomplexMayerVietoris.shortExact
        ℚ (rationalMayerVietoris_aux_P U) (rationalMayerVietoris_aux_P V)).epi_g
      have hg : Epi (HomologicalComplex.homologyMap
          (rationalMayerVietoris_aux_SC U V).g 0) :=
        HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
          (rationalMayerVietoris_aux_SC U V).g 0 (by
          intro j hj
          dsimp at hj
          omega)
      apply (ModuleCat.epi_iff_surjective (mvJ U V 0)).2
      rw [← rationalMayerVietoris_aux_unionArrow U V hU hV hcov 0]
      exact ((ConcreteCategory.bijective_of_isIso
        (rationalMayerVietoris_aux_unionIso U V hU hV hcov 0).hom).2).comp
          (((ModuleCat.epi_iff_surjective _).1 hg).comp
            (ConcreteCategory.bijective_of_isIso
              (rationalMayerVietoris_aux_pieceIso U V 0).inv).2)
    have hJ0surj : Function.Surjective (mvJ U V 0).hom :=
      (ModuleCat.epi_iff_surjective (mvJ U V 0)).mp hJ0epi
    obtain ⟨eI⟩ := hIp.1
    let fU := HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientH0.singularPostcomposition ℚ iU) 0
    let fV := HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientH0.singularPostcomposition ℚ iV) 0
    letI : IsIso fU := (ConcreteCategory.isIso_iff_bijective fU).2 biU
    letI : IsIso fV := (ConcreteCategory.isIso_iff_bijective fV).2 biV
    let isoU := asIso fU
    let isoV := (asIso fV) ≪≫ rationalMayerVietoris_aux_negIso _
    have hmvI : mvI U V 0 = biprod.lift isoU.hom (-isoV.hom) := by
      dsimp [mvI]
      congr 1
      simp [isoV, rationalMayerVietoris_aux_negIso]
      rfl
    have hzero : biprod.lift isoU.hom (-isoV.hom) ≫ mvJ U V 0 = 0 := by
      rw [← hmvI]
      apply ModuleCat.hom_ext
      ext x
      change (mvJ U V 0).hom ((mvI U V 0).hom x) = 0
      have hx : (mvI U V 0).hom x ∈ LinearMap.range (mvI U V 0).hom := ⟨x, rfl⟩
      rw [e1 0] at hx
      exact hx
    have hex : (ShortComplex.mk (biprod.lift isoU.hom (-isoV.hom))
        (mvJ U V 0) hzero).Exact := by
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      simpa [hmvI] using e1 0
    haveI : Epi (mvJ U V 0) := hJ0epi
    have h0iso : Nonempty (Homology Z 0 ≅ ModuleCat.of ℚ ℚ) :=
      ⟨(@rationallyPointlike_of_openCover_aux_targetIso _ _ _ _ isoU isoV
        (mvJ U V 0) hzero hex hJ0epi) ≪≫ eI⟩
    refine ⟨h0iso, ?_⟩
    intro k hk
    rcases k with _ | k
    · omega
    rcases k with _ | k
    · have hr : LinearMap.range (δ 0).hom = ⊥ := by
        rw [e3 0, LinearMap.ker_eq_bot]
        exact hi0
      have hd : (δ 0).hom = 0 := LinearMap.range_eq_bot.mp hr
      have hz := rationallyPointlike_of_openCover_aux_biprod_zero
        (hUp.2 1 (by omega)) (hVp.2 1 (by omega))
      letI : Subsingleton (Homology Z 1) := ⟨by
        intro x y
        suffices hh : ∀ z : Homology Z 1, z = 0 by exact (hh x).trans (hh y).symm
        intro z
        have hzker : z ∈ LinearMap.ker (δ 0).hom := by rw [hd]; simp
        rw [← e2 0] at hzker
        obtain ⟨a, ha⟩ := hzker
        rw [← ha, rationallyPointlike_of_openCover_aux_elem_zero hz a, map_zero]⟩
      exact ModuleCat.isZero_of_subsingleton _
    · apply rationallyPointlike_of_openCover_aux_exact_zero
        (mvJ U V (k + 2)) (δ (k + 1))
      · exact rationallyPointlike_of_openCover_aux_biprod_zero
          (hUp.2 _ (by omega)) (hVp.2 _ (by omega))
      · exact hIp.2 _ (by omega)
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using e2 (k + 1)

/-- L4 (LIBRARY): rational Mayer--Vietoris for a point wedge.  The local
hypotheses rule out wild wedges such as the Hawaiian earring. -/
theorem wedge_rationallyPointlike
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y)
    (hX : RationallyPointlike X) (hY : RationallyPointlike Y)
    (hnX : HasPointedContractibleNeighbourhood x₀)
    (hnY : HasPointedContractibleNeighbourhood y₀) :
    RationallyPointlike (Wedge x₀ y₀) := by
  open ConstructionTargets.GenericPointWedgeOpenCoverComparison in
  obtain ⟨M, hy, hM, ⟨cM⟩⟩ := hnY
  obtain ⟨N, hx, hN, ⟨cN⟩⟩ := hnX
  let P := genericPointWedgeCoverPackage x₀ y₀ M N hM hN hy hx cM cN
  exact rationallyPointlike_of_openCover _ _ P.leftOpen_isOpen P.rightOpen_isOpen
    P.union_eq_univ ⟨_, (P.intersectionEquiv.invFun ()).2⟩
    (rationallyPointlike_of_homotopyEquiv P.leftEquiv hX)
    (rationallyPointlike_of_homotopyEquiv P.rightEquiv hY)
    (rationallyPointlike_of_homotopyEquiv P.intersectionEquiv rationallyPointlike_unit)

/-- L5: pointed contractible neighbourhoods persist at the point of a
binary wedge. -/
def wedgePoint_hasPointedContractibleNeighbourhood_aux_sum
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ : X} {y₀ : Y} (hX : PointedContraction X x₀)
    (hY : PointedContraction Y y₀) (t : unitInterval) :
    Sum X Y → Wedge x₀ y₀
  | .inl x => quotientMap x₀ y₀ (.inl (hX.homotopy (t, x)))
  | .inr y => quotientMap x₀ y₀ (.inr (hY.homotopy (t, y)))

private theorem wedgePoint_hasPointedContractibleNeighbourhood_aux_respects
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ : X} {y₀ : Y} (hX : PointedContraction X x₀)
    (hY : PointedContraction Y y₀) (t : unitInterval) (a b : Sum X Y)
    (hab : Relation.EqvGen (Rel x₀ y₀) a b) :
    wedgePoint_hasPointedContractibleNeighbourhood_aux_sum hX hY t a =
      wedgePoint_hasPointedContractibleNeighbourhood_aux_sum hX hY t b := by
  induction hab with
  | rel a b hab =>
      cases hab
      change quotientMap x₀ y₀ (.inl (hX.homotopy (t, x₀))) =
        quotientMap x₀ y₀ (.inr (hY.homotopy (t, y₀)))
      rw [hX.fixed, hY.fixed]
      exact Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def wedgePoint_hasPointedContractibleNeighbourhood_aux_map
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ : X} {y₀ : Y} (hX : PointedContraction X x₀)
    (hY : PointedContraction Y y₀) :
    unitInterval × Wedge x₀ y₀ → Wedge x₀ y₀ :=
  fun p => Quotient.lift
    (wedgePoint_hasPointedContractibleNeighbourhood_aux_sum hX hY p.1)
    (wedgePoint_hasPointedContractibleNeighbourhood_aux_respects hX hY p.1) p.2

theorem wedgePoint_hasPointedContractibleNeighbourhood_aux_continuous
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ : X} {y₀ : Y} (hX : PointedContraction X x₀)
    (hY : PointedContraction Y y₀) :
    Continuous (wedgePoint_hasPointedContractibleNeighbourhood_aux_map hX hY) := by
  have hq : Topology.IsQuotientMap (quotientMap x₀ y₀) :=
    isQuotientMap_quotient_mk'
  apply hq.continuous_lift_prod_right
  let g : (unitInterval × X) ⊕ (unitInterval × Y) → Wedge x₀ y₀
    | .inl p => quotientMap x₀ y₀ (.inl (hX.homotopy p))
    | .inr p => quotientMap x₀ y₀ (.inr (hY.homotopy p))
  have hg : Continuous g := by
    rw [continuous_sum_dom]
    exact ⟨(continuous_quotientMap x₀ y₀).comp
      (continuous_inl.comp hX.homotopy.continuous),
      (continuous_quotientMap x₀ y₀).comp
        (continuous_inr.comp hY.homotopy.continuous)⟩
  have heq : (fun p : unitInterval × Sum X Y =>
      wedgePoint_hasPointedContractibleNeighbourhood_aux_map hX hY
        (p.1, quotientMap x₀ y₀ p.2)) =
      g ∘ Homeomorph.prodSumDistrib := by
    funext p
    rcases p with ⟨t, s⟩
    cases s <;> rfl
  rw [heq]
  exact hg.comp Homeomorph.prodSumDistrib.continuous

def wedgePoint_hasPointedContractibleNeighbourhood_aux_contraction
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ : X} {y₀ : Y} (hX : PointedContraction X x₀)
    (hY : PointedContraction Y y₀) :
    PointedContraction (Wedge x₀ y₀) (quotientMap x₀ y₀ (.inl x₀)) where
  homotopy :=
    { toFun := wedgePoint_hasPointedContractibleNeighbourhood_aux_map hX hY
      continuous_toFun :=
        wedgePoint_hasPointedContractibleNeighbourhood_aux_continuous hX hY
      map_zero_left := by
        rintro ⟨a⟩
        cases a with
        | inl x =>
            change quotientMap x₀ y₀ (Sum.inl (hX.homotopy (0, x))) =
              quotientMap x₀ y₀ (Sum.inl x)
            exact congrArg (fun z => quotientMap x₀ y₀ (Sum.inl z))
              (hX.homotopy.map_zero_left x)
        | inr y =>
            change quotientMap x₀ y₀ (Sum.inr (hY.homotopy (0, y))) =
              quotientMap x₀ y₀ (Sum.inr y)
            exact congrArg (fun z => quotientMap x₀ y₀ (Sum.inr z))
              (hY.homotopy.map_zero_left y)
      map_one_left := by
        rintro ⟨a⟩
        cases a with
        | inl x =>
            change quotientMap x₀ y₀ (Sum.inl (hX.homotopy (1, x))) =
              quotientMap x₀ y₀ (Sum.inl x₀)
            exact congrArg (fun z => quotientMap x₀ y₀ (Sum.inl z))
              (hX.homotopy.map_one_left x)
        | inr y =>
            calc
              quotientMap x₀ y₀ (.inr (hY.homotopy (1, y))) =
                  quotientMap x₀ y₀ (.inr y₀) := congrArg
                    (fun z => quotientMap x₀ y₀ (.inr z))
                    (hY.homotopy.map_one_left y)
              _ = quotientMap x₀ y₀ (.inl x₀) :=
                (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)).symm }
  fixed := by
    intro t
    change quotientMap x₀ y₀ (.inl (hX.homotopy (t, x₀))) = _
    rw [hX.fixed]

def wedgePoint_hasPointedContractibleNeighbourhood_aux_transport
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ : X} (e : X ≃ₜ Y) (h : PointedContraction Y (e x₀)) :
    PointedContraction X x₀ where
  homotopy :=
    { toFun := fun p => e.symm (h.homotopy (p.1, e p.2))
      continuous_toFun := e.symm.continuous.comp
        (h.homotopy.continuous.comp
          (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
      map_zero_left := by intro x; simp
      map_one_left := by intro x; simp }
  fixed := by
    intro t
    change e.symm (h.homotopy (t, e x₀)) = x₀
    rw [h.fixed]
    exact e.symm_apply_apply x₀

theorem wedgePoint_hasPointedContractibleNeighbourhood
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y)
    (hnX : HasPointedContractibleNeighbourhood x₀)
    (hnY : HasPointedContractibleNeighbourhood y₀) :
    HasPointedContractibleNeighbourhood (quotientMap x₀ y₀ (.inl x₀)) := by
  rcases hnX with ⟨A, hx, hA, ⟨cA⟩⟩
  rcases hnY with ⟨B, hy, hB, ⟨cB⟩⟩
  let U := ConstructionTargets.PointWedgeRestrictedOpenQuotient.restrictedOpen
    x₀ y₀ A B
  have hU : IsOpen U :=
    ConstructionTargets.PointWedgeRestrictedOpenQuotient.restrictedOpen_isOpen
      hA hB hx hy
  have hp : quotientMap x₀ y₀ (.inl x₀) ∈ U := ⟨.inl x₀, hx, rfl⟩
  let e : U ≃ₜ Wedge (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B) :=
    ConstructionTargets.PointWedgeRestrictedOpenQuotient.restrictedOpenHomeomorphWedge
      hA hB hx hy
  let c := wedgePoint_hasPointedContractibleNeighbourhood_aux_contraction cA cB
  have he : e ⟨_, hp⟩ = quotientMap (⟨x₀, hx⟩ : A) (⟨y₀, hy⟩ : B)
      (.inl ⟨x₀, hx⟩) :=
    ConstructionTargets.PointWedgeRestrictedOpenQuotient.restrictedOpenHomeomorphWedge_left
      _ _ _ _ _ _
  rw [← he] at c
  exact ⟨U, hp, hU,
    ⟨wedgePoint_hasPointedContractibleNeighbourhood_aux_transport e c⟩⟩

/-- L6: every endomorphism acts identically on one-dimensional `H₀` of a
path-connected space. -/
theorem induced_zero_eq_id
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (e : Homology X 0 ≅ ModuleCat.of ℚ ℚ) (f : C(X, X)) :
    (induced f 0).hom = LinearMap.id := by
  open ConstructionTargets.CoefficientH0 in
    letI : FiniteDimensional ℚ (Homology X 0) :=
      Module.Finite.equiv e.toLinearEquiv.symm
    let ε : Homology X 0 ⟶ ModuleCat.of ℚ ℚ := h0Augmentation ℚ
    let p : X := Classical.choice inferInstance
    have hsurj : Function.Surjective ε := by
      intro a
      refine ⟨singularVertexH0Class ℚ p a, ?_⟩
      exact congrArg (fun g => g a)
        (singularVertexH0Class_comp_h0Augmentation ℚ p)
    have hdim : Module.finrank ℚ (Homology X 0) =
        Module.finrank ℚ (ModuleCat.of ℚ ℚ) := by
      simpa using e.toLinearEquiv.finrank_eq
    have hinj : Function.Injective ε :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
    letI : Mono ε := (ModuleCat.mono_iff_injective ε).2 hinj
    have hcat : (induced f 0) ≫ ε = (𝟙 _) ≫ ε := by
      rw [Category.id_comp]
      change HomologicalComplex.homologyMap
          (singularPostcomposition ℚ f) 0 ≫ ε = ε
      exact h0Augmentation_naturality ℚ f
    have h := (cancel_mono ε).1 hcat
    exact congrArg (fun g => g.hom) h

/-- A path-connected rational homology point has Lefschetz number one for
every self-map. -/
theorem lefschetzNumber_one_of_rationallyPointlike
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (hX : RationallyPointlike X) :
    ∀ f : C(X, X), HasLefschetzNumber f 1 := by
  intro f
  obtain ⟨e⟩ := hX.1
  letI : FiniteDimensional ℚ (Homology X 0) :=
    Module.Finite.equiv e.toLinearEquiv.symm
  have hfd : ∀ k, FiniteDimensional ℚ (Homology X k) := by
    intro k
    by_cases hk : k = 0
    · subst k
      infer_instance
    · letI : Subsingleton (Homology X k) :=
        ModuleCat.subsingleton_of_isZero (hX.2 k (Nat.pos_of_ne_zero hk))
      exact Module.Finite.of_surjective (0 : ℚ →ₗ[ℚ] Homology X k)
        (fun x ↦ ⟨0, Subsingleton.elim _ _⟩)
  refine ⟨hfd, 0, ?_, ?_⟩
  · intro k hk
    exact ModuleCat.subsingleton_of_isZero (hX.2 k hk)
  · simp only [Nat.zero_add, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, pow_zero, one_mul]
    rw [induced_zero_eq_id e f, LinearMap.trace_id]
    have hrank : Module.finrank ℚ (Homology X 0) = 1 := by
      simpa using e.toLinearEquiv.finrank_eq
    simp [hrank]

/-- The standard twofold projective-plane wedge is rationally pointlike. -/
theorem projectivePlaneWedge_rationallyPointlike :
    RationallyPointlike ProjectivePlaneWedge := by
  exact wedge_rationallyPointlike _ _
    realProjectivePlane_rationallyPointlike
    realProjectivePlane_rationallyPointlike
    surfacePoint_hasPointedContractibleNeighbourhood
    surfacePoint_hasPointedContractibleNeighbourhood

/-- Its wedge point has the same local regularity, allowing iteration. -/
theorem projectivePlaneWedge_pointedNeighbourhood :
    HasPointedContractibleNeighbourhood
      (quotientMap (surfacePoint false 1) (surfacePoint false 1)
        (.inl (surfacePoint false 1))) := by
  exact wedgePoint_hasPointedContractibleNeighbourhood _ _
    surfacePoint_hasPointedContractibleNeighbourhood
    surfacePoint_hasPointedContractibleNeighbourhood

end ConstructionTargets.ProjectivePlaneWedgeRationalHomology
