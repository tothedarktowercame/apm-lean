import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.IntegralSingularHomologyComparison
import ConstructionTargets.SingularH0Augmentation
import ConstructionTargets.SignedDiagonalCokernel

/-!
# Endpoint adapter for the integral Mayer--Vietoris sequence

The production open-cover sequence exposes exactness in every nonnegative
degree.  At degree zero the chain-level reassembly map is already epic, since
there is no outgoing differential.  This file records the corresponding
homology-level endpoint and transports it to the production presentation.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.T00A01MayerVietorisAdapters

open ConstructionTargets.SingularExcision
open ConstructionTargets.SingularSubdivision
open ConstructionTargets.BooleanTwoCoverScaffold
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.IntegralSingularHomologyComparison
open ConstructionTargets.SingularH0Augmentation
open ConstructionTargets.SignedDiagonalCokernel

/-- Two consecutive exact triples with zero outer objects identify their
shared arrow as an isomorphism. -/
theorem isIso_middle_of_two_exact_of_isZero_ends
    {C : Type*} [Category C] [Abelian C]
    {A B C' D : C} (f : A ⟶ B) (g : B ⟶ C') (h : C' ⟶ D)
    (hfg : f ≫ g = 0) (hgh : g ≫ h = 0)
    (hex₁ : (ShortComplex.mk f g hfg).Exact)
    (hex₂ : (ShortComplex.mk g h hgh).Exact)
    (hA : IsZero A) (hD : IsZero D) : IsIso g := by
  haveI : Mono g := hex₁.mono_g_iff.mpr (hA.eq_of_src _ _)
  haveI : Epi g := hex₂.epi_f_iff.mpr (hD.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi g

/-- Homotopy-equivalence invariance in the `ModuleCat ℤ` presentation used by
the frozen `t00A01` statement. -/
noncomputable def moduleHomologyIsoOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)) ≅
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y)) :=
  moduleIsoOfUnderlyingIso
    (singularHomologyComparison (TopCat.of X) n ≪≫
      singularHomologyIsoOfHomotopyEquiv e n ≪≫
      (singularHomologyComparison (TopCat.of Y) n).symm)

/-- The stored Boolean-cover reassembly map is epic on zeroth homology. -/
noncomputable instance booleanReassemblyHomologyMap_epi_zero
    {X : Type} [TopologicalSpace X] (U V : Set X) :
    Epi (HomologicalComplex.homologyMap (shortComplex U V).g 0) := by
  letI : Epi (shortComplex U V).g :=
    (subcomplexMayerVietorisShortComplex_shortExact
      (leftRange U) (rightRange V)).epi_g
  exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
    (shortComplex U V).g 0 (by
      intro j hj
      dsimp at hj
      omega)

/-- For an open two-cover, the actual sum-of-inclusions map onto the ambient
zeroth singular homology is epic. -/
noncomputable instance productionReassemblyArrow_epi_zero
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    Epi (productionReassemblyArrow U V 0) := by
  rw [← booleanReassemblyArrow_eq_production U V hU hV hcover 0]
  infer_instance

/-- The H₀ map of a subspace inclusion, packaged as an isomorphism whenever
both spaces have integral H₀ coordinate `ℤ`. -/
noncomputable def h0SubspaceInclusionIso
    {X : Type} [TopologicalSpace X] {A B : Set X} (h : A ⊆ B)
    [Nonempty A] [Nonempty B]
    (eA : SingularHomology 0 (TopCat.of A) ≅ AddCommGrpCat.of ℤ)
    (eB : SingularHomology 0 (TopCat.of B) ≅ AddCommGrpCat.of ℤ) :
    SingularHomology 0 (TopCat.of A) ≅ SingularHomology 0 (TopCat.of B) := by
  let f : C(A, B) :=
    ⟨fun x ↦ ⟨x.1, h x.2⟩, continuous_subtype_val.subtype_mk _⟩
  exact @asIso _ _ _ _
    (HomologicalComplex.homologyMap (singularPostcomposition f) 0)
    (h0Map_isIso_of_iso_int f eA eB)

/-- The degree-zero Mayer--Vietoris target has the common integral coordinate
of a nonempty intersection and two nonempty cover pieces. -/
noncomputable def openCoverH0IsoOfCoordinates
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [Nonempty (U ∩ V : Set X)] [Nonempty U] [Nonempty V]
    (eI : SingularHomology 0 (TopCat.of (U ∩ V : Set X)) ≅ AddCommGrpCat.of ℤ)
    (eU : SingularHomology 0 (TopCat.of U) ≅ AddCommGrpCat.of ℤ)
    (eV : SingularHomology 0 (TopCat.of V) ≅ AddCommGrpCat.of ℤ) :
    SingularHomology 0 (TopCat.of X) ≅ AddCommGrpCat.of ℤ := by
  let fi : C((U ∩ V : Set X), U) :=
    ⟨fun x ↦ ⟨x.1, Set.inter_subset_left x.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  let fj : C((U ∩ V : Set X), V) :=
    ⟨fun x ↦ ⟨x.1, Set.inter_subset_right x.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  have hi0 : IsIso (HomologicalComplex.homologyMap
      (singularPostcomposition fi) 0) := h0Map_isIso_of_iso_int fi eI eU
  have hj0 : IsIso (HomologicalComplex.homologyMap
      (singularPostcomposition fj) 0) := h0Map_isIso_of_iso_int fj eI eV
  let imap := HomologicalComplex.homologyMap
      (((AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.toSSet.map
          (topologicalSubspaceInclusion (X := X) (A := U ∩ V) (B := U)
            Set.inter_subset_left))) 0
  let jmap := HomologicalComplex.homologyMap
      (((AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.toSSet.map
          (topologicalSubspaceInclusion (X := X) (A := U ∩ V) (B := V)
            Set.inter_subset_right))) 0
  have hi : IsIso imap := by
    rw [show imap = HomologicalComplex.homologyMap
      (singularPostcomposition fi) 0 from
        topologicalSubspaceInclusion_homologyMap _ 0]
    exact hi0
  have hj : IsIso jmap := by
    rw [show jmap = HomologicalComplex.homologyMap
      (singularPostcomposition fj) 0 from
        topologicalSubspaceInclusion_homologyMap _ 0]
    exact hj0
  let i := @asIso _ _ _ _ imap hi
  let j := @asIso _ _ _ _ jmap hj
  have harrow : productionIntersectionArrow U V 0 =
      biprod.lift i.hom (-j.hom) := by
    rfl
  have hstored : HomologicalComplex.homologyMap (shortComplex U V).f 0 ≫
      HomologicalComplex.homologyMap (shortComplex U V).g 0 = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, (shortComplex U V).zero,
      HomologicalComplex.homologyMap_zero]
  have hz : productionIntersectionArrow U V 0 ≫
      productionReassemblyArrow U V 0 = 0 := by
    rw [← booleanIntersectionArrow_eq_production U V 0,
      ← booleanReassemblyArrow_eq_production U V hU hV hcover 0]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    calc
      _ = (booleanIntersectionProductionHomologyIso U V 0).inv ≫
          (HomologicalComplex.homologyMap (shortComplex U V).f 0 ≫
            HomologicalComplex.homologyMap (shortComplex U V).g 0) ≫
          (booleanUnionProductionHomologyIso U V hU hV hcover 0).hom := by
            simp only [Category.assoc]
      _ = 0 := by rw [hstored, zero_comp, comp_zero]
  let hr : biprod.lift i.hom (-j.hom) ≫
      productionReassemblyArrow U V 0 = 0 := by
    simpa only [← harrow] using hz
  let hex : (ShortComplex.mk (biprod.lift i.hom (-j.hom))
      (productionReassemblyArrow U V 0) hr).Exact := by
    simpa only [harrow] using
      productionMayerVietoris_exact_pieces U V hU hV hcover 0
  exact @exactEpiSignedLiftTargetIsoOfCoordinate _ _ _ _ _ _ _ _
    eI i j (productionReassemblyArrow U V 0) hr hex
    (productionReassemblyArrow_epi_zero U V hU hV hcover)

/-- If both cover pieces vanish in two adjacent degrees, the production
connecting arrow between them is an isomorphism. -/
theorem productionConnecting_isIso_of_pieces_isZero
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ)
    (hU' : IsZero (SingularHomology (n + 1) (TopCat.of U)))
    (hV' : IsZero (SingularHomology (n + 1) (TopCat.of V)))
    (hU0 : IsZero (SingularHomology n (TopCat.of U)))
    (hV0 : IsZero (SingularHomology n (TopCat.of V))) :
    IsIso (productionConnecting U V hU hV hcover n) := by
  apply isIso_middle_of_two_exact_of_isZero_ends
    (productionReassemblyArrow U V (n + 1))
    (productionConnecting U V hU hV hcover n)
    (productionIntersectionArrow U V n)
    _ _
    (productionMayerVietoris_exact_union U V hU hV hcover n)
    (productionMayerVietoris_exact_intersection U V hU hV hcover n)
  · exact (biprod_isZero_iff _ _).mpr ⟨hU', hV'⟩
  · exact (biprod_isZero_iff _ _).mpr ⟨hU0, hV0⟩

/-- Transfer a frozen `ModuleCat ℤ` vanishing hypothesis back to the
additive-group presentation used by production Mayer--Vietoris. -/
theorem groupHomologyIsZeroOfModuleHomologyIsZero
    (X : TopCat) (n : ℕ)
    (h : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).obj X)) :
    IsZero (SingularHomology n X) := by
  exact (forgetIntModules.map_isZero h).of_iso
    (singularHomologyComparison X n).symm

end ConstructionTargets.T00A01MayerVietorisAdapters

#print axioms ConstructionTargets.T00A01MayerVietorisAdapters.productionReassemblyArrow_epi_zero
#print axioms ConstructionTargets.T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv
#print axioms ConstructionTargets.T00A01MayerVietorisAdapters.isIso_middle_of_two_exact_of_isZero_ends
#print axioms ConstructionTargets.T00A01MayerVietorisAdapters.h0SubspaceInclusionIso
#print axioms ConstructionTargets.T00A01MayerVietorisAdapters.openCoverH0IsoOfCoordinates
#print axioms ConstructionTargets.T00A01MayerVietorisAdapters.productionConnecting_isIso_of_pieces_isZero
#print axioms ConstructionTargets.T00A01MayerVietorisAdapters.groupHomologyIsZeroOfModuleHomologyIsZero
