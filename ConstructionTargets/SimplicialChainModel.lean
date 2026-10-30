import ConstructionTargets.SimplicialSingularQuasiIso

/-! The last steps of the finite chain model for the Lefschetz argument, from
`orientedPackage_homology_bijective` on. They moved out of `SimplicialChainMaps`
(claude-14, 2026-10-30) so that they can use `orderedFace_singular_quasiIso`
from `SimplicialSingularQuasiIso`, which itself imports `SimplicialChainMaps`.
The namespace is unchanged. -/
open Set CategoryTheory
open ConstructionTargets.OrientedSimplicialChains
open ConstructionTargets.RationalLefschetz

noncomputable section
namespace ConstructionTargets.SimplicialChainMaps

/-- An oriented package's comparison is a quasi-isomorphism. Transport
`SimplicialSingularComparison.orderedFace_singular_quasiIso` (stated with
`ChainComplex.ofHom`) to `cmpH` through the identity map from
`ChainComplex.of _ (fun j ↦ C.d (j+1) j) _` to `C`, as in the map `e` at the end of
`vertexChainMap_affineComparison_square`. That theorem is the accepted interface:
its own `sorry` is tracked in SimplicialSingularComparison, so use it. -/
theorem orientedPackage_homology_bijective {n : ℕ} (o : LinearOrder (Euc n)) (K : GSC n)
    (hK : K.faces.Finite) (d : ∀ k, FaceModuleCat K (k+1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k+1) ≫ d k = 0)
    (cmp : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (hcmp : IsAffineComparison K cmp)
    (cmpH : ChainComplex.of _ d hdd ⟶ CoefficientH0.SingularChains ℚ (TopCat.of K.space))
    (cmpH_f : ∀ k, cmpH.f k = cmp k) :
    ∀ k, Function.Bijective (HomologicalComplex.homologyMap cmpH k).hom := by
  have hchain : ∀ k, cmp (k + 1) ≫
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 1) k =
        d k ≫ cmp k := by
    intro k
    rw [← cmpH_f, ← cmpH_f]
    simpa only [ChainComplex.of_d] using cmpH.comm (k + 1) k
  let q := ChainComplex.ofHom _ _ hdd _ _
    (fun k => (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d_comp_d
      (k + 2) (k + 1) k) cmp hchain
  let C := CoefficientH0.SingularChains ℚ (TopCat.of K.space)
  let e : ChainComplex.of _ (fun j ↦ C.d (j + 1) j)
      (fun j ↦ C.d_comp_d (j + 2) (j + 1) j) ⟶ C :=
    { f := fun _ ↦ 𝟙 _
      comm' := by
        rintro i j (rfl : j + 1 = i)
        simp [ChainComplex.of_d] }
  have hq : q ≫ e = cmpH := by
    ext k x
    simpa [q, e] using congrArg (fun f ↦ f x) (cmpH_f k).symm
  rw [← hq]
  intro k
  have hb := SimplicialSingularComparison.orderedFace_singular_quasiIso
    o K hK d hd hdd cmp hcmp hchain k
  letI (i : ℕ) : IsIso (e.f i) := by
    dsimp [e]
    infer_instance
  letI : IsIso e := HomologicalComplex.Hom.isIso_of_components e
  have he : Function.Bijective (HomologicalComplex.homologyMap e k).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [HomologicalComplex.homologyMap_comp]
  exact he.comp hb

/-- The composite `sd ≫ hm` is conjugate on homology to `e ∘ g ∘ e⁻¹`. Apply
`homologyMap_comp`, then `hv` and `hsd`, reassociating. Then
`induced (setCongr hspace.symm) ≫ induced f = induced (e ∘ g ∘ e⁻¹)`: replace `f`
using `hhom` (`SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic`,
used in the same way as in `LefschetzCompactPolyhedron`), then use functoriality
(`Functor.map_comp`, with `setCongr hspace.symm` followed by `setCongr hspace`
equal to `id` by `ext; rfl`). -/
theorem oriented_model_aux_conj {X : Type} [TopologicalSpace X] {n : ℕ} (K K' : GSC n)
    (hspace : K'.space = K.space) (e : X ≃ₜ K.space) (g : C(X,X)) (f : C(K'.space, K.space))
    {CK CK' : ChainComplex (ModuleCat ℚ) ℕ} (sdH : CK ⟶ CK') (hmH : CK' ⟶ CK)
    (cmpKH : CK ⟶ CoefficientH0.SingularChains ℚ (TopCat.of K.space))
    (cmpK'H : CK' ⟶ CoefficientH0.SingularChains ℚ (TopCat.of K'.space))
    (hsd : ∀ k, HomologicalComplex.homologyMap sdH k ≫ HomologicalComplex.homologyMap cmpK'H k =
      HomologicalComplex.homologyMap cmpKH k ≫ induced (Homeomorph.setCongr hspace.symm) k)
    (hv : ∀ k, HomologicalComplex.homologyMap hmH k ≫ HomologicalComplex.homologyMap cmpKH k =
      HomologicalComplex.homologyMap cmpK'H k ≫ induced f k)
    (hhom : ContinuousMap.Homotopic
      ((homeomorphMap e).comp (g.comp ((homeomorphMap e.symm).comp
        (homeomorphMap (Homeomorph.setCongr hspace : K'.space ≃ₜ K.space))))) f) :
    ∀ k, HomologicalComplex.homologyMap (sdH ≫ hmH) k ≫ HomologicalComplex.homologyMap cmpKH k =
      HomologicalComplex.homologyMap cmpKH k ≫
        induced ((homeomorphMap e).comp (g.comp (homeomorphMap e.symm))) k := by
  intro k
  have hf :=
    ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℚ) (ModuleCat.of ℚ ℚ) hhom k
  change induced
      ((homeomorphMap e).comp (g.comp ((homeomorphMap e.symm).comp
        (homeomorphMap (Homeomorph.setCongr hspace))))) k = induced f k at hf
  have hind :
      induced (homeomorphMap (Homeomorph.setCongr hspace.symm)) k ≫ induced f k =
        induced ((homeomorphMap e).comp (g.comp (homeomorphMap e.symm))) k := by
    rw [← hf]
    unfold induced
    rw [← Functor.map_comp, ← TopCat.ofHom_comp]
    congr 1
  calc
    HomologicalComplex.homologyMap (sdH ≫ hmH) k ≫
        HomologicalComplex.homologyMap cmpKH k =
      HomologicalComplex.homologyMap sdH k ≫
        (HomologicalComplex.homologyMap hmH k ≫
          HomologicalComplex.homologyMap cmpKH k) := by
            rw [HomologicalComplex.homologyMap_comp, Category.assoc]
    _ = HomologicalComplex.homologyMap sdH k ≫
        (HomologicalComplex.homologyMap cmpK'H k ≫ induced f k) := by
      exact congrArg (fun z => HomologicalComplex.homologyMap sdH k ≫ z) (hv k)
    _ = (HomologicalComplex.homologyMap sdH k ≫
        HomologicalComplex.homologyMap cmpK'H k) ≫ induced f k :=
      (Category.assoc _ _ _).symm
    _ = (HomologicalComplex.homologyMap cmpKH k ≫
        induced (homeomorphMap (Homeomorph.setCongr hspace.symm)) k) ≫ induced f k := by
      exact congrArg (fun z => z ≫ induced f k) (hsd k)
    _ = HomologicalComplex.homologyMap cmpKH k ≫
        induced ((homeomorphMap e).comp (g.comp (homeomorphMap e.symm))) k := by
      exact (Category.assoc _ _ _).trans
        (congrArg (fun z => HomologicalComplex.homologyMap cmpKH k ≫ z) hind)

/-- A chain model with a bijective comparison square represents `g`. Set
`E k := LinearEquiv.ofBijective (c k).hom (hc k)`, followed by the isomorphism
`induced (homeomorphMap e.symm) k` (whose inverse is `induced (homeomorphMap e) k`,
by functoriality). The square is `hsq`, conjugated by `e`. -/
theorem homologyModels_of_square {X : Type} [TopologicalSpace X] {n : ℕ} (K : GSC n)
    (e : X ≃ₜ K.space) (g : C(X,X)) (M : LefschetzCompactPolyhedron.FiniteChainEndomorphism)
    (c : ∀ k, M.C.homology k ⟶ Homology K.space k)
    (hc : ∀ k, Function.Bijective (c k).hom)
    (hsq : ∀ k, HomologicalComplex.homologyMap M.φ k ≫ c k =
      c k ≫ induced ((homeomorphMap e).comp (g.comp (homeomorphMap e.symm))) k) :
    LefschetzCompactPolyhedron.HomologyModels M g := by
  let F : ℕ → TopCat ⥤ ModuleCat ℚ := fun k =>
    (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)
  have hei (k : ℕ) : Function.Bijective (induced (homeomorphMap e.symm) k).hom := by
    apply Function.bijective_iff_has_inverse.mpr
    refine ⟨(induced (homeomorphMap e) k).hom, ?_, ?_⟩
    · intro x
      have h : induced (homeomorphMap e.symm) k ≫ induced (homeomorphMap e) k = 𝟙 _ := by
        change (F k).map _ ≫ (F k).map _ = _
        rw [← Functor.map_comp]
        rw [show TopCat.ofHom (homeomorphMap e.symm) ≫ TopCat.ofHom (homeomorphMap e) = 𝟙 _ by
          apply TopCat.hom_ext
          apply ContinuousMap.ext
          intro y
          exact e.apply_symm_apply y]
        exact (F k).map_id _
      exact congrArg (fun q => q.hom x) h
    · intro x
      have h : induced (homeomorphMap e) k ≫ induced (homeomorphMap e.symm) k = 𝟙 _ := by
        change (F k).map _ ≫ (F k).map _ = _
        rw [← Functor.map_comp]
        rw [show TopCat.ofHom (homeomorphMap e) ≫ TopCat.ofHom (homeomorphMap e.symm) = 𝟙 _ by
          apply TopCat.hom_ext
          apply ContinuousMap.ext
          intro y
          exact e.symm_apply_apply y]
        exact (F k).map_id _
      exact congrArg (fun q => q.hom x) h
  let E : ∀ k, M.C.homology k ≃ₗ[ℚ] Homology X k := fun k =>
    (LinearEquiv.ofBijective (c k).hom (hc k)).trans
      (LinearEquiv.ofBijective (induced (homeomorphMap e.symm) k).hom (hei k))
  refine ⟨E, fun k => ?_⟩
  apply LinearMap.ext
  intro x
  have hs := congrArg (fun q => q.hom x) (hsq k)
  change (c k).hom ((HomologicalComplex.homologyMap M.φ k).hom x) =
    (induced ((homeomorphMap e).comp (g.comp (homeomorphMap e.symm))) k).hom
      ((c k).hom x) at hs
  change (induced (homeomorphMap e.symm) k).hom
      ((c k).hom ((HomologicalComplex.homologyMap M.φ k).hom x)) =
    (induced g k).hom ((induced (homeomorphMap e.symm) k).hom ((c k).hom x))
  rw [hs]
  change (induced (homeomorphMap e.symm) k).hom
      ((induced ((homeomorphMap e).comp (g.comp (homeomorphMap e.symm))) k).hom
        ((c k).hom x)) =
    (induced g k).hom ((induced (homeomorphMap e.symm) k).hom ((c k).hom x))
  have hnat :
      induced ((homeomorphMap e).comp (g.comp (homeomorphMap e.symm))) k ≫
          induced (homeomorphMap e.symm) k =
        induced (homeomorphMap e.symm) k ≫ induced g k := by
    change (F k).map _ ≫ (F k).map _ = (F k).map _ ≫ (F k).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg (F k).map
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    exact e.symm_apply_apply (g (e.symm y))
  exact congrArg (fun q => q.hom ((c k).hom x)) hnat

/-- LIBRARY: assemble explicit commuting subdivision and vertex maps, their
comparison squares and quasi-isomorphism into the packaged finite chain model. -/
theorem oriented_model_of_explicit_maps
    {X : Type} [TopologicalSpace X] {n : ℕ} (K K' : GSC n)
    (m : ℕ) (hiter : K' = (barycentricStep^[m]) K)
    (hK : K.faces.Finite) (hK' : K'.faces.Finite) (hspace : K'.space = K.space)
    (e : X ≃ₜ K.space) (g : C(X,X)) (h : Euc n → Euc n)
    (hh : GeometricSimplicialSubdivision.IsSimplicialVertexMap K' K h)
    (havoid : CarrierAvoidingVertexMap K K' h)
    (f : C(K'.space, K.space))
    (hf : ∀ s ∈ K'.faces, ∀ x : K'.space,
      (x : Euc n) ∈ convexHull ℝ (s : Set _) →
      (f x : Euc n) ∈ convexHull ℝ (s.image h : Set _))
    (hhom : ContinuousMap.Homotopic
      ((homeomorphMap e).comp
        (g.comp ((homeomorphMap e.symm).comp
          (homeomorphMap (Homeomorph.setCongr hspace : K'.space ≃ₜ K.space))))) f) :
    ∃ M : LefschetzCompactPolyhedron.FiniteChainEndomorphism,
      (∀ k, M.chainTrace k = 0) ∧ LefschetzCompactPolyhedron.HomologyModels M g := by
  classical
  let o : LinearOrder (Euc n) := IsWellOrder.linearOrder WellOrderingRel
  subst hiter
  obtain ⟨dK, hdK, hddK, cmpK, hcmpK, cmpKH, cmpKH_f⟩ := orientedPackage_exists o K
  obtain ⟨dK', hdK', hddK', cmpK', hcmpK', cmpK'H, cmpK'H_f⟩ :=
    orientedPackage_exists o ((barycentricStep^[m]) K)
  obtain ⟨sdH, hcarr, hsd⟩ := iterSubdivision_square o m K dK dK' hdK hdK' hddK hddK'
    cmpK cmpK' hcmpK hcmpK' cmpKH cmpK'H cmpKH_f cmpK'H_f
  obtain ⟨hmH, hvert, hv⟩ := vertexChainMap_square_package o _ K h hh f hf dK' dK
    hdK' hdK hddK' hddK cmpK' cmpK hcmpK' hcmpK cmpK'H cmpKH cmpK'H_f cmpKH_f
  obtain ⟨b, hb⟩ := faceModule_zero_above K hK
  let M : LefschetzCompactPolyhedron.FiniteChainEndomorphism :=
    { C := ChainComplex.of _ dK hddK
      φ := sdH ≫ hmH
      bound := b
      finiteChain := faceModule_finiteDimensional K hK
      finiteHomology := orientedChains_homology_finiteDimensional K hK dK hddK
      chainAbove := hb }
  refine ⟨M, fun k ↦ ?_, ?_⟩
  · exact faceModule_trace_eq_zero K hK k ((sdH ≫ hmH).f k)
      (composite_zero_diagonal_of_isHullCarried o K _ h (fun k ↦ sdH.f k) (fun k ↦ hmH.f k)
        hcarr hvert havoid k)
  · exact homologyModels_of_square K e g M (fun k ↦ HomologicalComplex.homologyMap cmpKH k)
      (orientedPackage_homology_bijective o K hK dK hdK hddK cmpK hcmpK cmpKH cmpKH_f)
      (oriented_model_aux_conj K _ hspace e g f sdH hmH cmpKH cmpK'H hsd hv hhom)

/-- Adapter with exactly the statement consumed by `LefschetzCompactPolyhedron`. -/
theorem exists_carrier_avoiding_oriented_chain_model
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (e : X ≃ₜ K.space) (g : C(X, X))
    (δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ s ∈ K.faces, ∀ x : X,
      (e x : EuclideanSpace ℝ (Fin n)) ∈ convexHull ℝ (s : Set _) →
      ∀ y ∈ convexHull ℝ (s : Set _),
        δ ≤ dist (e (g x) : EuclideanSpace ℝ (Fin n)) y) :
    ∃ M : LefschetzCompactPolyhedron.FiniteChainEndomorphism,
      (∀ k, M.chainTrace k = 0) ∧
        LefschetzCompactPolyhedron.HomologyModels M g := by
  obtain ⟨p, m, hL, hLfin, hspace, hK', h, hh, hav, hstar⟩ :=
    exists_fine_iterated_approximation K hK e g δ hδ hmargin
  let L := (barycentricStep^[p]) K
  let K' := (barycentricStep^[m]) L
  let eL : X ≃ₜ L.space := e.trans (Homeomorph.setCongr hL.symm)
  obtain ⟨f, _hvertex, hf⟩ :=
    GeometricSimplicialSubdivision.exists_inducedContinuousMap K' hK' L h hh
  exact oriented_model_of_explicit_maps L K' m rfl hLfin hK' hspace eL g h hh hav f hf
    (GeometricSimplicialSubdivision.inducedMap_homotopic_of_star_condition
      K' L _ f h hstar hf)
end ConstructionTargets.SimplicialChainMaps

#print axioms ConstructionTargets.SimplicialChainMaps.exists_carrier_avoiding_oriented_chain_model
