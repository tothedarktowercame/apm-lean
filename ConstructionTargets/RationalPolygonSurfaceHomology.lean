import Mathlib
import ConstructionTargets.Surfaces
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.SurfaceGroupBetti
import ConstructionTargets.PolygonSurfaceHomology

/-! # Rational homology of polygon surfaces

Banked verbatim from the closed t98A01 blueprint (claude-14, 2026-10-28):
rational homology from integral homology by extension of scalars (`ratUC_*`),
and the boundary ranks of the standard pairing data (`polygonNF_*`).  Used by
`ProjectivePlaneWedgeRationalHomology`. -/

open ConstructionTargets.Surfaces

noncomputable section

open CategoryTheory
open ConstructionTargets ConstructionTargets.SurfaceGroupBetti
open ConstructionTargets.PolygonSurfacePiOne ConstructionTargets.PolygonSurfaceHomology
open ConstructionTargets.RationalLefschetz

namespace ConstructionTargets.RationalPolygonSurfaceHomology

/-! ## (b) Rational homology from integral homology (universal coefficients)

`HasEulerCharacteristic` uses rational singular homology.  The banked polygon
homology (`PolygonSurfaceHomology.polygonQuotient_homology`) is integral.  The
three leaves below pass from `ℤ` to `ℚ` by extension of scalars.  They are
general homological algebra, not polygon-specific, and serve every rational
Euler-characteristic consumer. -/

/-- Extension of scalars `ℤ → ℚ` on module categories. -/
abbrev ratUC_F : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ :=
  ModuleCat.extendScalars (algebraMap ℤ ℚ)

abbrev ratUC_chainsZ (X : TopCat.{0}) : ChainComplex (ModuleCat ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj X

abbrev ratUC_chainsQ (X : TopCat.{0}) : ChainComplex (ModuleCat ℚ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    (ModuleCat.of ℚ ℚ)).obj X

/-- **Leaf `ratUC_chainIso` (UC i).**  Rational singular chains are the
extension of scalars of integral singular chains.

Route.  Both complexes are `alternatingFaceMapComplex` of the simplicial
object `n ↦ ∐_{σ : SingularSimplex X n} R`
(`SSet.singularChainComplexFunctor`).  `AlgebraicTopology.map_alternatingFaceMapComplex`
commutes `F.mapHomologicalComplex` past `alternatingFaceMapComplex`, so it
suffices to give an iso of simplicial objects
`F ∘ (∐ ℤ) ≅ ∐ ℚ`.  `ratUC_F` is a left adjoint
(`ModuleCat.extendRestrictScalarsAdj`), so it preserves coproducts
(`PreservesCoproduct.iso`), and `F.obj (ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℚ ℚ`
(`TensorProduct.lid`-style).  Naturality in the simplicial index: face maps
are `Sigma.map'` along reindexing, which commute with the coproduct
comparison (`Sigma.hom_ext`).  If `ratUC_F.Additive` is needed it follows from
the adjunction (`Adjunction.left_adjoint_additive`-style, or
`Functor.additive_of_preservesBinaryBiproducts`).  About 100–220 lines. -/
noncomputable def ratUC_chainIso_aux_coeff :
    ratUC_F.obj (ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℚ ℚ :=
  (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toModuleIso

theorem ratUC_chainIso_aux_pres_hom (A : Type) :
    (Limits.PreservesCoproduct.iso ratUC_F
      (fun _ : A => ModuleCat.of ℤ ℤ)).hom =
      inv (Limits.sigmaComparison ratUC_F
        (fun _ : A => ModuleCat.of ℤ ℤ)) := by
  let e := Limits.PreservesCoproduct.iso ratUC_F
    (fun _ : A => ModuleCat.of ℤ ℤ)
  let s := Limits.sigmaComparison ratUC_F
    (fun _ : A => ModuleCat.of ℤ ℤ)
  have h : e.symm = asIso s := Iso.ext (by
    exact Limits.PreservesCoproduct.inv_hom ratUC_F
      (fun _ : A => ModuleCat.of ℤ ℤ))
  exact congrArg Iso.inv h

noncomputable def ratUC_chainIso_aux_sigma :
    (Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ)) ⋙ ratUC_F ≅
      Limits.sigmaConst.obj (ModuleCat.of ℚ ℚ) :=
  NatIso.ofComponents (fun A =>
    Limits.PreservesCoproduct.iso ratUC_F (fun _ : A => ModuleCat.of ℤ ℤ) ≪≫
      Limits.Sigma.mapIso (fun _ : A => ratUC_chainIso_aux_coeff)) (by
        intro A B f
        apply (cancel_epi ((Limits.PreservesCoproduct.iso ratUC_F
          (fun _ : A => ModuleCat.of ℤ ℤ) ≪≫
            Limits.Sigma.mapIso (fun _ : A => ratUC_chainIso_aux_coeff)).inv)).mp
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        apply Limits.Sigma.hom_ext
        intro a
        simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
          Functor.mapIso_hom, Category.assoc]
        erw [Limits.colimit.ι_map_assoc]
        erw [Limits.colimit.ι_map_assoc]
        simp only [Limits.PreservesCoproduct.inv_hom]
        erw [Limits.ι_comp_sigmaComparison_assoc]
        erw [Limits.ι_comp_sigmaComparison_assoc]
        simp only [Functor.comp_map]
        have hm :
            ratUC_F.map (Limits.Sigma.ι (fun _ : A => ModuleCat.of ℤ ℤ) a) ≫
                ratUC_F.map ((Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ)).map f) ≫
                (Limits.PreservesCoproduct.iso ratUC_F
                  (fun _ : B => ModuleCat.of ℤ ℤ)).hom ≫
                (Limits.Sigma.mapIso
                  (fun _ : B => ratUC_chainIso_aux_coeff)).hom =
              ratUC_F.map (Limits.Sigma.ι (fun _ : A => ModuleCat.of ℤ ℤ) a ≫
                (Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ)).map f) ≫
                (Limits.PreservesCoproduct.iso ratUC_F
                  (fun _ : B => ModuleCat.of ℤ ℤ)).hom ≫
                (Limits.Sigma.mapIso
                  (fun _ : B => ratUC_chainIso_aux_coeff)).hom := by
          rw [ratUC_F.map_comp]
          simp only [Category.assoc]
        have hmfull := congrArg (fun k : ratUC_F.obj (ModuleCat.of ℤ ℤ) ⟶
            (Limits.sigmaConst.obj (ModuleCat.of ℚ ℚ)).obj B =>
          ratUC_chainIso_aux_coeff.inv ≫ k) hm
        simp only [Category.assoc, Functor.mapIso_hom] at hmfull
        change ratUC_chainIso_aux_coeff.inv ≫ _ =
          ratUC_chainIso_aux_coeff.inv ≫ _
        refine hmfull.trans ?_
        dsimp only [Limits.sigmaConst]
        rw [Limits.Sigma.ι_comp_map']
        simp only [Category.id_comp]
        rw [ratUC_chainIso_aux_pres_hom, ratUC_chainIso_aux_pres_hom]
        erw [Limits.map_ι_comp_inv_sigmaComparison_assoc]
        erw [Limits.map_ι_comp_inv_sigmaComparison_assoc]
        erw [Limits.ι_colimMap_assoc]
        let α : Discrete.functor (fun _ : B => ratUC_F.obj (ModuleCat.of ℤ ℤ)) ≅
            Discrete.functor (fun _ : B => ModuleCat.of ℚ ℚ) :=
          Discrete.natIso (fun _ => ratUC_chainIso_aux_coeff)
        have hc := Limits.colimit.ι_map α.hom ⟨f a⟩
        have hcfull := congrArg (fun k : ratUC_F.obj (ModuleCat.of ℤ ℤ) ⟶
            (Limits.sigmaConst.obj (ModuleCat.of ℚ ℚ)).obj B =>
          ratUC_chainIso_aux_coeff.inv ≫ k) hc
        refine hcfull.trans ?_
        dsimp [α]
        simp [Category.assoc, ratUC_chainIso_aux_coeff])

theorem ratUC_chainIso (X : TopCat.{0}) :
    Nonempty ((ratUC_F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (ratUC_chainsZ X) ≅ ratUC_chainsQ X) := by
  letI : ratUC_F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap ℤ ℚ)).left_adjoint_additive
  let S := (TopCat.toSSet.obj X)
  let SZ : SimplicialObject (ModuleCat ℤ) :=
    ((SimplicialObject.whiskering (Type 0) (ModuleCat ℤ)).obj
      (Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ))).obj S
  let e :
      ((SimplicialObject.whiskering (ModuleCat ℤ) (ModuleCat ℚ)).obj ratUC_F).obj
          (((SimplicialObject.whiskering (Type 0) (ModuleCat ℤ)).obj
            (Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ))).obj S) ≅
        (((SimplicialObject.whiskering (Type 0) (ModuleCat ℚ)).obj
            (Limits.sigmaConst.obj (ModuleCat.of ℚ ℚ))).obj S) :=
    ((SimplicialObject.whiskering (Type 0) (ModuleCat ℚ)).mapIso
      ratUC_chainIso_aux_sigma).app S
  refine ⟨?_⟩
  dsimp [ratUC_chainsZ, ratUC_chainsQ,
    AlgebraicTopology.singularChainComplexFunctor,
    AlgebraicTopology.SSet.singularChainComplexFunctor]
  exact (eqToIso (Functor.congr_obj
      (AlgebraicTopology.map_alternatingFaceMapComplex ratUC_F) SZ)) ≪≫
    (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℚ)).mapIso e

/-- **Leaf `ratUC_homologyIso` (UC ii).**  Extension of scalars to `ℚ`
commutes with homology of any chain complex of abelian groups.

Route.  `ℚ` is a flat `ℤ`-module (`Module.Flat` of a localization, or
torsion-free over a PID), so `ratUC_F` is exact.  An exact functor between
abelian categories preserves homology
(`Functor.preservesHomology_of_map_exact` in
`Mathlib/CategoryTheory/Abelian/Exact.lean`).  Then
`ShortComplex.mapHomologyIso` applied to `K.sc k` gives the iso, since
`((F.mapHomologicalComplex _).obj K).sc k = (K.sc k).map F` up to `Iso.refl`.
About 60–150 lines. -/
theorem ratUC_homologyIso (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (k : ℕ) :
    Nonempty (((ratUC_F.mapHomologicalComplex _).obj K).homology k ≅
      ratUC_F.obj (K.homology k)) := by
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap ℤ ℚ)
  letI : ratUC_F.Additive := adj.left_adjoint_additive
  have hflat : (algebraMap ℤ ℚ).Flat := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  letI : Limits.PreservesFiniteLimits ratUC_F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  letI : Limits.PreservesFiniteColimits ratUC_F :=
    (Adjunction.leftAdjoint_preservesColimits.{0, 0} adj).preservesFiniteColimits
  letI : ratUC_F.PreservesHomology := by
    apply ((Functor.exact_tfae ratUC_F).out 3 2).mp
    exact And.intro (by infer_instance) (by infer_instance)
  exact ⟨(K.sc k).mapHomologyIso ratUC_F⟩

/-- **Leaf `ratUC_finrank` (UC iii).**  For a finitely generated abelian group
`M`, `ℚ ⊗ M` is finite dimensional of dimension `finrank ℤ M`.

Route.  `ratUC_F.obj M` is `ℚ ⊗[ℤ] M` (`ModuleCat.ExtendScalars.obj'`).
Finite: `Module.Finite.base_change`.  Rank: write `M ≃ ℤ^r × T` with `T`
finite (`Module.equiv_free_prod_directSum`, structure theorem over a PID);
`ℚ ⊗ T = 0` because `T` is torsion; `ℚ ⊗ ℤ^r ≅ ℚ^r`
(`Module.finrank_baseChange`).  `Module.finrank ℤ M = r` because torsion has
rank zero over a domain.  Alternatively `IsLocalizedModule` with
`Module.finrank_of_isLocalizedModule_of_free`-style lemmas.  Degenerate case
`M = 0`: both sides are `0`.  About 60–150 lines. -/
theorem ratUC_finrank (M : Type) [AddCommGroup M] [Module.Finite ℤ M] :
    FiniteDimensional ℚ (ratUC_F.obj (ModuleCat.of ℤ M)) ∧
      Module.finrank ℚ (ratUC_F.obj (ModuleCat.of ℤ M)) = Module.finrank ℤ M := by
  change Module.Finite ℚ (TensorProduct ℤ ℚ M) ∧
    Module.finrank ℚ (TensorProduct ℤ ℚ M) = Module.finrank ℤ M
  constructor
  · infer_instance
  · exact (TensorProduct.isBaseChange (R := ℤ) (M := M) (S := ℚ)).finrank_eq

/-- Layer 2 (uses UC i–iii): rational homology rank from an integral
computation. -/
theorem ratUC_rationalHomology_finrank (X : Type) [TopologicalSpace X] (k : ℕ)
    (M : Type) [AddCommGroup M] [Module.Finite ℤ M]
    (e : SpaceH X k ≅ ModuleCat.of ℤ M) :
    FiniteDimensional ℚ (Homology X k) ∧
      Module.finrank ℚ (Homology X k) = Module.finrank ℤ M := by
  obtain ⟨c⟩ := ratUC_chainIso (TopCat.of X)
  obtain ⟨h⟩ := ratUC_homologyIso (ratUC_chainsZ (TopCat.of X)) k
  have i : Homology X k ≅ ratUC_F.obj (ModuleCat.of ℤ M) :=
    (HomologicalComplex.homologyFunctor _ _ k).mapIso c.symm ≪≫ h ≪≫ ratUC_F.mapIso e
  let l := i.toLinearEquiv
  obtain ⟨hfd, hr⟩ := ratUC_finrank M
  exact ⟨LinearEquiv.finiteDimensional l.symm, l.finrank_eq.trans hr⟩

/-! ## (b) Euler characteristic of the standard surfaces (`polygonNF_*` family) -/

/-- The identity acts on rational homology with trace equal to its rank. -/
theorem polygonNF_trace_induced_id (X : Type) [TopologicalSpace X] (k : ℕ)
    [FiniteDimensional ℚ (Homology X k)] :
    LinearMap.trace ℚ (Homology X k) (induced (ContinuousMap.id X) k).hom =
      Module.finrank ℚ (Homology X k) := by
  have h : induced (ContinuousMap.id X) k = 𝟙 _ := by
    simp only [induced]
    exact CategoryTheory.Functor.map_id _ _
  rw [h, ModuleCat.hom_id, LinearMap.trace_id]

/-- `HasEulerCharacteristic` from finite ranks: the trace of the identity is
the rank. -/
theorem polygonNF_hasEulerCharacteristic_of_finrank (X : Type) [TopologicalSpace X]
    (hfd : ∀ k, FiniteDimensional ℚ (Homology X k)) (bound : ℕ)
    (hz : ∀ k, bound < k → Module.finrank ℚ (Homology X k) = 0) (v : ℚ)
    (hv : ∑ k ∈ Finset.range (bound + 1),
      (-1 : ℚ) ^ k * (Module.finrank ℚ (Homology X k) : ℚ) = v) :
    HasEulerCharacteristic X v := by
  refine ⟨hfd, bound, fun k hk => ?_, ?_⟩
  · haveI := hfd k
    exact Module.finrank_zero_iff.mp (hz k hk)
  · rw [← hv]
    refine Finset.sum_congr rfl fun k _ => ?_
    haveI := hfd k
    rw [polygonNF_trace_induced_id]

/-- `HasEulerCharacteristic` is a homeomorphism invariant. -/
theorem polygonNF_hasEulerCharacteristic_of_homeomorph {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {v : ℚ}
    (h : HasEulerCharacteristic Y v) : HasEulerCharacteristic X v := by
  obtain ⟨hfd, bound, hsub, hv⟩ := h
  let l : ∀ k, Homology X k ≃ₗ[ℚ] Homology Y k := fun k =>
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).mapIso (TopCat.isoOfHomeo e)).toLinearEquiv
  have hfdX : ∀ k, FiniteDimensional ℚ (Homology X k) := fun k => by
    haveI := hfd k
    exact LinearEquiv.finiteDimensional (l k).symm
  refine polygonNF_hasEulerCharacteristic_of_finrank X hfdX bound (fun k hk => ?_) v ?_
  · haveI := hsub k hk
    rw [(l k).finrank_eq]
    exact Module.finrank_zero_of_subsingleton
  · rw [← hv]
    refine Finset.sum_congr rfl fun k _ => ?_
    haveI := hfd k
    rw [polygonNF_trace_induced_id, (l k).finrank_eq]

/-- **Family leaf `polygonNF_standard_boundary_ranks`** (t98A01 here; later
any χ consumer).  Integral ranks of the cellular boundary `ℤ → ℤ^{edges}` of
the standard pairing data.  Orientable: the degree is `0` (each handle orbit
has one `true` and one `false` edge, `handleSign`), so the kernel is `ℤ` and
the cokernel is `ℤ^{2g}`.  Nonorientable: the degree is `-2` on every orbit
(banked `SurfaceGroupBetti.standard_nonorientable_data_aux_degree`), so the
kernel is `0` and the cokernel has rank `g - 1`.

Route.  Orbit counts: `orientableOrbitEquiv`, `nonorientableOrbitEquiv`
(both banked).  Orientable: show `attachingDegree = 0` as in
`standard_nonorientable_data_aux_degree` (sum over `orientableCoord`), then
`attachingBoundary = 0`, `ker = ⊤ ≅ ℤ`, cokernel `≅ (Fin g × Bool → ℤ)`.
Nonorientable: `n • d = 0 → n = 0` for `d ≠ 0` gives `ker = ⊥`; the cokernel
of the span of one nonzero vector in `ℤ^g` has rank `g - 1`
(`Submodule.finrank_quotient_add_finrank` over `ℤ`, or pass to `ℚ`).
`Module.Finite` of a quotient of `Fin`-indexed functions is
`Module.Finite.quotient`.  About 80–200 lines. -/
lemma polygonNF_standard_boundary_ranks_aux_orientable_orbit (g : ℕ) (hg : 0 < g)
    (i : Fin (4 * g)) (j : Fin g × Bool) :
    (standardPairingData true g hg).orbit i =
        (orientableOrbitEquiv g).symm j ↔
      orientableOrbitLabel g i = j := by
  change Quotient.mk _ i = (orientableOrbitEquiv g).symm j ↔ _
  constructor
  · intro h
    have h' := congrArg (orientableOrbitEquiv g) h
    simpa using h'
  · intro h
    apply (orientableOrbitEquiv g).injective
    simpa using h

lemma polygonNF_standard_boundary_ranks_aux_orientable_degree (g : ℕ) (hg : 0 < g) :
    attachingDegree (standardPairingData true g hg) = 0 := by
  funext j
  rw [attachingDegree_apply]
  calc
    _ = ∑ p : Fin g × Fin 4,
        edgeOrbitContribution (standardPairingData true g hg)
          ((orientableCoord g).symm p) j :=
      ((orientableCoord g).symm.sum_comp fun i ↦
        edgeOrbitContribution (standardPairingData true g hg) i j).symm
    _ = 0 := by
      simp only [edgeOrbitContribution]
      generalize hj : (orientableOrbitEquiv g) j = q
      have ej : j = (orientableOrbitEquiv g).symm q := by
        rw [← hj]
        exact (orientableOrbitEquiv g).symm_apply_apply j |>.symm
      subst j
      rcases q with ⟨a, b⟩
      cases b
      · simp_rw [polygonNF_standard_boundary_ranks_aux_orientable_orbit]
        simp [standardPairingData, orientableStandardPairingData,
          standardPairingDataOfOneVertex, standardPair, standardSign,
          orientableOrbitLabel, handleOrbitLabel, edgeAttachingDegree,
          Fintype.sum_prod_type]
        rw [Fintype.sum_eq_single a]
        · simp [Fin.sum_univ_four, handleOrbitLabel, handleSign]
        · intro b hb
          simp [hb]
      · simp_rw [polygonNF_standard_boundary_ranks_aux_orientable_orbit]
        simp [standardPairingData, orientableStandardPairingData,
          standardPairingDataOfOneVertex, standardPair, standardSign,
          orientableOrbitLabel, handleOrbitLabel, edgeAttachingDegree,
          Fintype.sum_prod_type]
        rw [Fintype.sum_eq_single a]
        · simp [Fin.sum_univ_four, handleOrbitLabel, handleSign]
        · intro b hb
          simp [hb]

theorem polygonNF_standard_boundary_ranks (o : Bool) (g : ℕ) (hg : 0 < g) :
    Module.Finite ℤ (BoundaryCokernel (standardPairingData o g hg)) ∧
      Module.finrank ℤ (BoundaryCokernel (standardPairingData o g hg)) =
        (if o then 2 * g else g - 1) ∧
      Module.finrank ℤ (BoundaryKernel (standardPairingData o g hg)) =
        (if o then 1 else 0) := by
  cases o with
  | false =>
      let P := standardPairingData false g hg
      have hfin : Module.Finite ℤ (BoundaryCokernel P) :=
        Module.Finite.quotient ℤ (LinearMap.range (attachingBoundary P))
      have hinj : Function.Injective (attachingBoundary P) := by
        intro n m hnm
        have hcoord := congrFun hnm ((nonorientableOrbitEquiv g).symm ⟨0, hg⟩)
        change n * attachingDegree P ((nonorientableOrbitEquiv g).symm ⟨0, hg⟩) =
          m * attachingDegree P ((nonorientableOrbitEquiv g).symm ⟨0, hg⟩) at hcoord
        rw [standard_nonorientable_data_aux_degree] at hcoord
        exact mul_right_cancel₀ (by norm_num : (-2 : ℤ) ≠ 0) hcoord
      have hker : LinearMap.ker (attachingBoundary P) = ⊥ :=
        LinearMap.ker_eq_bot.mpr hinj
      have hrange : Module.finrank ℤ (LinearMap.range (attachingBoundary P)) = 1 := by
        rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_self]
      have hamb : Module.finrank ℤ (PairingOrbit P.pair → ℤ) = g := by
        letI := Fintype.ofFinite (PairingOrbit P.pair)
        rw [Module.finrank_fintype_fun_eq_card]
        rw [Fintype.card_eq_nat_card]
        change Nat.card (PairingOrbit (nonorientablePair g)) = g
        simpa using Nat.card_congr (nonorientableOrbitEquiv g)
      have hquot : Module.finrank ℤ (BoundaryCokernel P) +
          Module.finrank ℤ (LinearMap.range (attachingBoundary P)) =
          Module.finrank ℤ (PairingOrbit P.pair → ℤ) :=
        Submodule.finrank_quotient_add_finrank _
      refine ⟨hfin, ?_, ?_⟩
      · change Module.finrank ℤ (BoundaryCokernel P) = g - 1
        rw [hrange, hamb] at hquot
        omega
      · change Module.finrank ℤ (LinearMap.ker (attachingBoundary P)) = 0
        rw [hker, finrank_bot]
  | true =>
      let P := standardPairingData true g hg
      have hdeg : attachingDegree P = 0 :=
        polygonNF_standard_boundary_ranks_aux_orientable_degree g hg
      have hboundary : attachingBoundary P = 0 := by
        apply LinearMap.ext
        intro n
        simp [attachingBoundary_apply, hdeg]
      have hfin : Module.Finite ℤ (BoundaryCokernel P) :=
        Module.Finite.quotient ℤ (LinearMap.range (attachingBoundary P))
      have hamb : Module.finrank ℤ (PairingOrbit P.pair → ℤ) = 2 * g := by
        letI := Fintype.ofFinite (PairingOrbit P.pair)
        rw [Module.finrank_fintype_fun_eq_card]
        rw [Fintype.card_eq_nat_card]
        change Nat.card (PairingOrbit (orientablePair g)) = 2 * g
        rw [Nat.card_congr (orientableOrbitEquiv g), Nat.card_prod,
          Nat.card_fin]
        have hb : Nat.card Bool = 2 := by
          rw [Nat.card_eq_fintype_card, Fintype.card_bool]
        rw [hb]
        omega
      have hquot : Module.finrank ℤ (BoundaryCokernel P) +
          Module.finrank ℤ (LinearMap.range (attachingBoundary P)) =
          Module.finrank ℤ (PairingOrbit P.pair → ℤ) :=
        Submodule.finrank_quotient_add_finrank _
      refine ⟨hfin, ?_, ?_⟩
      · change Module.finrank ℤ (BoundaryCokernel P) = 2 * g
        have hr : LinearMap.range (attachingBoundary P) = ⊥ := by
          rw [hboundary, LinearMap.range_zero]
        have hrank : Module.finrank ℤ (LinearMap.range (attachingBoundary P)) = 0 := by
          rw [hr, finrank_bot]
        rw [hrank, hamb] at hquot
        omega
      · change Module.finrank ℤ (LinearMap.ker (attachingBoundary P)) = 1
        rw [hboundary, LinearMap.ker_zero, finrank_top, Module.finrank_self]


end ConstructionTargets.RationalPolygonSurfaceHomology
