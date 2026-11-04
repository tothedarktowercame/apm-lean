import Mathlib
import ConstructionTargets.SingularHomologyHomotopy
import ConstructionTargets.CoefficientRadialPair
import ConstructionTargets.CoefficientPairNaturality
import ConstructionTargets.CoefficientExcision
import ConstructionTargets.CoefficientCompactComplementTransportedExactness
import ConstructionTargets.CoefficientSubcomplexRelativeHomologySequence
import ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso
import ConstructionTargets.CoefficientModelLocal
import ConstructionTargets.CoefficientManifoldLocalComparison
import ConstructionTargets.CollaredConnectedSumHomology

open scoped ContDiff Manifold
open CategoryTheory
open CategoryTheory.Limits

universe u

/-- Mod-2 singular homology, with an `ULift` coefficient module so that the
construction remains available for spaces in an arbitrary universe. -/
abbrev t00A04_ModTwoHomology (n : ℕ) (X : Type u) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} (ZMod 2)) n).obj
      (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).obj (TopCat.of X) : Type u)

/-- Relative mod-2 singular homology `H_n(X, X \ A)`, for the Type-0
coefficient-relative API used by the compact-complement Mayer--Vietoris code. -/
abbrev t00A04_ModTwoLocalHomology (X : Type) [TopologicalSpace X]
    (A : Set X) (n : ℕ) :=
  ((ConstructionTargets.CoefficientRelativeSmall.relativeChains
      (ZMod 2) Aᶜ).homology n : Type)

/-- Restriction from support in `A` to local homology at `x ∈ A`. -/
noncomputable def t00A04_modTwo_pointRestriction
    (X : Type) [TopologicalSpace X] (A : Set X) (x : X) (hx : x ∈ A) (n : ℕ) :=
  HomologicalComplex.homologyMap
    (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Aᶜ ({x} : Set X)ᶜ
      (ContinuousMap.id X) (by
        intro y hy
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq] using
          fun (hxy : y = x) ↦ hy (hxy ▸ hx))) n

/-- Restriction from support in `K` to support in a smaller set `A ⊆ K`:
the map `H_n(X, X \ K) → H_n(X, X \ A)` induced by the identity of `X`. -/
noncomputable def t00A04_modTwo_restrict
    (X : Type) [TopologicalSpace X] (A K : Set X) (h : A ⊆ K) (n : ℕ) :=
  HomologicalComplex.homologyMap
    (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Kᶜ Aᶜ
      (ContinuousMap.id X) (fun _ hy hyA ↦ hy (h hyA))) n

/-- The usable conclusion of Hatcher 3.27 for a compact support `A`. -/
structure t00A04_HatcherConclusion
    (X : Type) [TopologicalSpace X] (d : ℕ) (A : Set X) : Prop where
  vanish_above : ∀ i, d < i → Subsingleton (t00A04_ModTwoLocalHomology X A i)
  exists_everywhere_nonzero : ∃ c : t00A04_ModTwoLocalHomology X A d,
    ∀ (x : X) (hx : x ∈ A), t00A04_modTwo_pointRestriction X A x hx d c ≠ 0
  eq_zero_iff_pointwise : ∀ c : t00A04_ModTwoLocalHomology X A d,
    c = 0 ↔ ∀ (x : X) (hx : x ∈ A),
      t00A04_modTwo_pointRestriction X A x hx d c = 0

/-! # APM t00A04 — a retract inclusion is not null-homotopic -/

def apm_t00a04_NullHomotopic {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) : Prop :=
  ∃ (y : Y) (H : X × ℝ → Y), Continuous H ∧
    (∀ x, H (x, 0) = f x) ∧ ∀ x, H (x, 1) = y

/-- A zero-dimensional real normed space is a singleton. -/
theorem t00A04_model_subsingleton_of_finrank_zero
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 0) :
    Subsingleton E := by
  refine ⟨fun x y ↦ ?_⟩
  rw [finrank_zero_iff_forall_zero.mp hdim x,
    finrank_zero_iff_forall_zero.mp hdim y]

/-- A manifold modelled on a singleton has the discrete topology.  The
`Subsingleton E` conclusion is passed in explicitly so this leaf is independent
of the preceding linear-algebra leaf. -/
theorem t00A04_manifold_discrete_of_model_subsingleton
    (E X : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : ModelWithCorners ℝ E E) [Subsingleton E]
    [TopologicalSpace X] [ChartedSpace E X] [IsManifold I ∞ X] :
    DiscreteTopology X := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  have hsource : (chartAt E x).source = ({x} : Set X) := by
    ext y
    constructor
    · intro hy
      have hxy : chartAt E x y = chartAt E x x := Subsingleton.elim _ _
      have hx : x ∈ (chartAt E x).source := mem_chart_source E x
      have := congrArg (chartAt E x).symm hxy
      simpa [(chartAt E x).left_inv hy, (chartAt E x).left_inv hx] using this
    · intro hy
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact mem_chart_source E x
  rw [← hsource]
  exact (chartAt E x).open_source

/-- A continuous real-parameter homotopy cannot move a point in a discrete
space.  Thus a null-homotopic identity on a discrete space forces the space to
be a singleton. -/
theorem t00A04_discrete_nullhomotopic_identity_subsingleton
    (X : Type*) [TopologicalSpace X] [DiscreteTopology X]
    (hnull : apm_t00a04_NullHomotopic (fun x : X => x)) :
    Subsingleton X := by
  rcases hnull with ⟨y, H, hH, hH0, hH1⟩
  constructor
  intro x x'
  have hx : x = y := by
    have hpath : Continuous (fun t : ℝ ↦ H (x, t)) :=
      hH.comp (Continuous.prodMk_right x)
    have hend : H (x, 0) = H (x, 1) :=
      TotallyDisconnectedSpace.eq_of_continuous _ hpath 0 1
    simpa only [hH0 x, hH1 x] using hend
  have hx' : x' = y := by
    have hpath : Continuous (fun t : ℝ ↦ H (x', t)) :=
      hH.comp (Continuous.prodMk_right x')
    have hend : H (x', 0) = H (x', 1) :=
      TotallyDisconnectedSpace.eq_of_continuous _ hpath 0 1
    simpa only [hH0 x', hH1 x'] using hend
  exact hx.trans hx'.symm

/-- A nontrivial type is not a subsingleton. -/
theorem t00A04_nontrivial_not_subsingleton
    (X : Type*) [Nontrivial X] : ¬ Subsingleton X := by
  exact not_subsingleton_iff_nontrivial.mpr inferInstance

/-- **LIBRARY (invariance of domain).**  A finite-dimensional self-model has
no manifold boundary: its model map has open range. -/
theorem t00A04_boundarylessManifold_of_finiteDimensional_selfModel_aux_openRange
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E) :
    IsOpen (Set.range I) := by
  let d := Module.finrank ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [d])
  let g : ↑(Set.univ : Set (EuclideanSpace ℝ (Fin d))) →
      EuclideanSpace ℝ (Fin d) := fun x ↦ e (I (e.symm x))
  have hg : Continuous g := by
    simpa only [g, Function.comp_apply] using
      e.continuous.comp (I.continuous.comp
        (e.symm.continuous.comp continuous_subtype_val))
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    exact e.symm.injective (I.injective (e.injective hxy))
  have hopen_g : IsOpenMap g :=
    ConstructionTargets.CollaredConnectedSumHomology.BallCollar.largeInterior_isOpen_aux_euclidean_aux_open
      d
      (fun hf hinj ↦
        ConstructionTargets.CollaredConnectedSumHomology.BallCollar.largeInterior_isOpen_aux_euclidean_aux_interior d
          (fun hg' ↦
            ConstructionTargets.CollaredConnectedSumHomology.BallCollar.largeInterior_isOpen_aux_euclidean_aux_brouwer
              d
              ConstructionTargets.CollaredConnectedSumHomology.BallCollar.largeInterior_isOpen_aux_euclidean_aux_noRetraction
              hg')
          hf hinj)
      isOpen_univ hg hginj
  have hrange_g : IsOpen (Set.range g) := hopen_g.isOpen_range
  have hrange : Set.range g = e '' Set.range I := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨I (e.symm x), ⟨e.symm x, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨⟨e x, Set.mem_univ _⟩, by simp [g]⟩
  have hopen_image : IsOpen (e '' Set.range I) := hrange ▸ hrange_g
  have hpreimage : e ⁻¹' (e '' Set.range I) = Set.range I := by
    exact Set.preimage_image_eq _ e.injective
  rw [← hpreimage]
  exact hopen_image.preimage e.continuous

theorem t00A04_boundarylessManifold_of_finiteDimensional_selfModel
    (E X : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [ChartedSpace E X] [IsManifold I ∞ X] :
    BoundarylessManifold I X := by
  refine ⟨fun x ↦ ?_⟩
  rw [ModelWithCorners.IsInteriorPoint,
    (t00A04_boundarylessManifold_of_finiteDimensional_selfModel_aux_openRange E I).interior_eq]
  exact Set.mem_range_self _

/-- **Relative Mayer--Vietoris, middle term.**  For compact `K, L` in a
Hausdorff space (so `Kᶜ, Lᶜ` are open and the small-chains theorem applies),
classes on `K` and on `L` that agree on `K ∩ L` come from one class on
`K ∪ L`.  (The chain-level sequence with `C((K ∩ L)ᶜ)` in place of
`C(Kᶜ) + C(Lᶜ)` is not exact in the middle; the small-chains comparison is
what makes this true.) -/
noncomputable def t00A04_relativeMV_middle_aux_sumQuotient
    (X : Type) [TopologicalSpace X] (A B : Set X) :=
  cokernel
    (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.unionAmbient
      (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
        (ConstructionTargets.SingularExcision.ambientSubspaceRange B))

theorem t00A04_relativeMV_middle_aux_chain_shortExact
    (X : Type) [TopologicalSpace X] (A B : Set X) :
    (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex.shortComplex
      (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
        (ConstructionTargets.SingularExcision.ambientSubspaceRange B)).ShortExact := by
  exact ConstructionTargets.CoefficientSubcomplexRelativeDegreewiseExact.shortComplex_shortExact
    (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
      (ConstructionTargets.SingularExcision.ambientSubspaceRange B)

theorem t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_inter_left
    (X : Type) [TopologicalSpace X] (A B : Set X) :
    ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToLeftRelative
        (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
          (ConstructionTargets.SingularExcision.ambientSubspaceRange B) ≫
      ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap
        (ZMod 2) A =
    ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap
        (ZMod 2) A B ≫
      ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) (A ∩ B) A
        (ContinuousMap.id X) Set.inter_subset_left := by
  apply (cancel_epi (cokernel.π
    (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionAmbient
      (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
        (ConstructionTargets.SingularExcision.ambientSubspaceRange B)))).1
  rw [← Category.assoc,
    ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex.intersectionToLeftRelative_projection]
  have hrange :
      cokernel.π (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftAmbient
          (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)) ≫
        ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap
          (ZMod 2) A =
      cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2) A) := by
    exact cokernel.π_desc _ _ _
  rw [hrange]
  have hinter :
      cokernel.π
          (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionAmbient
            (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
              (ConstructionTargets.SingularExcision.ambientSubspaceRange B)) ≫
        ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap
          (ZMod 2) A B =
      cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2) (A ∩ B)) := by
    exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)
  rw [← Category.assoc, hinter]
  have h := ConstructionTargets.CoefficientRadialPair.projection (ZMod 2) (A ∩ B) A
    (ContinuousMap.id X) Set.inter_subset_left
  rw [ConstructionTargets.CoefficientPairNaturality.absolute_id, Category.id_comp] at h
  exact h.symm

theorem t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_inter_right
    (X : Type) [TopologicalSpace X] (A B : Set X) :
    ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToRightRelative
        (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
          (ConstructionTargets.SingularExcision.ambientSubspaceRange B) ≫
      ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap
        (ZMod 2) B =
    ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap
        (ZMod 2) A B ≫
      ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) (A ∩ B) B
        (ContinuousMap.id X) Set.inter_subset_right := by
  apply (cancel_epi (cokernel.π
    (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionAmbient
      (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
        (ConstructionTargets.SingularExcision.ambientSubspaceRange B)))).1
  rw [← Category.assoc,
    ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex.intersectionToRightRelative_projection]
  have hrange :
      cokernel.π (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightAmbient
          (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange B)) ≫
        ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap
          (ZMod 2) B =
      cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2) B) := by
    exact cokernel.π_desc _ _ _
  rw [hrange]
  have hinter :
      cokernel.π
          (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionAmbient
            (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
              (ConstructionTargets.SingularExcision.ambientSubspaceRange B)) ≫
        ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap
          (ZMod 2) A B =
      cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2) (A ∩ B)) := by
    exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)
  rw [← Category.assoc, hinter]
  have h := ConstructionTargets.CoefficientRadialPair.projection (ZMod 2) (A ∩ B) B
    (ContinuousMap.id X) Set.inter_subset_right
  rw [ConstructionTargets.CoefficientPairNaturality.absolute_id, Category.id_comp] at h
  exact h.symm

theorem t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_union_left
    (X : Type) [TopologicalSpace X] (A B : Set X) :
    ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftToUnionRelative
          (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange B) ≫
      cokernel.map
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGeneratedAmbientInclusion (ZMod 2) A B)
        (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2) (A ∪ B))
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGeneratedToProduction (ZMod 2) A B)
        (𝟙 _)
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGenerated_relative_square (ZMod 2) A B) =
    ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap (ZMod 2) A ≫
      ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) A (A ∪ B)
        (ContinuousMap.id X) Set.subset_union_left := by
  have hid : ConstructionTargets.CoefficientRadialPair.absoluteMap (ZMod 2)
      (ContinuousMap.id X) = 𝟙 _ := by
    change (ConstructionTargets.CoefficientRadialPair.chains (ZMod 2)).map
      (TopCat.toSSet.map (𝟙 (TopCat.of X))) = _
    simp only [CategoryTheory.Functor.map_id]
  apply (cancel_epi (cokernel.π _)).1
  simp only [ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftToUnionRelative,
    ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap,
    ConstructionTargets.CoefficientRadialPair.pairMap, cokernel.map, cokernel.π_desc_assoc,
    Category.id_comp]
  erw [cokernel.π_desc, cokernel.π_desc_assoc, cokernel.π_desc]
  rw [hid]
  exact (Category.id_comp _).symm

theorem t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_union_right
    (X : Type) [TopologicalSpace X] (A B : Set X) :
    ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightToUnionRelative
          (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange B) ≫
      cokernel.map
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGeneratedAmbientInclusion (ZMod 2) A B)
        (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2) (A ∪ B))
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGeneratedToProduction (ZMod 2) A B)
        (𝟙 _)
        (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.unionGenerated_relative_square (ZMod 2) A B) =
    ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap (ZMod 2) B ≫
      ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) B (A ∪ B)
        (ContinuousMap.id X) Set.subset_union_right := by
  have hid : ConstructionTargets.CoefficientRadialPair.absoluteMap (ZMod 2)
      (ContinuousMap.id X) = 𝟙 _ := by
    change (ConstructionTargets.CoefficientRadialPair.chains (ZMod 2)).map
      (TopCat.toSSet.map (𝟙 (TopCat.of X))) = _
    simp only [CategoryTheory.Functor.map_id]
  apply (cancel_epi (cokernel.π _)).1
  simp only [ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightToUnionRelative,
    ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap,
    ConstructionTargets.CoefficientRadialPair.pairMap, cokernel.map, cokernel.π_desc_assoc,
    Category.id_comp]
  erw [cokernel.π_desc, cokernel.π_desc_assoc, cokernel.π_desc]
  rw [hid]
  exact (Category.id_comp _).symm

theorem t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_inter_homology
    (X : Type) [TopologicalSpace X] (A B : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToLeftRelative
          (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange B)) n ≫
      (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso
        (ZMod 2) A n).hom =
      (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.intersectionRelativeIso
        (ZMod 2) A B n).hom ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) (A ∩ B) A
          (ContinuousMap.id X) Set.inter_subset_left) n ∧
    HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToRightRelative
          (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange B)) n ≫
      (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso
        (ZMod 2) B n).hom =
      (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.intersectionRelativeIso
        (ZMod 2) A B n).hom ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) (A ∩ B) B
          (ContinuousMap.id X) Set.inter_subset_right) n := by
  have hA : (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso (ZMod 2) A n).hom =
      HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap (ZMod 2) A) n := rfl
  have hB : (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso (ZMod 2) B n).hom =
      HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap (ZMod 2) B) n := rfl
  have hI : (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.intersectionRelativeIso (ZMod 2) A B n).hom =
      HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.intersectionRelativeCokernelMap (ZMod 2) A B) n := rfl
  rw [hA, hB, hI]
  constructor
  · have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n) (t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_inter_left X A B)
    simp only [HomologicalComplex.homologyMap_comp] at h
    exact h
  · have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n) (t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_inter_right X A B)
    simp only [HomologicalComplex.homologyMap_comp] at h
    exact h

theorem t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_union_homology
    (X : Type) [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftToUnionRelative
          (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange B)) n ≫
      (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso
        (ZMod 2) A B hA hB n).hom =
      (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso
        (ZMod 2) A n).hom ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) A (A ∪ B)
          (ContinuousMap.id X) Set.subset_union_left) n ∧
    HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightToUnionRelative
          (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange B)) n ≫
      (ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso
        (ZMod 2) A B hA hB n).hom =
      (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso
        (ZMod 2) B n).hom ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) B (A ∪ B)
          (ContinuousMap.id X) Set.subset_union_right) n := by
  have hA : (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso (ZMod 2) A n).hom =
      HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap (ZMod 2) A) n := rfl
  have hB : (ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso (ZMod 2) B n).hom =
      HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeLiteralComparison.rangeRelativeCokernelMap (ZMod 2) B) n := rfl
  rw [ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso_hom,
    hA, hB]
  constructor
  · have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n) (t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_union_left X A B)
    simp only [HomologicalComplex.homologyMap_comp] at h
    exact h.trans (HomologicalComplex.homologyMap_comp _ _ _)
  · have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n) (t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_union_right X A B)
    simp only [HomologicalComplex.homologyMap_comp] at h
    exact h.trans (HomologicalComplex.homologyMap_comp _ _ _)

theorem t00A04_relativeMV_middle_aux_small_quotient_exact_literal
    (X : Type) [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ)
    (a : (ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2) A).homology n)
    (b : (ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2) B).homology n)
    (hab : HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) A (A ∪ B)
            (ContinuousMap.id X) Set.subset_union_left) n a =
        HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) B (A ∪ B)
            (ContinuousMap.id X) Set.subset_union_right) n b) :
    ∃ c : (ConstructionTargets.CoefficientRelativeSmall.relativeChains
        (ZMod 2) (A ∩ B)).homology n,
      HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) (A ∩ B) A
            (ContinuousMap.id X) Set.inter_subset_left) n c = a ∧
      HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) (A ∩ B) B
          (ContinuousMap.id X) Set.inter_subset_right) n c = b := by
  have hinterA :=
    t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_inter_left X A B
  have hinterB :=
    t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_inter_right X A B
  have hunionA :=
    t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_union_left X A B
  have hunionB :=
    t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_union_right X A B
  have hinter :=
    t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_inter_homology X A B n
  have hunion :=
    t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_union_homology
      X A B hA hB n
  have hs := t00A04_relativeMV_middle_aux_chain_shortExact X A B
  have _ := hinterA
  have _ := hinterB
  have _ := hunionA
  have _ := hunionB
  let S := ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex.shortComplex
    (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
      (ConstructionTargets.SingularExcision.ambientSubspaceRange B)
  let IA := ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso
    (ZMod 2) A n
  let IB := ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso
    (ZMod 2) B n
  let II := ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.intersectionRelativeIso
    (ZMod 2) A B n
  let J := ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso
    (ZMod 2) A B hA hB n
  have hmc : ∀ {K L M : ChainComplex (ModuleCat (ZMod 2)) ℕ} (φ : K ⟶ L) (ψ : L ⟶ M) (z : K.homology n),
      HomologicalComplex.homologyMap ψ n (HomologicalComplex.homologyMap φ n z) =
        HomologicalComplex.homologyMap (φ ≫ ψ) n z := by
    intro K L M φ ψ z
    rw [HomologicalComplex.homologyMap_comp]
    rfl
  let a' := IA.inv a
  let b' := IB.inv b
  let x : S.X₂.homology n :=
    HomologicalComplex.homologyMap (biprod.inl : _ ⟶ S.X₂) n a' +
      HomologicalComplex.homologyMap (biprod.inr : _ ⟶ S.X₂) n b'
  have hl : HomologicalComplex.homologyMap ((biprod.inl : _ ⟶ S.X₂) ≫ S.g) n =
      HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftToUnionRelative
        (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
          (ConstructionTargets.SingularExcision.ambientSubspaceRange B)) n := by
    congr 1
    exact biprod.inl_desc _ _
  have hr : HomologicalComplex.homologyMap ((biprod.inr : _ ⟶ S.X₂) ≫ S.g) n =
      -HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightToUnionRelative
        (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
          (ConstructionTargets.SingularExcision.ambientSubspaceRange B)) n := by
    rw [← HomologicalComplex.homologyMap_neg]
    congr 1
    exact biprod.inr_desc _ _
  have hgx' : HomologicalComplex.homologyMap S.g n x =
      HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.leftToUnionRelative
        (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
          (ConstructionTargets.SingularExcision.ambientSubspaceRange B)) n a' -
      HomologicalComplex.homologyMap (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.rightToUnionRelative
        (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
          (ConstructionTargets.SingularExcision.ambientSubspaceRange B)) n b' := by
    dsimp only [x]
    erw [map_add, hmc, hmc, hl, hr]
    rw [sub_eq_add_neg]
    rfl
  have hgx : HomologicalComplex.homologyMap S.g n x = 0 := by
    have hJ : J.hom (HomologicalComplex.homologyMap S.g n x) = 0 := by
      have h1 := ConcreteCategory.congr_hom hunion.1 a'
      have h2 := ConcreteCategory.congr_hom hunion.2 b'
      erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1 h2
      have ea : IA.hom a' = a := Iso.inv_hom_id_apply IA a
      have eb : IB.hom b' = b := Iso.inv_hom_id_apply IB b
      erw [ea] at h1
      erw [eb] at h2
      rw [hgx']
      erw [map_sub, h1, h2, hab, sub_self]
    have := congrArg J.inv hJ
    rwa [Iso.hom_inv_id_apply, map_zero] at this
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (hs.homology_exact₂ n) x hgx
  change HomologicalComplex.homologyMap S.f n y = x at hy
  refine ⟨II.hom y, ?_, ?_⟩
  · have h1 := ConcreteCategory.congr_hom hinter.1 y
    simp only [ConcreteCategory.comp_apply] at h1
    rw [← h1]
    have : HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToLeftRelative
          (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange B)) n y = a' := by
      rw [show ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToLeftRelative
          (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange B) = S.f ≫ biprod.fst from
          (biprod.lift_fst _ _).symm]
      erw [← hmc, hy]
      dsimp only [x]
      erw [map_add, hmc, hmc]
      have k1 : HomologicalComplex.homologyMap ((biprod.inl : _ ⟶ S.X₂) ≫ biprod.fst) n a' = a' := by
        rw [biprod.inl_fst, HomologicalComplex.homologyMap_id]; rfl
      have k2 : HomologicalComplex.homologyMap ((biprod.inr : _ ⟶ S.X₂) ≫ biprod.fst) n b' = 0 := by
        rw [biprod.inr_fst, HomologicalComplex.homologyMap_zero]; rfl
      convert congrArg₂ (· + ·) k1 k2 using 1
      simp
    rw [this]
    exact Iso.inv_hom_id_apply IA a
  · have h1 := ConcreteCategory.congr_hom hinter.2 y
    simp only [ConcreteCategory.comp_apply] at h1
    rw [← h1]
    have : HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToRightRelative
          (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange B)) n y = b' := by
      rw [show ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToRightRelative
          (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange B) = S.f ≫ biprod.snd from
          (biprod.lift_snd _ _).symm]
      erw [← hmc, hy]
      dsimp only [x]
      erw [map_add, hmc, hmc]
      have k1 : HomologicalComplex.homologyMap ((biprod.inl : _ ⟶ S.X₂) ≫ biprod.snd) n a' = 0 := by
        rw [biprod.inl_snd, HomologicalComplex.homologyMap_zero]; rfl
      have k2 : HomologicalComplex.homologyMap ((biprod.inr : _ ⟶ S.X₂) ≫ biprod.snd) n b' = b' := by
        rw [biprod.inr_snd, HomologicalComplex.homologyMap_id]; rfl
      convert congrArg₂ (· + ·) k1 k2 using 1
      simp
    rw [this]
    exact Iso.inv_hom_id_apply IB b

/-- Generic set transport for the De Morgan rewrites: the set arguments of
`pairMap` are generalized to variables, so `subst` applies and the subset proofs
are irrelevant. -/
theorem t00A04_relativeMV_aux_pairMap_set_transport
    (X : Type) [TopologicalSpace X] (S S' T U : Set X) (hS : S = S')
    (hT : Set.MapsTo (ContinuousMap.id X) S T) (hU : Set.MapsTo (ContinuousMap.id X) S U)
    (hT' : Set.MapsTo (ContinuousMap.id X) S' T) (hU' : Set.MapsTo (ContinuousMap.id X) S' U)
    (n : ℕ) (a : (ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2) T).homology n)
    (b : (ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2) U).homology n)
    (h : ∃ c : (ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2) S).homology n,
      HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) S T (ContinuousMap.id X) hT) n c = a ∧
      HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) S U (ContinuousMap.id X) hU) n c = b) :
    ∃ c : (ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2) S').homology n,
      HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) S' T (ContinuousMap.id X) hT') n c = a ∧
      HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) S' U (ContinuousMap.id X) hU') n c = b := by
  subst hS
  exact h

theorem t00A04_relativeMV_aux_pairMap_target_transport
    (X : Type) [TopologicalSpace X] (P Q D D' : Set X) (hD : D = D')
    (hP : Set.MapsTo (ContinuousMap.id X) P D) (hQ : Set.MapsTo (ContinuousMap.id X) Q D)
    (hP' : Set.MapsTo (ContinuousMap.id X) P D') (hQ' : Set.MapsTo (ContinuousMap.id X) Q D')
    (n : ℕ) (a : (ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2) P).homology n)
    (b : (ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2) Q).homology n)
    (h : HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) P D (ContinuousMap.id X) hP) n a =
        HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Q D (ContinuousMap.id X) hQ) n b) :
    HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) P D' (ContinuousMap.id X) hP') n a =
        HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Q D' (ContinuousMap.id X) hQ') n b := by
  subst hD
  exact h

theorem t00A04_relativeMV_aux_pairMap_kernel_transport
    (X : Type) [TopologicalSpace X] (S S' T U : Set X) (hS : S = S')
    (hT : Set.MapsTo (ContinuousMap.id X) S T) (hU : Set.MapsTo (ContinuousMap.id X) S U)
    (hT' : Set.MapsTo (ContinuousMap.id X) S' T) (hU' : Set.MapsTo (ContinuousMap.id X) S' U)
    (n : ℕ)
    (h : ∀ c' : (ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2) S).homology n,
      HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) S T (ContinuousMap.id X) hT) n c' = 0 →
      HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) S U (ContinuousMap.id X) hU) n c' = 0 →
      c' = 0) :
    ∀ c : (ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2) S').homology n,
      HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) S' T (ContinuousMap.id X) hT') n c = 0 →
      HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) S' U (ContinuousMap.id X) hU') n c = 0 →
      c = 0 := by
  subst hS
  exact h

theorem t00A04_relativeMV_aux_homology_set_transport
    (X : Type) [TopologicalSpace X] (S S' : Set X) (hS : S = S') (n : ℕ)
    (h : Subsingleton ((ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2) S).homology n)) :
    Subsingleton ((ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2) S').homology n) := by
  subst hS
  exact h

theorem t00A04_relativeMV_middle_aux_complement_rewrite_aux_transport
    (X : Type) [TopologicalSpace X] (K L : Set X) (n : ℕ)
    (a : t00A04_ModTwoLocalHomology X K n) (b : t00A04_ModTwoLocalHomology X L n)
    (h : ∃ c : (ConstructionTargets.CoefficientRelativeSmall.relativeChains
        (ZMod 2) (Kᶜ ∩ Lᶜ)).homology n,
      HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) (Kᶜ ∩ Lᶜ) Kᶜ
            (ContinuousMap.id X) Set.inter_subset_left) n c = a ∧
      HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) (Kᶜ ∩ Lᶜ) Lᶜ
            (ContinuousMap.id X) Set.inter_subset_right) n c = b) :
    ∃ c : t00A04_ModTwoLocalHomology X (K ∪ L) n,
      t00A04_modTwo_restrict X K (K ∪ L) Set.subset_union_left n c = a ∧
      t00A04_modTwo_restrict X L (K ∪ L) Set.subset_union_right n c = b := by
  exact t00A04_relativeMV_aux_pairMap_set_transport X (Kᶜ ∩ Lᶜ) (K ∪ L)ᶜ Kᶜ Lᶜ
    (Set.compl_union K L).symm _ _ _ _ n a b h

theorem t00A04_relativeMV_middle_aux_complement_rewrite_aux_input_transport
    (X : Type) [TopologicalSpace X] (K L : Set X) (n : ℕ)
    (a : t00A04_ModTwoLocalHomology X K n) (b : t00A04_ModTwoLocalHomology X L n)
    (hab : t00A04_modTwo_restrict X (K ∩ L) K Set.inter_subset_left n a =
      t00A04_modTwo_restrict X (K ∩ L) L Set.inter_subset_right n b) :
    HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Kᶜ (Kᶜ ∪ Lᶜ)
          (ContinuousMap.id X) Set.subset_union_left) n a =
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Lᶜ (Kᶜ ∪ Lᶜ)
          (ContinuousMap.id X) Set.subset_union_right) n b := by
  exact t00A04_relativeMV_aux_pairMap_target_transport X Kᶜ Lᶜ (K ∩ L)ᶜ (Kᶜ ∪ Lᶜ)
    (Set.compl_inter K L) _ _ _ _ n a b hab

theorem t00A04_relativeMV_middle_aux_complement_rewrite
    (X : Type) [TopologicalSpace X] [T2Space X] (K L : Set X)
    (hK : IsCompact K) (hL : IsCompact L) (n : ℕ)
    (a : t00A04_ModTwoLocalHomology X K n) (b : t00A04_ModTwoLocalHomology X L n)
    (hab : t00A04_modTwo_restrict X (K ∩ L) K Set.inter_subset_left n a =
      t00A04_modTwo_restrict X (K ∩ L) L Set.inter_subset_right n b) :
    ∃ c : t00A04_ModTwoLocalHomology X (K ∪ L) n,
      t00A04_modTwo_restrict X K (K ∪ L) Set.subset_union_left n c = a ∧
      t00A04_modTwo_restrict X L (K ∪ L) Set.subset_union_right n c = b := by
  apply t00A04_relativeMV_middle_aux_complement_rewrite_aux_transport X K L n a b
  apply t00A04_relativeMV_middle_aux_small_quotient_exact_literal X Kᶜ Lᶜ
    hK.isClosed.isOpen_compl hL.isClosed.isOpen_compl n a b
  exact t00A04_relativeMV_middle_aux_complement_rewrite_aux_input_transport
    X K L n a b hab

theorem t00A04_relativeMV_middle
    (X : Type) [TopologicalSpace X] [T2Space X] (K L : Set X)
    (hK : IsCompact K) (hL : IsCompact L) (n : ℕ)
    (a : t00A04_ModTwoLocalHomology X K n) (b : t00A04_ModTwoLocalHomology X L n)
    (hab : t00A04_modTwo_restrict X (K ∩ L) K Set.inter_subset_left n a =
      t00A04_modTwo_restrict X (K ∩ L) L Set.inter_subset_right n b) :
    ∃ c : t00A04_ModTwoLocalHomology X (K ∪ L) n,
      t00A04_modTwo_restrict X K (K ∪ L) Set.subset_union_left n c = a ∧
      t00A04_modTwo_restrict X L (K ∪ L) Set.subset_union_right n c = b := by
  exact t00A04_relativeMV_middle_aux_complement_rewrite X K L hK hL n a b hab

/-- **Relative Mayer--Vietoris, left term.**  If `H_{n+1}(X, X \ (K ∩ L))`
vanishes, a class on `K ∪ L` that restricts to zero on `K` and on `L` is zero
(it would come from the connecting map). -/
theorem t00A04_relativeMV_injective_aux_small_quotient_kernel
    (X : Type) [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (n : ℕ)
    (hzero : Subsingleton
      ((ConstructionTargets.CoefficientRelativeSmall.relativeChains
        (ZMod 2) (A ∪ B)).homology (n + 1)))
    (c : (ConstructionTargets.CoefficientRelativeSmall.relativeChains
      (ZMod 2) (A ∩ B)).homology n)
    (hcA : HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) (A ∩ B) A
        (ContinuousMap.id X) Set.inter_subset_left) n c = 0)
    (hcB : HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) (A ∩ B) B
        (ContinuousMap.id X) Set.inter_subset_right) n c = 0) : c = 0 := by
  have hinterA :=
    t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_inter_left X A B
  have hinterB :=
    t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_inter_right X A B
  have hunionA :=
    t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_union_left X A B
  have hunionB :=
    t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_union_right X A B
  have hinter :=
    t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_inter_homology X A B n
  have hunion :=
    t00A04_relativeMV_middle_aux_small_quotient_exact_literal_aux_union_homology
      X A B hA hB n
  have _ := hinterA
  have _ := hinterB
  have _ := hunionA
  have _ := hunionB
  have _ := hunion
  have hs := t00A04_relativeMV_middle_aux_chain_shortExact X A B
  let S := ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex.shortComplex
    (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
      (ConstructionTargets.SingularExcision.ambientSubspaceRange B)
  let IA := ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso
    (ZMod 2) A n
  let IB := ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.rangeRelativeIso
    (ZMod 2) B n
  let II := ConstructionTargets.CoefficientSubcomplexRelativeLiteralHomologyIso.intersectionRelativeIso
    (ZMod 2) A B n
  let J := ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare.relativeComparisonIso
    (ZMod 2) A B hA hB (n + 1)
  have hmc : ∀ {K L M : ChainComplex (ModuleCat (ZMod 2)) ℕ} (φ : K ⟶ L) (ψ : L ⟶ M) (z : K.homology n),
      HomologicalComplex.homologyMap ψ n (HomologicalComplex.homologyMap φ n z) =
        HomologicalComplex.homologyMap (φ ≫ ψ) n z := by
    intro K L M φ ψ z
    rw [HomologicalComplex.homologyMap_comp]
    rfl
  let c' := II.inv c
  have hc' : II.hom c' = c := Iso.inv_hom_id_apply II c
  have hfst : HomologicalComplex.homologyMap (biprod.fst : S.X₂ ⟶ _) n
      (HomologicalComplex.homologyMap S.f n c') = 0 := by
    have h1 := ConcreteCategory.congr_hom hinter.1 c'
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hc', hcA] at h1
    have h2 : HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToLeftRelative
          (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange B)) n c' = 0 := by
      have := congrArg IA.inv h1
      erw [Iso.hom_inv_id_apply, map_zero] at this
      exact this
    erw [hmc]
    convert h2 using 3
    congr 1
    exact biprod.lift_fst (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToLeftRelative (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A) (ConstructionTargets.SingularExcision.ambientSubspaceRange B))
      (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToRightRelative (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A) (ConstructionTargets.SingularExcision.ambientSubspaceRange B))
  have hsnd : HomologicalComplex.homologyMap (biprod.snd : S.X₂ ⟶ _) n
      (HomologicalComplex.homologyMap S.f n c') = 0 := by
    have h1 := ConcreteCategory.congr_hom hinter.2 c'
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hc', hcB] at h1
    have h2 : HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToRightRelative
          (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A)
            (ConstructionTargets.SingularExcision.ambientSubspaceRange B)) n c' = 0 := by
      have := congrArg IB.inv h1
      erw [Iso.hom_inv_id_apply, map_zero] at this
      exact this
    erw [hmc]
    convert h2 using 3
    congr 1
    exact biprod.lift_snd (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToLeftRelative (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A) (ConstructionTargets.SingularExcision.ambientSubspaceRange B))
      (ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows.intersectionToRightRelative (ZMod 2) (ConstructionTargets.SingularExcision.ambientSubspaceRange A) (ConstructionTargets.SingularExcision.ambientSubspaceRange B))
  have hf : HomologicalComplex.homologyMap S.f n c' = 0 := by
    set w := HomologicalComplex.homologyMap S.f n c'
    have hT : HomologicalComplex.homologyMap (𝟙 S.X₂) n =
        HomologicalComplex.homologyMap ((biprod.fst : S.X₂ ⟶ _) ≫ biprod.inl) n +
          HomologicalComplex.homologyMap ((biprod.snd : S.X₂ ⟶ _) ≫ biprod.inr) n := by
      erw [← HomologicalComplex.homologyMap_add]
      congr 1
      exact biprod.total.symm
    have htot := ConcreteCategory.congr_hom hT w
    rw [HomologicalComplex.homologyMap_id] at htot
    have htot' : w = HomologicalComplex.homologyMap ((biprod.fst : S.X₂ ⟶ _) ≫ biprod.inl) n w +
        HomologicalComplex.homologyMap ((biprod.snd : S.X₂ ⟶ _) ≫ biprod.inr) n w := htot
    rw [← hmc (biprod.fst : S.X₂ ⟶ _) biprod.inl w,
      ← hmc (biprod.snd : S.X₂ ⟶ _) biprod.inr w] at htot'
    erw [hfst, hsnd] at htot'
    rw [map_zero, map_zero] at htot'
    exact htot'.trans (zero_add _)
  have hJinj : Function.Injective J.hom := by
    intro p q h
    have := congrArg J.inv h
    erw [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply] at this
    exact this
  haveI hsub : Subsingleton (S.X₃.homology (n + 1)) := by
    constructor
    intro p q
    exact hJinj (Subsingleton.elim (J.hom p) (J.hom q))
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (hs.homology_exact₁ (n + 1) n rfl) c' hf
  have hc0 : c' = 0 := by
    rw [← hz, Subsingleton.elim z 0]
    exact map_zero _
  rw [← hc', hc0]
  exact map_zero _

theorem t00A04_relativeMV_injective_aux_complement_rewrite_aux_transport
    (X : Type) [TopologicalSpace X] (K L : Set X) (n : ℕ)
    (c : t00A04_ModTwoLocalHomology X (K ∪ L) n)
    (h : ∀ c' : (ConstructionTargets.CoefficientRelativeSmall.relativeChains
        (ZMod 2) (Kᶜ ∩ Lᶜ)).homology n,
      HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) (Kᶜ ∩ Lᶜ) Kᶜ
            (ContinuousMap.id X) Set.inter_subset_left) n c' = 0 →
      HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) (Kᶜ ∩ Lᶜ) Lᶜ
            (ContinuousMap.id X) Set.inter_subset_right) n c' = 0 → c' = 0)
    (hcK : t00A04_modTwo_restrict X K (K ∪ L) Set.subset_union_left n c = 0)
    (hcL : t00A04_modTwo_restrict X L (K ∪ L) Set.subset_union_right n c = 0) : c = 0 := by
  exact t00A04_relativeMV_aux_pairMap_kernel_transport X (Kᶜ ∩ Lᶜ) (K ∪ L)ᶜ Kᶜ Lᶜ
    (Set.compl_union K L).symm _ _ _ _ n h c hcK hcL

theorem t00A04_relativeMV_injective_aux_complement_rewrite_aux_hzero_transport
    (X : Type) [TopologicalSpace X] (K L : Set X) (n : ℕ)
    (hzero : Subsingleton (t00A04_ModTwoLocalHomology X (K ∩ L) (n + 1))) :
    Subsingleton ((ConstructionTargets.CoefficientRelativeSmall.relativeChains
      (ZMod 2) (Kᶜ ∪ Lᶜ)).homology (n + 1)) := by
  exact t00A04_relativeMV_aux_homology_set_transport X (K ∩ L)ᶜ (Kᶜ ∪ Lᶜ)
    (Set.compl_inter K L) (n + 1) hzero

theorem t00A04_relativeMV_injective_aux_complement_rewrite
    (X : Type) [TopologicalSpace X] [T2Space X] (K L : Set X)
    (hK : IsCompact K) (hL : IsCompact L) (n : ℕ)
    (hzero : Subsingleton (t00A04_ModTwoLocalHomology X (K ∩ L) (n + 1)))
    (c : t00A04_ModTwoLocalHomology X (K ∪ L) n)
    (hcK : t00A04_modTwo_restrict X K (K ∪ L) Set.subset_union_left n c = 0)
    (hcL : t00A04_modTwo_restrict X L (K ∪ L) Set.subset_union_right n c = 0) : c = 0 := by
  apply t00A04_relativeMV_injective_aux_complement_rewrite_aux_transport X K L n c
  · apply t00A04_relativeMV_injective_aux_small_quotient_kernel X Kᶜ Lᶜ
      hK.isClosed.isOpen_compl hL.isClosed.isOpen_compl n
    exact t00A04_relativeMV_injective_aux_complement_rewrite_aux_hzero_transport
      X K L n hzero
  · exact hcK
  · exact hcL

theorem t00A04_relativeMV_injective
    (X : Type) [TopologicalSpace X] [T2Space X] (K L : Set X)
    (hK : IsCompact K) (hL : IsCompact L) (n : ℕ)
    (hzero : Subsingleton (t00A04_ModTwoLocalHomology X (K ∩ L) (n + 1)))
    (c : t00A04_ModTwoLocalHomology X (K ∪ L) n)
    (hcK : t00A04_modTwo_restrict X K (K ∪ L) Set.subset_union_left n c = 0)
    (hcL : t00A04_modTwo_restrict X L (K ∪ L) Set.subset_union_right n c = 0) :
    c = 0 := by
  exact t00A04_relativeMV_injective_aux_complement_rewrite X K L hK hL n hzero c hcK hcL

/-- **LIBRARY F2.** The relative compact-complement Mayer--Vietoris union
step in Hatcher 3.27.  Its three inputs are explicit so seats are independent. -/
theorem t00A04_hatcherConclusion_union_aux_pointRestriction_restrict
    (X : Type) [TopologicalSpace X] (A K : Set X) (h : A ⊆ K) (x : X) (hx : x ∈ A)
    (n : ℕ) (c : t00A04_ModTwoLocalHomology X K n) :
    t00A04_modTwo_pointRestriction X A x hx n (t00A04_modTwo_restrict X A K h n c) =
      t00A04_modTwo_pointRestriction X K x (h hx) n c := by
  change
    ((HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Kᶜ Aᶜ
          (ContinuousMap.id X) _) n ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Aᶜ ({x} : Set X)ᶜ
          (ContinuousMap.id X) _) n) c) = _
  rw [← HomologicalComplex.homologyMap_comp,
    ← ConstructionTargets.CoefficientPairNaturality.pair_comp]
  rfl

theorem t00A04_hatcherConclusion_union
    (X : Type) [TopologicalSpace X] [T2Space X] (d : ℕ)
    (A B : Set X) (hA : IsCompact A) (hB : IsCompact B)
    (hAi : t00A04_HatcherConclusion X d A)
    (hBi : t00A04_HatcherConclusion X d B)
    (hABi : t00A04_HatcherConclusion X d (A ∩ B))
    (hloc : ∀ x : X, ∀ a b : t00A04_ModTwoLocalHomology X {x} d,
      a ≠ 0 → b ≠ 0 → a = b) :
    t00A04_HatcherConclusion X d (A ∪ B) := by
  constructor
  · intro i hdi
    constructor
    intro c c'
    have hABzero :
        Subsingleton (t00A04_ModTwoLocalHomology X (A ∩ B) (i + 1)) :=
      hABi.vanish_above (i + 1) (lt_trans hdi (Nat.lt_succ_self i))
    have hcA :
        t00A04_modTwo_restrict X A (A ∪ B) Set.subset_union_left i (c - c') = 0 := by
      exact @Subsingleton.elim _ (hAi.vanish_above i hdi) _ _
    have hcB :
        t00A04_modTwo_restrict X B (A ∪ B) Set.subset_union_right i (c - c') = 0 := by
      exact @Subsingleton.elim _ (hBi.vanish_above i hdi) _ _
    have hcc' := t00A04_relativeMV_injective X A B hA hB i hABzero (c - c') hcA hcB
    exact sub_eq_zero.mp hcc'
  · rcases hAi.exists_everywhere_nonzero with ⟨cA, hcA⟩
    rcases hBi.exists_everywhere_nonzero with ⟨cB, hcB⟩
    have hab :
        t00A04_modTwo_restrict X (A ∩ B) A Set.inter_subset_left d cA =
          t00A04_modTwo_restrict X (A ∩ B) B Set.inter_subset_right d cB := by
      apply sub_eq_zero.mp
      apply (hABi.eq_zero_iff_pointwise _).2
      intro x hx
      rw [map_sub]
      apply sub_eq_zero.mpr
      apply hloc x
      · rw [t00A04_hatcherConclusion_union_aux_pointRestriction_restrict]
        exact hcA x hx.1
      · rw [t00A04_hatcherConclusion_union_aux_pointRestriction_restrict]
        exact hcB x hx.2
    rcases t00A04_relativeMV_middle X A B hA hB d cA cB hab with
      ⟨c, hc_to_A, hc_to_B⟩
    refine ⟨c, ?_⟩
    intro x hx
    rcases hx with hxA | hxB
    · rw [← t00A04_hatcherConclusion_union_aux_pointRestriction_restrict
          X A (A ∪ B) Set.subset_union_left x hxA d c, hc_to_A]
      exact hcA x hxA
    · rw [← t00A04_hatcherConclusion_union_aux_pointRestriction_restrict
          X B (A ∪ B) Set.subset_union_right x hxB d c, hc_to_B]
      exact hcB x hxB
  · intro c
    constructor
    · intro hc
      subst c
      intro x hx
      exact map_zero _
    · intro hc
      have hABzero :
          Subsingleton (t00A04_ModTwoLocalHomology X (A ∩ B) (d + 1)) :=
        hABi.vanish_above (d + 1) (Nat.lt_succ_self d)
      have hcA : t00A04_modTwo_restrict X A (A ∪ B) Set.subset_union_left d c = 0 := by
        apply (hAi.eq_zero_iff_pointwise _).2
        intro x hx
        rw [t00A04_hatcherConclusion_union_aux_pointRestriction_restrict]
        exact hc x (Or.inl hx)
      have hcB : t00A04_modTwo_restrict X B (A ∪ B) Set.subset_union_right d c = 0 := by
        apply (hBi.eq_zero_iff_pointwise _).2
        intro x hx
        rw [t00A04_hatcherConclusion_union_aux_pointRestriction_restrict]
        exact hc x (Or.inr hx)
      exact t00A04_relativeMV_injective X A B hA hB d hABzero c hcA hcB

/-- **LIBRARY.** Top local mod-2 homology of a boundaryless manifold has a
unique nonzero element. -/
/- The purely algebraic last step.  Stating the two-element description
explicitly keeps the geometric leaves below independent of any choice of a
distinguished generator. -/
theorem t00A04_modTwoLocalHomology_unique_nonzero_aux_of_eq_zero_or_eq
    {M : Type*} [Zero M]
    (g : M) (hspan : ∀ z : M, z = 0 ∨ z = g) :
    ∀ a b : M, a ≠ 0 → b ≠ 0 → a = b := by
  intro a b ha hb
  rcases hspan a with ha0 | hag
  · exact (ha ha0).elim
  rcases hspan b with hb0 | hbg
  · exact (hb hb0).elim
  exact hag.trans hbg.symm

/- Euclidean local calculation.  This is the missing coefficient analogue of
the integral disk computations currently available in ConstructionTargets:
excision to an open disk, radial comparison with its boundary sphere, and the
coefficient long exact sequence identify the group with `ZMod 2`. -/
/- Algebraic step banked by lemma-3 (job invoke-1792640026768-2203): a group
identified with `ZMod 2` by a zero-preserving equivalence has at most one
nonzero element. -/
theorem t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_of_equiv
    {M : Type*} [Zero M] (e : M ≃ ZMod 2) (e0 : e 0 = 0) :
    ∀ a b : M, a ≠ 0 → b ≠ 0 → a = b := by
  intro a b ha hb
  apply e.injective
  have hea : e a ≠ 0 := by
    intro h
    apply ha
    apply e.injective
    simpa only [e0] using h
  have heb : e b ≠ 0 := by
    intro h
    apply hb
    apply e.injective
    simpa only [e0] using h
  have hone (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
    fin_cases z
    · exact (hz rfl).elim
    · rfl
  exact (hone (e a) hea).trans (hone (e b) heb).symm

/- Translation `y ↦ y - x` moves the local pair at `x` to the local pair at
the origin (`CoefficientManifoldLocalComparison.translationIso`). -/
theorem t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_translate (d : ℕ)
    (h0 : ∀ a b : t00A04_ModTwoLocalHomology (EuclideanSpace ℝ (Fin d)) {0} d,
      a ≠ 0 → b ≠ 0 → a = b) :
    ∀ x : EuclideanSpace ℝ (Fin d),
      ∀ a b : t00A04_ModTwoLocalHomology (EuclideanSpace ℝ (Fin d)) {x} d,
        a ≠ 0 → b ≠ 0 → a = b := by
  intro x a b ha hb
  let i := (ConstructionTargets.CoefficientManifoldLocalComparison.translationIso
    (ZMod 2) x d).toLinearEquiv
  apply i.injective
  exact h0 (i a) (i b) ((map_ne_zero_iff i i.injective).mpr ha)
    ((map_ne_zero_iff i i.injective).mpr hb)

/- Dimension `m + 2` at the origin: `CoefficientModelLocal.localIso`
(connecting map, radial retraction to the sphere, sphere normalization). -/
theorem t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_high (m : ℕ) :
    ∃ e : t00A04_ModTwoLocalHomology (EuclideanSpace ℝ (Fin (m+2))) {0} (m+2) ≃ ZMod 2,
      e 0 = 0 := by
  let i := ConstructionTargets.CoefficientModelLocal.localIso (ZMod 2) m
  exact ⟨i.toLinearEquiv.toEquiv, map_zero i.toLinearEquiv⟩

/- Dimension 0.  `EuclideanSpace ℝ (Fin 0)` is a point, so `{0}ᶜ = ∅` and the
relative group is absolute `H₀` of a point.  Route: the relative complex of
the empty subspace has the absolute chains as its cokernel
(`CoefficientRelativeSmall.subspaceMap` from the empty space is zero), then
`CoefficientH0.h0Iso` for the path-connected point. -/
theorem t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_zero_aux_emptyMap
    (R X : Type) [CommRing R] [TopologicalSpace X] :
    ConstructionTargets.CoefficientRelativeSmall.subspaceMap R (∅ : Set X) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro s
  exact isEmptyElim
    ((TopCat.toSSetObjEquiv (TopCat.of (∅ : Set X))
      (Opposite.op (SimplexCategory.mk n)) s)
      (Classical.choice inferInstance))

theorem t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_zero_aux_emptyRelativeH0
    (X : Type) [TopologicalSpace X] [PathConnectedSpace X] (p : X)
    (A : Set X) (hA : A = ∅) :
    ∃ e : ((ConstructionTargets.CoefficientRelativeSmall.relativeChains
        (ZMod 2) A).homology 0 : Type) ≃ ZMod 2,
      e 0 = 0 := by
  subst A
  let ciso : ConstructionTargets.CoefficientRelativeSmall.relativeChains
      (ZMod 2) (∅ : Set X) ≅
      ConstructionTargets.CoefficientH0.SingularChains (ZMod 2) (TopCat.of X) :=
    CategoryTheory.Limits.cokernelIsoOfEq
      (t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_zero_aux_emptyMap
        (ZMod 2) X) ≪≫
      CategoryTheory.Limits.cokernelZeroIsoTarget
  letI : IsIso ciso.hom := inferInstance
  let hiso := asIso (HomologicalComplex.homologyMap ciso.hom 0)
  let e := (hiso ≪≫
    ConstructionTargets.CoefficientH0.h0Iso (ZMod 2) p).toLinearEquiv
  exact ⟨e.toEquiv, map_zero e⟩

theorem t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_zero :
    ∃ e : t00A04_ModTwoLocalHomology (EuclideanSpace ℝ (Fin 0)) {0} 0 ≃ ZMod 2,
      e 0 = 0 := by
  let X := EuclideanSpace ℝ (Fin 0)
  have hpoint : ({0} : Set X) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_singleton_iff.mpr (Subsingleton.elim x 0)
  have hempty : ({0} : Set X)ᶜ = ∅ := by simp [hpoint]
  exact
    t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_zero_aux_emptyRelativeH0
      X (0 : X) ({0} : Set X)ᶜ hempty

/- Dimension 1.  `ℝ¹` is contractible, so
`CoefficientContractiblePair.contractibleH1KernelIso` identifies `H₁(ℝ¹, ℝ¹ \ 0)`
with the kernel of `H₀(ℝ¹ \ 0) → H₀(ℝ¹)`.  The two open half-lines are
path-connected and cover `ℝ¹ \ 0` (`CoefficientSmallH0.h0Iso` for an open
cover, as in `intervalCover`), so the map is `(ZMod 2)² → ZMod 2`, sum of
coordinates, with kernel spanned by `(1, 1)`.  Compare
`CoefficientSphereShift.sphereH1KernelIso` for the same pattern one dimension
up. -/
noncomputable def t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_one_aux_punctureIso :
    ConstructionTargets.CoefficientContractiblePair.H (ZMod 2) 0
        (TopCat.of (ConstructionTargets.CoefficientModelLocal.puncture 1)) ≅
      ModuleCat.of (ZMod 2) (Bool → ZMod 2) :=
  ConstructionTargets.CoefficientModelLocal.radialIso (ZMod 2) 1 0 ≪≫
    (ConstructionTargets.CoefficientRadialPair.F (ZMod 2) 0).mapIso
      (TopCat.isoOfHomeo
        (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundaryHomeomorph 1)).symm ≪≫
    ConstructionTargets.CoefficientSphereEndpoints.boundaryIso (ZMod 2)

theorem t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_one_aux_diskIso_hom :
    (ConstructionTargets.CoefficientSphereEndpoints.diskIso (ZMod 2)).hom =
      ConstructionTargets.CoefficientH0.h0Augmentation (ZMod 2) := by
  letI : ContractibleSpace ConstructionTargets.CoefficientSphereEndpoints.disk :=
    Metric.contractibleSpace_closedBall (by norm_num)
  let p : ConstructionTargets.CoefficientSphereEndpoints.disk :=
    Classical.choice inferInstance
  letI : IsIso
      (ConstructionTargets.CoefficientH0.h0Augmentation (ZMod 2)
        (X := ConstructionTargets.CoefficientSphereEndpoints.disk)) := by
    change IsIso (ConstructionTargets.CoefficientH0.h0Iso (ZMod 2) p).hom
    infer_instance
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  have hd : (ConstructionTargets.CoefficientSphereEndpoints.diskIso
      (ZMod 2)).hom.hom x ≠ 0 := by
    exact (map_ne_zero_iff _
      (ConcreteCategory.bijective_of_isIso
        (ConstructionTargets.CoefficientSphereEndpoints.diskIso
          (ZMod 2)).hom).1).mpr hx
  have ha : (ConstructionTargets.CoefficientH0.h0Augmentation
      (ZMod 2)).hom x ≠ 0 := by
    exact (map_ne_zero_iff _
      (ConcreteCategory.bijective_of_isIso
        (ConstructionTargets.CoefficientH0.h0Augmentation (ZMod 2))).1).mpr hx
  have hone (w : ZMod 2) (hw : w ≠ 0) : w = 1 := by
    fin_cases w
    · exact (hw rfl).elim
    · rfl
  exact (hone _ hd).trans (hone _ ha).symm

theorem t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_one_aux_coordinates_aux_disk :
    (ConstructionTargets.CoefficientSphereEndpoints.diskIso (ZMod 2)).hom =
      ConstructionTargets.CoefficientH0.h0Augmentation (ZMod 2) := by
  letI : ContractibleSpace ConstructionTargets.CoefficientSphereEndpoints.disk :=
    Metric.contractibleSpace_closedBall (by norm_num)
  let p : ConstructionTargets.CoefficientSphereEndpoints.disk :=
    Classical.choice inferInstance
  have hf : Function.Injective
      (ConstructionTargets.CoefficientSphereEndpoints.diskIso (ZMod 2)).hom.hom :=
    (ConstructionTargets.CoefficientSphereEndpoints.diskIso (ZMod 2)).toLinearEquiv.injective
  have hg : Function.Injective
      (ConstructionTargets.CoefficientH0.h0Augmentation (ZMod 2)
        (X := ConstructionTargets.CoefficientSphereEndpoints.disk)).hom := by
    change Function.Injective
      (ConstructionTargets.CoefficientH0.h0Iso (ZMod 2) p).hom.hom
    exact (ConstructionTargets.CoefficientH0.h0Iso (ZMod 2) p).toLinearEquiv.injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  generalize hfx :
      (ConstructionTargets.CoefficientSphereEndpoints.diskIso (ZMod 2)).hom.hom x = y
  generalize hgx :
      (ConstructionTargets.CoefficientH0.h0Augmentation (ZMod 2)).hom x = z
  fin_cases y <;> fin_cases z
  · rfl
  · exfalso
    have hx : x = 0 := hf (hfx.trans (map_zero _).symm)
    have ht := congrArg
      (ConstructionTargets.CoefficientH0.h0Augmentation (ZMod 2)).hom hx
    rw [map_zero, hgx] at ht
    exact one_ne_zero ht
  · exfalso
    have hx : x = 0 := hg (hgx.trans (map_zero _).symm)
    have ht := congrArg
      (ConstructionTargets.CoefficientSphereEndpoints.diskIso (ZMod 2)).hom.hom hx
    rw [map_zero, hfx] at ht
    exact one_ne_zero ht
  · rfl

theorem t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_one_aux_coordinates :
    (t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_one_aux_punctureIso).hom ≫
        ConstructionTargets.CoefficientCodiagonalKernel.sumMap (ZMod 2) =
      HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2)
          (ConstructionTargets.CoefficientModelLocal.puncture 1)) 0 ≫
          (ConstructionTargets.CoefficientH0.h0Iso (ZMod 2)
          (0 : EuclideanSpace ℝ (Fin 1))).hom := by
  dsimp [t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_one_aux_punctureIso]
  simp only [Category.assoc]
  rw [← ConstructionTargets.CoefficientSphereEndpoints.inclusion_coordinates]
  rw [t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_one_aux_coordinates_aux_disk]
  change _ = HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2)
        (ConstructionTargets.CoefficientModelLocal.puncture 1)) 0 ≫
      ConstructionTargets.CoefficientH0.h0Augmentation (ZMod 2)
  have hinc := ConstructionTargets.CoefficientH0.h0Augmentation_naturality (ZMod 2)
    (⟨Subtype.val, continuous_subtype_val⟩ : C(
      ConstructionTargets.CoefficientSphereEndpoints.boundary,
      ConstructionTargets.CoefficientSphereEndpoints.disk))
  change ConstructionTargets.CoefficientSphereEndpoints.inclusion (ZMod 2) ≫
      ConstructionTargets.CoefficientH0.h0Augmentation (ZMod 2) = _ at hinc
  rw [hinc]
  let fhome : C(T02A06.euclideanUnitSphere 1,
      ConstructionTargets.CoefficientSphereEndpoints.boundary) :=
    ⟨(ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundaryHomeomorph 1).symm,
      (ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundaryHomeomorph 1).symm.continuous⟩
  have hhome := ConstructionTargets.CoefficientH0.h0Augmentation_naturality (ZMod 2) fhome
  change (ConstructionTargets.CoefficientRadialPair.F (ZMod 2) 0).map
      (TopCat.ofHom fhome) ≫
      ConstructionTargets.CoefficientH0.h0Augmentation (ZMod 2) = _ at hhome
  have hfhome : TopCat.ofHom fhome = TopCat.ofHom
      (↑(ConstructionTargets.T02A06DiskRadialComparison.closedDiskBoundaryHomeomorph 1).symm) := by
    ext x
    rfl
  rw [hfhome] at hhome
  rw [hhome]
  have hrad := ConstructionTargets.CoefficientH0.h0Augmentation_naturality (ZMod 2)
    (ConstructionTargets.PuncturedNormedSpaceRadialEquivalence.radialNormalize
      (EuclideanSpace ℝ (Fin 1)))
  change (ConstructionTargets.CoefficientModelLocal.radialIso (ZMod 2) 1 0).hom ≫
      ConstructionTargets.CoefficientH0.h0Augmentation (ZMod 2) = _ at hrad
  exact hrad.trans (ConstructionTargets.CoefficientH0.h0Augmentation_naturality (ZMod 2)
    (⟨Subtype.val, continuous_subtype_val⟩ : C(
      ConstructionTargets.CoefficientModelLocal.puncture 1,
      EuclideanSpace ℝ (Fin 1)))).symm

theorem t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_one :
    ∃ e : t00A04_ModTwoLocalHomology (EuclideanSpace ℝ (Fin 1)) {0} 1 ≃ ZMod 2,
      e 0 = 0 := by
  let i :=
    ConstructionTargets.CoefficientContractiblePair.contractibleH1KernelIso
        (ZMod 2) (ConstructionTargets.CoefficientModelLocal.puncture 1) ≪≫
      CategoryTheory.Limits.kernel.mapIso
        (f := HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2)
            (ConstructionTargets.CoefficientModelLocal.puncture 1)) 0)
        (ConstructionTargets.CoefficientCodiagonalKernel.sumMap (ZMod 2))
        t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_one_aux_punctureIso
        (ConstructionTargets.CoefficientH0.h0Iso (ZMod 2)
          (0 : EuclideanSpace ℝ (Fin 1)))
        t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_one_aux_coordinates.symm ≪≫
      ConstructionTargets.CoefficientCodiagonalKernel.kernelIso (ZMod 2)
  exact ⟨i.toLinearEquiv.toEquiv, map_zero i.toLinearEquiv⟩

theorem t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean (d : ℕ) :
    ∀ x : EuclideanSpace ℝ (Fin d),
      ∀ a b : t00A04_ModTwoLocalHomology (EuclideanSpace ℝ (Fin d)) {x} d,
        a ≠ 0 → b ≠ 0 → a = b := by
  apply t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_translate d
  obtain ⟨e, e0⟩ : ∃ e : t00A04_ModTwoLocalHomology (EuclideanSpace ℝ (Fin d)) {0} d ≃
      ZMod 2, e 0 = 0 := by
    rcases d with _ | _ | m
    · exact t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_zero
    · exact t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_one
    · exact t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_high m
  exact t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_of_equiv e e0

/- Chart excision and transport.  The chart around `x` first identifies its
local pair with an open subset of `E`; a linear homeomorphism
`E ≃ₗ EuclideanSpace ℝ (Fin (finrank ℝ E))` transports the pair, and a
second excision identifies it with the ambient Euclidean local pair. -/
theorem t00A04_modTwoLocalHomology_unique_nonzero_aux_chart
    (E X : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X]
    [IsManifold I ∞ X] [BoundarylessManifold I X]
    (heuclidean : ∀ (d : ℕ) (x : EuclideanSpace ℝ (Fin d)),
      ∀ a b : t00A04_ModTwoLocalHomology (EuclideanSpace ℝ (Fin d)) {x} d,
        a ≠ 0 → b ≠ 0 → a = b) :
    ∀ x : X, ∀ a b : t00A04_ModTwoLocalHomology X {x} (Module.finrank ℝ E),
      a ≠ 0 → b ≠ 0 → a = b := by
  intro x a b ha hb
  let e := ConstructionTargets.CoefficientManifoldLocalComparison.allComparison
    (ZMod 2) (Module.finrank ℝ E) rfl x (Module.finrank ℝ E)
  have hinj : Function.Injective e.hom.hom :=
    (ConcreteCategory.bijective_of_isIso e.hom).1
  apply hinj
  exact heuclidean (Module.finrank ℝ E) 0 (e.hom.hom a) (e.hom.hom b)
    ((map_ne_zero_iff e.hom.hom hinj).mpr ha)
    ((map_ne_zero_iff e.hom.hom hinj).mpr hb)

theorem t00A04_modTwoLocalHomology_unique_nonzero
    (E X : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X]
    [IsManifold I ∞ X] [BoundarylessManifold I X] :
    ∀ x : X, ∀ a b : t00A04_ModTwoLocalHomology X {x} (Module.finrank ℝ E),
      a ≠ 0 → b ≠ 0 → a = b := by
  exact t00A04_modTwoLocalHomology_unique_nonzero_aux_chart E X I
    t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean
/-- Euclidean specialization of local uniqueness, with the degree written as
`d` so finite-union seats avoid dependent rewriting of `finrank`. -/
theorem t00A04_modTwoLocalHomology_unique_nonzero_euclidean (d : ℕ) :
    ∀ x : EuclideanSpace ℝ (Fin d),
      ∀ a b : t00A04_ModTwoLocalHomology (EuclideanSpace ℝ (Fin d)) {x} d,
        a ≠ 0 → b ≠ 0 → a = b := by
  exact t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean d

/-- **LIBRARY F1.** Hatcher 3.27 for a compact convex subset of the
finite-dimensional Euclidean model. -/
theorem t00A04_hatcherConclusion_compact_convex_euclidean_aux_empty
    (d n : ℕ) :
    Subsingleton (t00A04_ModTwoLocalHomology
      (EuclideanSpace ℝ (Fin d)) (∅ : Set (EuclideanSpace ℝ (Fin d))) n) := by
  change Subsingleton
    (((ConstructionTargets.CoefficientRelativeSmall.relativeChains
      (ZMod 2) ((∅ : Set (EuclideanSpace ℝ (Fin d)))ᶜ)).homology n : Type))
  rw [Set.compl_empty]
  let f := ConstructionTargets.CoefficientRelativeSmall.subspaceMap
    (ZMod 2) (Set.univ : Set (EuclideanSpace ℝ (Fin d)))
  haveI : IsIso f := by
    dsimp [f, ConstructionTargets.CoefficientRelativeSmall.subspaceMap,
      ConstructionTargets.CoefficientRelativeSmall.chains]
    rw [ConstructionTargets.SingularHomologyConcrete.subspaceInclusion_univ]
    apply Functor.map_isIso
  have hz : CategoryTheory.Limits.IsZero
      (ConstructionTargets.CoefficientRelativeSmall.relativeChains
        (ZMod 2) (Set.univ : Set (EuclideanSpace ℝ (Fin d)))) :=
    CategoryTheory.Limits.isZero_cokernel_of_epi f
  exact ModuleCat.subsingleton_of_isZero
    (Functor.map_isZero
      (HomologicalComplex.homologyFunctor (ModuleCat (ZMod 2))
        (ComplexShape.down ℕ) n) hz)

/-- Radial deformation of the complement of a compact convex set onto the
complement of any one of its points makes restriction to that point an
isomorphism on relative homology. -/
theorem t00A04_hatcherConclusion_compact_convex_euclidean_aux_pointRestriction_bijective_aux_complement
    (d : ℕ) (A : Set (EuclideanSpace ℝ (Fin d)))
    (hA : IsCompact A) (hconv : Convex ℝ A)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ A) :
    ∃ e : ContinuousMap.HomotopyEquiv
        ↥Aᶜ ↥(({x} : Set (EuclideanSpace ℝ (Fin d)))ᶜ),
      e.toFun =
        ⟨fun y ↦ ⟨y, by
          intro hyx
          exact y.property (hyx.symm ▸ hx)⟩,
          continuous_subtype_val.subtype_mk (fun y ↦ by
            intro hyx
            exact y.property (hyx.symm ▸ hx))⟩ := by
  obtain ⟨R, hR, hAR⟩ := hA.isBounded.subset_ball_lt 1 x
  let j : C(↥Aᶜ, ↥(({x} : Set (EuclideanSpace ℝ (Fin d)))ᶜ)) :=
    { toFun := fun y ↦ ⟨y, by
        intro hyx
        exact y.property (hyx.symm ▸ hx)⟩
      continuous_toFun := by fun_prop }
  let ρ : C(↥(({x} : Set (EuclideanSpace ℝ (Fin d)))ᶜ), ↥Aᶜ) :=
    { toFun := fun y ↦ ⟨x + (1 + R / ‖y.1 - x‖) • (y.1 - x), by
        intro hyA
        have hyne : y.1 - x ≠ 0 := sub_ne_zero.mpr y.property
        have hn : 0 < ‖y.1 - x‖ := norm_pos_iff.mpr hyne
        have hc : 0 ≤ 1 + R / ‖y.1 - x‖ := by positivity
        have hdist : dist (x + (1 + R / ‖y.1 - x‖) • (y.1 - x)) x =
            ‖y.1 - x‖ + R := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg hc]
          field_simp
        have hb := hAR hyA
        rw [Metric.mem_ball, hdist] at hb
        linarith⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        have hv : Continuous (fun y : ↥(({x} : Set (EuclideanSpace ℝ (Fin d)))ᶜ) ↦
            y.1 - x) := continuous_subtype_val.sub continuous_const
        have hn : Continuous (fun y : ↥(({x} : Set (EuclideanSpace ℝ (Fin d)))ᶜ) ↦
            ‖y.1 - x‖) := continuous_norm.comp hv
        have hn0 : ∀ y : ↥(({x} : Set (EuclideanSpace ℝ (Fin d)))ᶜ),
            ‖y.1 - x‖ ≠ 0 := fun y ↦ norm_ne_zero_iff.mpr (sub_ne_zero.mpr y.property)
        exact continuous_const.add
          ((continuous_const.add (continuous_const.div hn hn0)).smul hv) }
  let Hout : ContinuousMap.Homotopy (j.comp ρ) (ContinuousMap.id _) :=
    { toFun := fun ty ↦ ⟨(1 - (ty.1 : ℝ)) • ((j.comp ρ) ty.2).1 +
          (ty.1 : ℝ) • ty.2.1, by
        intro heq
        have hvne : ty.2.1 - x ≠ 0 := sub_ne_zero.mpr ty.2.property
        have hn : 0 < ‖ty.2.1 - x‖ := norm_pos_iff.mpr hvne
        have hc : 0 < (1 - (ty.1 : ℝ)) * (1 + R / ‖ty.2.1 - x‖) +
            (ty.1 : ℝ) := by
          have ht0 := ty.1.property.1
          have ht1 := ty.1.property.2
          have hRp : 0 ≤ R / ‖ty.2.1 - x‖ := by positivity
          nlinarith
        apply hvne
        have hz : ((1 - (ty.1 : ℝ)) * (1 + R / ‖ty.2.1 - x‖) +
            (ty.1 : ℝ)) • (ty.2.1 - x) = 0 := by
          calc
            _ = (1 - (ty.1 : ℝ)) • ((j.comp ρ) ty.2).1 +
                (ty.1 : ℝ) • ty.2.1 - x := by dsimp [j, ρ]; module
            _ = 0 := sub_eq_zero.mpr heq
        exact (smul_eq_zero.mp hz).resolve_left hc.ne'⟩
      continuous_toFun := by fun_prop
      map_zero_left := by intro y; apply Subtype.ext; simp [j, ρ]
      map_one_left := by intro y; apply Subtype.ext; simp }
  let Hin : ContinuousMap.Homotopy (ρ.comp j) (ContinuousMap.id _) :=
    { toFun := fun ty ↦ ⟨(1 - (ty.1 : ℝ)) • ((ρ.comp j) ty.2).1 +
          (ty.1 : ℝ) • ty.2.1, by
        intro hz
        have ht0 : 0 ≤ (ty.1 : ℝ) := ty.1.property.1
        have ht1 : (ty.1 : ℝ) ≤ 1 := ty.1.property.2
        have hvne : ty.2.1 - x ≠ 0 := sub_ne_zero.mpr (by
          intro hyx
          exact ty.2.property (hyx.symm ▸ hx))
        have hn : 0 < ‖ty.2.1 - x‖ := norm_pos_iff.mpr hvne
        let c : ℝ := (1 - (ty.1 : ℝ)) * (1 + R / ‖ty.2.1 - x‖) +
          (ty.1 : ℝ)
        have hc : 1 ≤ c := by
          dsimp [c]
          have hRp : 0 ≤ R / ‖ty.2.1 - x‖ := by positivity
          nlinarith
        have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
        have hzform : (1 - (ty.1 : ℝ)) • ((ρ.comp j) ty.2).1 +
              (ty.1 : ℝ) • ty.2.1 = x + c • (ty.2.1 - x) := by
          dsimp [c, ρ, j]
          module
        have hp : ty.2.1 = (1 - c⁻¹) • x + c⁻¹ •
            ((1 - (ty.1 : ℝ)) • ((ρ.comp j) ty.2).1 +
              (ty.1 : ℝ) • ty.2.1) := by
          rw [hzform, smul_add, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
          module
        have hc_inv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc0.le
        have hc_sub : 0 ≤ 1 - c⁻¹ := sub_nonneg.mpr ((inv_le_one₀ hc0).2 hc)
        have hmem := hconv hx hz hc_sub hc_inv (by ring)
        exact ty.2.property (hp.symm ▸ hmem)⟩
      continuous_toFun := by fun_prop
      map_zero_left := by intro y; apply Subtype.ext; simp [ρ, j]
      map_one_left := by intro y; apply Subtype.ext; simp }
  let e : ContinuousMap.HomotopyEquiv ↥Aᶜ
      ↥(({x} : Set (EuclideanSpace ℝ (Fin d)))ᶜ) :=
    { toFun := j
      invFun := ρ
      left_inv := ⟨Hin⟩
      right_inv := ⟨Hout⟩ }
  refine ⟨e, ?_⟩
  rfl

theorem t00A04_hatcherConclusion_compact_convex_euclidean_aux_pointRestriction_bijective_aux_subspace
    (d : ℕ) (A : Set (EuclideanSpace ℝ (Fin d)))
    (hA : IsCompact A) (hconv : Convex ℝ A)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ A) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientRadialPair.subMap (ZMod 2)
        Aᶜ ({x} : Set (EuclideanSpace ℝ (Fin d)))ᶜ
        (ContinuousMap.id _) (by
          intro y hy
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq] using
            fun (hxy : y = x) ↦ hy (hxy ▸ hx))) n) := by
  obtain ⟨e, he⟩ :=
    t00A04_hatcherConclusion_compact_convex_euclidean_aux_pointRestriction_bijective_aux_complement
      d A hA hconv x hx
  change IsIso ((ConstructionTargets.CoefficientRadialPair.F (ZMod 2) n).map _)
  rw [show ConstructionTargets.SingularExcision.subspaceMap
      Aᶜ ({x} : Set (EuclideanSpace ℝ (Fin d)))ᶜ
      (ContinuousMap.id _) _ = TopCat.ofHom e.toFun by
    rw [he]
    rfl]
  rw [← ConstructionTargets.CoefficientRadialPair.homotopyIso_hom (ZMod 2) e n]
  infer_instance

theorem t00A04_hatcherConclusion_compact_convex_euclidean_aux_pointRestriction_bijective
    (d : ℕ) (A : Set (EuclideanSpace ℝ (Fin d)))
    (hA : IsCompact A) (hconv : Convex ℝ A)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ A) (n : ℕ) :
    Function.Bijective (t00A04_modTwo_pointRestriction
      (EuclideanSpace ℝ (Fin d)) A x hx n) := by
  let hmap : Set.MapsTo (ContinuousMap.id (EuclideanSpace ℝ (Fin d)))
      Aᶜ ({x} : Set (EuclideanSpace ℝ (Fin d)))ᶜ := by
    intro y hy
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq] using
      fun (hxy : y = x) ↦ hy (hxy ▸ hx)
  let i := ConstructionTargets.CoefficientCokernelComparison.comparisonIso
    (ZMod 2)
    (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2) Aᶜ)
    (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2) ({x} : Set _)ᶜ)
    (ConstructionTargets.CoefficientRadialPair.subMap (ZMod 2) Aᶜ ({x} : Set _)ᶜ
      (ContinuousMap.id _) hmap)
    (ConstructionTargets.CoefficientRadialPair.absoluteMap (ZMod 2) (ContinuousMap.id _))
    (ConstructionTargets.CoefficientRadialPair.square (ZMod 2) Aᶜ ({x} : Set _)ᶜ
      (ContinuousMap.id _) hmap)
    (fun j ↦
      t00A04_hatcherConclusion_compact_convex_euclidean_aux_pointRestriction_bijective_aux_subspace
        d A hA hconv x hx j)
    (fun j ↦ by
      change IsIso ((ConstructionTargets.CoefficientRadialPair.F (ZMod 2) j).map
        (TopCat.ofHom (ContinuousMap.id _)))
      simpa using (inferInstance : IsIso
        ((ConstructionTargets.CoefficientRadialPair.F (ZMod 2) j).map (𝟙 _)))) n
  change Function.Bijective (HomologicalComplex.homologyMap
    (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Aᶜ ({x} : Set _)ᶜ
      (ContinuousMap.id _) hmap) n)
  exact ConcreteCategory.bijective_of_isIso i.hom

/-- Euclidean point-local homology vanishes strictly above the dimension. -/
theorem t00A04_hatcherConclusion_compact_convex_euclidean_aux_point_vanish_aux_origin_high_aux_sphere
    (d k : ℕ) (hk : d ≤ k) (hk0 : k ≠ 0) :
    CategoryTheory.Limits.IsZero
      (ConstructionTargets.CoefficientContractiblePair.H (ZMod 2) k
        (TopCat.of (T02A06.euclideanUnitSphere d))) := by
  induction d generalizing k with
  | zero =>
      exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
        (ModuleCat (ZMod 2)) k (ModuleCat.of (ZMod 2) (ZMod 2))
          (TopCat.of (T02A06.euclideanUnitSphere 0)) hk0
  | succ d ih =>
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      by_cases hq0 : q = 0
      · subst q
        have hd : d = 0 := by omega
        subst d
        exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
          (ModuleCat (ZMod 2)) 1 (ModuleCat.of (ZMod 2) (ZMod 2))
            (TopCat.of (T02A06.euclideanUnitSphere 1)) (by decide)
      · have hs := ConstructionTargets.CoefficientSphereShift.sphereShift
          (ZMod 2) d q hq0
        exact (ih q (by omega) hq0).of_iso hs

theorem t00A04_hatcherConclusion_compact_convex_euclidean_aux_point_vanish_aux_origin_zero_aux_emptyRelative
    (i : ℕ) (hi : 0 < i) :
    CategoryTheory.Limits.IsZero
      ((ConstructionTargets.CoefficientRelativeSmall.relativeChains
        (ZMod 2) (∅ : Set (EuclideanSpace ℝ (Fin 0)))).homology i) := by
  let X := EuclideanSpace ℝ (Fin 0)
  let ciso : ConstructionTargets.CoefficientRelativeSmall.relativeChains
      (ZMod 2) (∅ : Set X) ≅
      ConstructionTargets.CoefficientH0.SingularChains (ZMod 2) (TopCat.of X) :=
    CategoryTheory.Limits.cokernelIsoOfEq
      (t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_zero_aux_emptyMap
        (ZMod 2) X) ≪≫
      CategoryTheory.Limits.cokernelZeroIsoTarget
  let hiso := asIso (HomologicalComplex.homologyMap ciso.hom i)
  exact (ConstructionTargets.CoefficientContractiblePair.higher_zero
    (ZMod 2) X i (by omega)).of_iso hiso

theorem t00A04_hatcherConclusion_compact_convex_euclidean_aux_point_vanish_aux_origin_zero
    (i : ℕ) (hi : 0 < i) :
    Subsingleton (t00A04_ModTwoLocalHomology
      (EuclideanSpace ℝ (Fin 0)) {0} i) := by
  have hpoint : ({0} : Set (EuclideanSpace ℝ (Fin 0))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_singleton_iff.mpr (Subsingleton.elim x 0)
  change Subsingleton
    (((ConstructionTargets.CoefficientRelativeSmall.relativeChains
      (ZMod 2) ({0} : Set (EuclideanSpace ℝ (Fin 0)))ᶜ).homology i : Type))
  rw [hpoint, Set.compl_univ]
  exact ModuleCat.subsingleton_of_isZero
    (t00A04_hatcherConclusion_compact_convex_euclidean_aux_point_vanish_aux_origin_zero_aux_emptyRelative
      i hi)

theorem t00A04_hatcherConclusion_compact_convex_euclidean_aux_point_vanish_aux_origin_one
    (i : ℕ) (hi : 1 < i) :
    Subsingleton (t00A04_ModTwoLocalHomology
      (EuclideanSpace ℝ (Fin 1)) {0} i) := by
  have hi0 : i - 1 ≠ 0 := by omega
  let e :=
    ConstructionTargets.CoefficientContractiblePair.contractibleConnectingIso
      (ZMod 2) (ConstructionTargets.CoefficientModelLocal.puncture 1) (i - 1) hi0 ≪≫
    ConstructionTargets.CoefficientModelLocal.radialIso (ZMod 2) 1 (i - 1)
  have hz :=
    t00A04_hatcherConclusion_compact_convex_euclidean_aux_point_vanish_aux_origin_high_aux_sphere
      1 (i - 1) (by omega) hi0
  have hzrel : CategoryTheory.Limits.IsZero
      ((ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2)
        (ConstructionTargets.CoefficientModelLocal.puncture 1)).homology i) := by
    have heq : i - 1 + 1 = i := by omega
    rw [← heq]
    exact hz.of_iso e
  change Subsingleton
    (((ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2)
      ({0} : Set (EuclideanSpace ℝ (Fin 1)))ᶜ).homology i : Type))
  exact ModuleCat.subsingleton_of_isZero hzrel

theorem t00A04_hatcherConclusion_compact_convex_euclidean_aux_point_vanish_aux_origin_high
    (m i : ℕ) (hi : m + 2 < i) :
    Subsingleton (t00A04_ModTwoLocalHomology
      (EuclideanSpace ℝ (Fin (m + 2))) {0} i) := by
  have hi0 : i - 1 ≠ 0 := by omega
  let e :=
    ConstructionTargets.CoefficientContractiblePair.contractibleConnectingIso
      (ZMod 2) (ConstructionTargets.CoefficientModelLocal.puncture (m + 2))
        (i - 1) hi0 ≪≫
    ConstructionTargets.CoefficientModelLocal.radialIso (ZMod 2) (m + 2) (i - 1)
  have hz :=
    t00A04_hatcherConclusion_compact_convex_euclidean_aux_point_vanish_aux_origin_high_aux_sphere
      (m + 2) (i - 1) (by omega) hi0
  have hzrel : CategoryTheory.Limits.IsZero
      ((ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2)
        (ConstructionTargets.CoefficientModelLocal.puncture (m + 2))).homology i) := by
    have heq : i - 1 + 1 = i := by omega
    rw [← heq]
    exact hz.of_iso e
  change Subsingleton
    (((ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2)
      ({0} : Set (EuclideanSpace ℝ (Fin (m + 2))))ᶜ).homology i : Type))
  exact ModuleCat.subsingleton_of_isZero hzrel

theorem t00A04_hatcherConclusion_compact_convex_euclidean_aux_point_vanish
    (d i : ℕ) (x : EuclideanSpace ℝ (Fin d)) (hi : d < i) :
    Subsingleton (t00A04_ModTwoLocalHomology
      (EuclideanSpace ℝ (Fin d)) {x} i) := by
  let e := (ConstructionTargets.CoefficientManifoldLocalComparison.translationIso
    (ZMod 2) x i).toLinearEquiv
  have h0 : Subsingleton (t00A04_ModTwoLocalHomology
      (EuclideanSpace ℝ (Fin d)) {0} i) := by
    rcases d with _ | _ | m
    · exact t00A04_hatcherConclusion_compact_convex_euclidean_aux_point_vanish_aux_origin_zero
        i hi
    · exact t00A04_hatcherConclusion_compact_convex_euclidean_aux_point_vanish_aux_origin_one
        i hi
    · exact t00A04_hatcherConclusion_compact_convex_euclidean_aux_point_vanish_aux_origin_high
        m i hi
  constructor
  intro a b
  apply e.injective
  exact h0.elim (e a) (e b)

/-- Top-dimensional Euclidean point-local mod-2 homology contains its
nonzero generator. -/
theorem t00A04_hatcherConclusion_compact_convex_euclidean_aux_point_nonzero
    (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ g : t00A04_ModTwoLocalHomology
      (EuclideanSpace ℝ (Fin d)) {x} d, g ≠ 0 := by
  have h0 : ∃ e : t00A04_ModTwoLocalHomology (EuclideanSpace ℝ (Fin d)) {0} d ≃ ZMod 2,
      e 0 = 0 := by
    rcases d with _ | _ | m
    · exact t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_zero
    · exact t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_one
    · exact t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_high m
  obtain ⟨e, e0⟩ := h0
  let i := (ConstructionTargets.CoefficientManifoldLocalComparison.translationIso
    (ZMod 2) x d).toLinearEquiv
  refine ⟨i.symm (e.symm 1), ?_⟩
  intro h
  have h1 : e.symm 1 = 0 := by
    have h2 : i (i.symm (e.symm 1)) = i 0 := congrArg i h
    rwa [LinearEquiv.apply_symm_apply, LinearEquiv.map_zero] at h2
  have : (1 : ZMod 2) = 0 := by
    rw [← e.apply_symm_apply 1, h1, e0]
  exact one_ne_zero this

theorem t00A04_hatcherConclusion_compact_convex_euclidean
    (d : ℕ) (A : Set (EuclideanSpace ℝ (Fin d)))
    (hA : IsCompact A) (hconv : Convex ℝ A) :
    t00A04_HatcherConclusion (EuclideanSpace ℝ (Fin d)) d A := by
  classical
  by_cases hne : A.Nonempty
  · obtain ⟨x, hx⟩ := hne
    have hbij (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ A) (n : ℕ) :=
      t00A04_hatcherConclusion_compact_convex_euclidean_aux_pointRestriction_bijective
        d A hA hconv y hy n
    constructor
    · intro i hi
      constructor
      intro a b
      apply (hbij x hx i).1
      exact (t00A04_hatcherConclusion_compact_convex_euclidean_aux_point_vanish
        d i x hi).elim _ _
    · obtain ⟨g, hg⟩ :=
        t00A04_hatcherConclusion_compact_convex_euclidean_aux_point_nonzero d x
      obtain ⟨c, hc⟩ := (hbij x hx d).2 g
      refine ⟨c, ?_⟩
      intro y hy hcy
      have hc0 : c = 0 := (hbij y hy d).1 (by simpa using hcy)
      apply hg
      rw [← hc, hc0]
      exact map_zero _
    · intro c
      constructor
      · intro hc y hy
        subst c
        exact map_zero _
      · intro hc
        apply (hbij x hx d).1
        simpa using hc x hx
  · have hA0 : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst A
    constructor
    · intro i _
      exact t00A04_hatcherConclusion_compact_convex_euclidean_aux_empty d i
    · refine ⟨0, ?_⟩
      intro x hx
      simp at hx
    · intro c
      constructor
      · intro _ x hx
        simp at hx
      · intro _
        exact (t00A04_hatcherConclusion_compact_convex_euclidean_aux_empty
          d d).elim _ _

/-- **Support functoriality.**  Restricting from `K` to `A` and then to a
point `x ∈ A` is restriction from `K` to `x`. -/
theorem t00A04_modTwo_pointRestriction_restrict
    (X : Type) [TopologicalSpace X] (A K : Set X) (h : A ⊆ K) (x : X) (hx : x ∈ A)
    (n : ℕ) (c : t00A04_ModTwoLocalHomology X K n) :
    t00A04_modTwo_pointRestriction X A x hx n (t00A04_modTwo_restrict X A K h n c) =
      t00A04_modTwo_pointRestriction X K x (h hx) n c := by
  change
    ((HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Kᶜ Aᶜ
          (ContinuousMap.id X) _) n ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Aᶜ ({x} : Set X)ᶜ
          (ContinuousMap.id X) _) n) c) = _
  rw [← HomologicalComplex.homologyMap_comp,
    ← ConstructionTargets.CoefficientPairNaturality.pair_comp]
  rfl

/-- **Support functoriality.**  Restriction along `A ⊆ B ⊆ K` composes. -/
theorem t00A04_modTwo_restrict_restrict
    (X : Type) [TopologicalSpace X] (A B K : Set X) (hAB : A ⊆ B) (hBK : B ⊆ K)
    (n : ℕ) (c : t00A04_ModTwoLocalHomology X K n) :
    t00A04_modTwo_restrict X A B hAB n (t00A04_modTwo_restrict X B K hBK n c) =
      t00A04_modTwo_restrict X A K (hAB.trans hBK) n c := by
  change
    ((HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Kᶜ Bᶜ
          (ContinuousMap.id X) _) n ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Bᶜ Aᶜ
          (ContinuousMap.id X) _) n) c) = _
  rw [← HomologicalComplex.homologyMap_comp,
    ← ConstructionTargets.CoefficientPairNaturality.pair_comp]
  rfl

/-- **Compact supports (Hatcher 3.27, step 3).**  A class supported on a
compact `A ⊆ ℝ^d` comes from a finite union of compact convex sets whose
interior contains `A`: a representing relative cycle has boundary with compact
support disjoint from `A`, so finitely many small closed balls around points of
`A` avoid it. -/
theorem t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport_aux_lift
    (d n : ℕ) (A : Set (EuclideanSpace ℝ (Fin d)))
    (c : t00A04_ModTwoLocalHomology (EuclideanSpace ℝ (Fin d)) A n) :
    ∃ (z : (ConstructionTargets.CoefficientH0.SingularChains (ZMod 2)
          (TopCat.of (EuclideanSpace ℝ (Fin d)))).X n)
      (q : (ConstructionTargets.CoefficientRelativeSmall.relativeChains
          (ZMod 2) Aᶜ).cycles n),
      (ConstructionTargets.CoefficientRelativeSmall.relativeChains
          (ZMod 2) Aᶜ).iCycles n q =
        (cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap
          (ZMod 2) Aᶜ)).f n z ∧
      (ConstructionTargets.CoefficientRelativeSmall.relativeChains
          (ZMod 2) Aᶜ).homologyπ n q = c := by
  let Q := ConstructionTargets.CoefficientRelativeSmall.relativeChains
    (ZMod 2) Aᶜ
  obtain ⟨q, hqc⟩ := (ModuleCat.epi_iff_surjective (Q.homologyπ n)).mp
    inferInstance c
  let p := cokernel.π
    (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2) Aᶜ)
  haveI : Epi p := by
    dsimp only [p, cokernel.π]
    infer_instance
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (p.f n)).mp inferInstance
    (Q.iCycles n q)
  exact ⟨z, q, hz.symm, hqc⟩

theorem t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport_aux_finite_aux_boundary
    (d n : ℕ) (A : Set (EuclideanSpace ℝ (Fin d)))
    (z : (ConstructionTargets.CoefficientH0.SingularChains (ZMod 2)
      (TopCat.of (EuclideanSpace ℝ (Fin d)))).X n)
    (qA : (ConstructionTargets.CoefficientRelativeSmall.relativeChains
      (ZMod 2) Aᶜ).cycles n)
    (hqA : (ConstructionTargets.CoefficientRelativeSmall.relativeChains
        (ZMod 2) Aᶜ).iCycles n qA =
      (cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap
        (ZMod 2) Aᶜ)).f n z) :
    (ConstructionTargets.CoefficientH0.SingularChains (ZMod 2)
        (TopCat.of (EuclideanSpace ℝ (Fin d)))).d n (n - 1) z ∈
      Set.range ((ConstructionTargets.CoefficientRelativeSmall.subspaceMap
        (ZMod 2) Aᶜ).f (n - 1)) := by
  let p := cokernel.π
    (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2) Aᶜ)
  have hzero : p.f (n - 1)
      ((ConstructionTargets.CoefficientH0.SingularChains (ZMod 2)
        (TopCat.of (EuclideanSpace ℝ (Fin d)))).d n (n - 1) z) = 0 := by
    have hcomm := ConcreteCategory.congr_hom (p.comm n (n - 1)) z
    have hcycle := ConcreteCategory.congr_hom
      ((ConstructionTargets.CoefficientRelativeSmall.relativeChains
        (ZMod 2) Aᶜ).iCycles_d n (n - 1)) qA
    simp only [ConcreteCategory.comp_apply] at hcomm hcycle
    rw [← hcomm, ← hqA]
    exact hcycle
  have hex := (HomologicalComplex.exact_iff_degreewise_exact _).mp
    (ConstructionTargets.CoefficientCokernelComparison.cokernelShortComplex_shortExact
      (ZMod 2)
      (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2) Aᶜ)).exact
      (n - 1)
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex _ hzero
  exact ⟨w, hw⟩

theorem t00A04_simplex_mem_range_subspace_iff {X : Type} [TopologicalSpace X] (S : Set X) (m : ℕ)
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk m))) :
    τ ∈ Set.range ((TopCat.toSSet.map (ConstructionTargets.SingularHomologyConcrete.subspaceInclusion S)).app
        (Opposite.op (SimplexCategory.mk m))) ↔
      Set.range ((TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op (SimplexCategory.mk m))) τ) ⊆ S := by
  constructor
  · rintro ⟨σA, hA⟩ _ ⟨t, rfl⟩
    have := congrArg
      (fun τ ↦ (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op (SimplexCategory.mk m))).toFun τ t) hA
    change
      (((TopCat.toSSetObjEquiv (TopCat.of S) (Opposite.op (SimplexCategory.mk m))).toFun σA) t).1 = _ at this
    change _ ∈ S
    change _ = (((TopCat.toSSetObjEquiv (TopCat.of X) _)) τ) t at this
    rw [← this]
    exact (((TopCat.toSSetObjEquiv (TopCat.of S) _).toFun σA) t).2
  · intro h
    let f := (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op (SimplexCategory.mk m))) τ
    have hf : ∀ t, f t ∈ S := fun t ↦ h ⟨t, rfl⟩
    let g : C(stdSimplex ℝ (Fin (m + 1)), S) :=
      ⟨fun t ↦ ⟨f t, hf t⟩, f.continuous.subtype_mk hf⟩
    refine ⟨(TopCat.toSSetObjEquiv (TopCat.of S) (Opposite.op (SimplexCategory.mk m))).symm g, ?_⟩
    apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
    ext t
    rfl

theorem t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport_aux_finite_aux_support_aux_carrier
    (d m : ℕ) (S : Set (EuclideanSpace ℝ (Fin d)))
    (x : (ConstructionTargets.CoefficientH0.SingularChains (ZMod 2)
      (TopCat.of (EuclideanSpace ℝ (Fin d)))).X m)
    (hx : x ∈ Set.range ((ConstructionTargets.CoefficientRelativeSmall.subspaceMap
      (ZMod 2) S).f m)) :
    ∃ F : Finset C(stdSimplex ℝ (Fin (m + 1)), EuclideanSpace ℝ (Fin d)),
      (∀ σ ∈ F, Set.range σ ⊆ S) ∧
      x ∈ Set.range ((ConstructionTargets.CoefficientRelativeSmall.subspaceMap
        (ZMod 2) (⋃ σ ∈ F, Set.range σ)).f m) := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let n : SimplexCategoryᵒᵖ := Opposite.op (SimplexCategory.mk m)
  let e := ConstructionTargets.CoefficientSigmaConstFinsuppComparison.sigmaConstFinsuppIso
    (ZMod 2) ((TopCat.toSSet.obj (TopCat.of E)).obj n)
  let eqv := TopCat.toSSetObjEquiv (TopCat.of E) n
  have hrange (A : Set E) :
      Submodule.map e.hom.hom
          (LinearMap.range ((ConstructionTargets.CoefficientRelativeSmall.subspaceMap
            (ZMod 2) A).f m).hom) =
        Finsupp.supported (ZMod 2) (ZMod 2) {τ | Set.range (eqv τ) ⊆ A} := by
    refine (ConstructionTargets.CoefficientSimplicialChainFinsuppRange.chainsMap_component_range_finsupp
      (ZMod 2) (TopCat.toSSet.map
        (ConstructionTargets.SingularHomologyConcrete.subspaceInclusion A)) m).trans ?_
    rw [ConstructionTargets.CoefficientFinsuppRangeLattice.range_lmapDomain_eq_supported_range]
    congr 1
    ext τ
    exact t00A04_simplex_mem_range_subspace_iff A m τ
  have hx' : e.hom x ∈ Finsupp.supported (ZMod 2) (ZMod 2) {τ | Set.range (eqv τ) ⊆ S} := by
    rw [← hrange S]
    obtain ⟨y, rfl⟩ := hx
    exact ⟨_, ⟨y, rfl⟩, rfl⟩
  refine ⟨(e.hom x).support.image eqv, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hσ
    exact hx' hτ
  · have hK : e.hom x ∈ Finsupp.supported (ZMod 2) (ZMod 2)
        {τ | Set.range (eqv τ) ⊆ ⋃ σ ∈ (e.hom x).support.image eqv, Set.range σ} := by
      intro τ hτ y hy
      simp only [Set.mem_iUnion]
      exact ⟨eqv τ, Finset.mem_image_of_mem _ hτ, hy⟩
    rw [← hrange] at hK
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ := hK
    refine ⟨y, ?_⟩
    have h2 := congrArg (ConcreteCategory.hom e.inv) hy
    rwa [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply] at h2

theorem t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport_aux_finite_aux_support_aux_geometry
    (d m : ℕ) (S : Set (EuclideanSpace ℝ (Fin d)))
    (F : Finset C(stdSimplex ℝ (Fin (m + 1)), EuclideanSpace ℝ (Fin d)))
    (hF : ∀ σ ∈ F, Set.range σ ⊆ S) :
    (⋃ σ ∈ F, Set.range σ) ⊆ S ∧
      IsCompact (⋃ σ ∈ F, Set.range σ) := by
  constructor
  · intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨σ, hσ⟩ := hy
    obtain ⟨hσF, hyσ⟩ := hσ
    exact hF σ hσF hyσ
  · apply Set.Finite.isCompact_biUnion
    · exact F.finite_toSet
    · intro σ hσ
      exact isCompact_range σ.continuous

theorem t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport_aux_finite_aux_support
    (d n : ℕ) (A : Set (EuclideanSpace ℝ (Fin d)))
    (x : (ConstructionTargets.CoefficientH0.SingularChains (ZMod 2)
      (TopCat.of (EuclideanSpace ℝ (Fin d)))).X (n - 1))
    (hx : x ∈ Set.range ((ConstructionTargets.CoefficientRelativeSmall.subspaceMap
      (ZMod 2) Aᶜ).f (n - 1))) :
    ∃ K : Set (EuclideanSpace ℝ (Fin d)), K ⊆ Aᶜ ∧ IsCompact K ∧
      x ∈ Set.range ((ConstructionTargets.CoefficientRelativeSmall.subspaceMap
        (ZMod 2) Kᶜᶜ).f (n - 1)) := by
  obtain ⟨F, hFS, hxF⟩ :=
    t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport_aux_finite_aux_support_aux_carrier
      d (n - 1) Aᶜ x hx
  let K : Set (EuclideanSpace ℝ (Fin d)) := ⋃ σ ∈ F, Set.range σ
  have hgeom :=
    t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport_aux_finite_aux_support_aux_geometry
      d (n - 1) Aᶜ F hFS
  refine ⟨K, hgeom.1, hgeom.2, ?_⟩
  rw [compl_compl]
  exact hxF

theorem t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport_aux_finite_aux_cycle
    (d n : ℕ) (K : Set (EuclideanSpace ℝ (Fin d)))
    (z : (ConstructionTargets.CoefficientH0.SingularChains (ZMod 2)
      (TopCat.of (EuclideanSpace ℝ (Fin d)))).X n)
    (hz : (ConstructionTargets.CoefficientH0.SingularChains (ZMod 2)
        (TopCat.of (EuclideanSpace ℝ (Fin d)))).d n (n - 1) z ∈
      Set.range ((ConstructionTargets.CoefficientRelativeSmall.subspaceMap
        (ZMod 2) Kᶜᶜ).f (n - 1))) :
    ∃ qK : (ConstructionTargets.CoefficientRelativeSmall.relativeChains
        (ZMod 2) Kᶜᶜ).cycles n,
      (ConstructionTargets.CoefficientRelativeSmall.relativeChains
          (ZMod 2) Kᶜᶜ).iCycles n qK =
        (cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap
          (ZMod 2) Kᶜᶜ)).f n z := by
  let C := ConstructionTargets.CoefficientH0.SingularChains (ZMod 2)
    (TopCat.of (EuclideanSpace ℝ (Fin d)))
  let Q := ConstructionTargets.CoefficientRelativeSmall.relativeChains
    (ZMod 2) Kᶜᶜ
  let p := cokernel.π
    (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2) Kᶜᶜ)
  have hpd : p.f (n - 1) (C.d n (n - 1) z) = 0 := by
    obtain ⟨w, hw⟩ := hz
    rw [← hw]
    change p.f (n - 1)
      ((ConstructionTargets.CoefficientRelativeSmall.subspaceMap
        (ZMod 2) Kᶜᶜ).f (n - 1) w) = 0
    rw [← ConcreteCategory.comp_apply]
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.f (n - 1))
        (cokernel.condition
          (ConstructionTargets.CoefficientRelativeSmall.subspaceMap
            (ZMod 2) Kᶜᶜ))) w
  have hcycle : Q.d n (n - 1) (p.f n z) = 0 := by
    have hcomm := ConcreteCategory.congr_hom (p.comm n (n - 1)) z
    simp only [ConcreteCategory.comp_apply] at hcomm
    change Q.d n (n - 1) (p.f n z) = p.f (n - 1) (C.d n (n - 1) z) at hcomm
    exact hcomm.trans hpd
  let xhom : ModuleCat.of (ZMod 2) (ZMod 2) ⟶ Q.X n :=
    ConstructionTargets.CoefficientSmallComparison.elementHom (ZMod 2) (p.f n z)
  have xhomd : xhom ≫ Q.d n (n - 1) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (Q.d n (n - 1)).hom (r • p.f n z) = 0
    calc
      (Q.d n (n - 1)).hom (r • p.f n z) =
          r • (Q.d n (n - 1)).hom (p.f n z) :=
        (Q.d n (n - 1)).hom.map_smul r (p.f n z)
      _ = r • 0 := congrArg (r • ·) hcycle
      _ = 0 := smul_zero r
  have hnext : (ComplexShape.down ℕ).next n = n - 1 := by
    cases n with
    | zero => exact ChainComplex.next_nat_zero
    | succ n => simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
        ChainComplex.next_nat_succ n
  refine ⟨Q.liftCycles xhom (n - 1) hnext xhomd 1, ?_⟩
  have hi := ConcreteCategory.congr_hom
    (Q.liftCycles_i xhom (n - 1) hnext xhomd) 1
  exact hi.trans
    (ConstructionTargets.CoefficientSmallComparison.elementHom_one
      (ZMod 2) (p.f n z))

theorem t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport_aux_finite
    (d n : ℕ) (A : Set (EuclideanSpace ℝ (Fin d)))
    (z : (ConstructionTargets.CoefficientH0.SingularChains (ZMod 2)
      (TopCat.of (EuclideanSpace ℝ (Fin d)))).X n)
    (qA : (ConstructionTargets.CoefficientRelativeSmall.relativeChains
      (ZMod 2) Aᶜ).cycles n)
    (hqA : (ConstructionTargets.CoefficientRelativeSmall.relativeChains
        (ZMod 2) Aᶜ).iCycles n qA =
      (cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap
        (ZMod 2) Aᶜ)).f n z) :
    ∃ K : Set (EuclideanSpace ℝ (Fin d)), K ⊆ Aᶜ ∧ IsCompact K ∧
      ∃ qK : (ConstructionTargets.CoefficientRelativeSmall.relativeChains
          (ZMod 2) Kᶜᶜ).cycles n,
        (ConstructionTargets.CoefficientRelativeSmall.relativeChains
            (ZMod 2) Kᶜᶜ).iCycles n qK =
          (cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap
            (ZMod 2) Kᶜᶜ)).f n z := by
  have hb :=
    t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport_aux_finite_aux_boundary
      d n A z qA hqA
  obtain ⟨K, hKA, hKc, hK⟩ :=
    t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport_aux_finite_aux_support
      d n A _ hb
  exact ⟨K, hKA, hKc,
    t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport_aux_finite_aux_cycle
      d n K z hK⟩

theorem t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport_aux_descend
    (d n : ℕ) (A K : Set (EuclideanSpace ℝ (Fin d))) (hKA : K ⊆ Aᶜ)
    (z : (ConstructionTargets.CoefficientH0.SingularChains (ZMod 2)
      (TopCat.of (EuclideanSpace ℝ (Fin d)))).X n)
    (qA : (ConstructionTargets.CoefficientRelativeSmall.relativeChains
      (ZMod 2) Aᶜ).cycles n)
    (qK : (ConstructionTargets.CoefficientRelativeSmall.relativeChains
      (ZMod 2) Kᶜᶜ).cycles n)
    (hqA : (ConstructionTargets.CoefficientRelativeSmall.relativeChains
        (ZMod 2) Aᶜ).iCycles n qA =
      (cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap
        (ZMod 2) Aᶜ)).f n z)
    (hqK : (ConstructionTargets.CoefficientRelativeSmall.relativeChains
        (ZMod 2) Kᶜᶜ).iCycles n qK =
      (cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap
        (ZMod 2) Kᶜᶜ)).f n z) :
    t00A04_modTwo_restrict _ A Kᶜ
        (fun x hx hxK ↦ (hKA hxK) hx) n
        ((ConstructionTargets.CoefficientRelativeSmall.relativeChains
            (ZMod 2) Kᶜᶜ).homologyπ n qK) =
      (ConstructionTargets.CoefficientRelativeSmall.relativeChains
          (ZMod 2) Aᶜ).homologyπ n qA := by
  let CK := ConstructionTargets.CoefficientRelativeSmall.relativeChains
    (ZMod 2) Kᶜᶜ
  let CA := ConstructionTargets.CoefficientRelativeSmall.relativeChains
    (ZMod 2) Aᶜ
  let F : CK ⟶ CA :=
    ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Kᶜᶜ Aᶜ
      (ContinuousMap.id _) (fun x hx hxA ↦ (hKA (by simpa using hx)) hxA)
  have hcycles : HomologicalComplex.cyclesMap F n qK = qA := by
    apply (ModuleCat.mono_iff_injective (CA.iCycles n)).mp inferInstance
    have hci := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i F n) qK
    simp only [ConcreteCategory.comp_apply] at hci
    rw [hci, hqK, hqA]
    have hp := ConcreteCategory.congr_hom
      (ConstructionTargets.CoefficientRadialPair.projection_degree
        (ZMod 2) Kᶜᶜ Aᶜ (ContinuousMap.id _)
          (fun x hx hxA ↦ (hKA (by simpa using hx)) hxA) n) z
    simp only [ConcreteCategory.comp_apply] at hp
    have hid :
        (ConstructionTargets.CoefficientRadialPair.absoluteMap (ZMod 2)
          (ContinuousMap.id _)).f n z = z := by
      change (((AlgebraicTopology.singularChainComplexFunctor
        (ModuleCat (ZMod 2))).obj (ModuleCat.of (ZMod 2) (ZMod 2))).map
          (𝟙 (TopCat.of (EuclideanSpace ℝ (Fin d))))).f n z = z
      have he := congrArg (fun q ↦ q.f n)
        (((AlgebraicTopology.singularChainComplexFunctor
          (ModuleCat (ZMod 2))).obj (ModuleCat.of (ZMod 2) (ZMod 2))).map_id
            (TopCat.of (EuclideanSpace ℝ (Fin d))))
      exact ConcreteCategory.congr_hom he z
    change
      (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Kᶜᶜ Aᶜ
        (ContinuousMap.id _) (fun x hx hxA ↦ (hKA (by simpa using hx)) hxA)).f n
          ((cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap
            (ZMod 2) Kᶜᶜ)).f n z) = _
    calc
      _ = ((ConstructionTargets.CoefficientRadialPair.absoluteMap (ZMod 2)
              (ContinuousMap.id _)).f n ≫
            (cokernel.π (ConstructionTargets.CoefficientRelativeSmall.subspaceMap
              (ZMod 2) Aᶜ)).f n) z := hp
      _ = _ := by
        rw [ConcreteCategory.comp_apply, hid]
        rfl
  have hn := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality F n) qK
  simpa only [ConcreteCategory.comp_apply, hcycles] using hn

theorem t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport
    (d n : ℕ) (A : Set (EuclideanSpace ℝ (Fin d)))
    (c : t00A04_ModTwoLocalHomology (EuclideanSpace ℝ (Fin d)) A n) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin d))) (hKA : K ⊆ Aᶜ), IsCompact K ∧
      ∃ (cK : t00A04_ModTwoLocalHomology
          (EuclideanSpace ℝ (Fin d)) Kᶜ n),
        t00A04_modTwo_restrict _ A Kᶜ
          (fun x hx hxK ↦ (hKA hxK) hx) n cK = c := by
  obtain ⟨z, qA, hqA, hzc⟩ :=
    t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport_aux_lift d n A c
  obtain ⟨K, hKA, hK, qK, hqK⟩ :=
    t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport_aux_finite
      d n A z qA hqA
  refine ⟨K, hKA, hK, (ConstructionTargets.CoefficientRelativeSmall.relativeChains
    (ZMod 2) Kᶜᶜ).homologyπ n qK, ?_⟩
  rw [t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport_aux_descend
    d n A K hKA z qA qK hqA hqK]
  exact hzc

theorem t00A04_compactSupport_lift_aux_open
    (d n : ℕ) (A : Set (EuclideanSpace ℝ (Fin d)))
    (c : t00A04_ModTwoLocalHomology (EuclideanSpace ℝ (Fin d)) A n) :
    ∃ (W : Set (EuclideanSpace ℝ (Fin d))) (_ : IsOpen W) (_ : A ⊆ W)
      (cW : t00A04_ModTwoLocalHomology (EuclideanSpace ℝ (Fin d)) W n),
      t00A04_modTwo_restrict _ A W ‹A ⊆ W› n cW = c := by
  obtain ⟨K, hKA, hK, cK, hcK⟩ :=
    t00A04_compactSupport_lift_aux_open_aux_compactBoundarySupport d n A c
  refine ⟨Kᶜ, hK.isClosed.isOpen_compl, ?_, cK, ?_⟩
  · intro x hx hxK
    exact (hKA hxK) hx
  · exact hcK

theorem t00A04_compactSupport_lift_aux_finite_convex_neighborhood
    (d : ℕ) (A W : Set (EuclideanSpace ℝ (Fin d)))
    (hA : IsCompact A) (hW : IsOpen W) (hAW : A ⊆ W) :
    ∃ (s : Finset (Set (EuclideanSpace ℝ (Fin d))))
      (_ : ∀ B ∈ s, IsCompact B ∧ Convex ℝ B)
      (_ : A ⊆ interior (⋃ B ∈ s, B)),
      (⋃ B ∈ s, B) ⊆ W := by
  classical
  choose r hrpos hrW using fun a : A ↦
    (Metric.isOpen_iff.mp hW a (hAW a.property))
  let U : A → Set (EuclideanSpace ℝ (Fin d)) := fun a ↦ Metric.ball a (r a / 2)
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover U (fun a ↦ Metric.isOpen_ball)
    (fun x hx ↦ Set.mem_iUnion.mpr
      ⟨⟨x, hx⟩, by simp only [U, Metric.mem_ball, dist_self]; linarith [hrpos ⟨x, hx⟩]⟩)
  let f : A → Set (EuclideanSpace ℝ (Fin d)) :=
    fun a ↦ Metric.closedBall a (r a / 2)
  let s := t.image f
  refine ⟨s, ?_, ?_, ?_⟩
  · intro B hB
    rcases Finset.mem_image.mp hB with ⟨a, ha, rfl⟩
    exact ⟨isCompact_closedBall _ _, convex_closedBall _ _⟩
  · intro x hx
    have hxt : x ∈ ⋃ a ∈ t, U a := ht hx
    simp only [Set.mem_iUnion] at hxt
    rcases hxt with ⟨a, ha, hxa⟩
    apply mem_interior_iff_mem_nhds.mpr
    refine Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hxa) ?_
    intro y hy
    apply Set.mem_iUnion.mpr
    refine ⟨f a, ?_⟩
    apply Set.mem_iUnion.mpr
    refine ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    exact Metric.ball_subset_closedBall hy
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨B, hx⟩
    rcases hx with ⟨hBs, hxB⟩
    rcases Finset.mem_image.mp hBs with ⟨a, ha, rfl⟩
    apply hrW a
    exact Metric.closedBall_subset_ball (by linarith [hrpos a]) hxB

theorem t00A04_compactSupport_lift
    (d n : ℕ) (A : Set (EuclideanSpace ℝ (Fin d))) (hA : IsCompact A)
    (c : t00A04_ModTwoLocalHomology (EuclideanSpace ℝ (Fin d)) A n) :
    ∃ (s : Finset (Set (EuclideanSpace ℝ (Fin d))))
      (_ : ∀ B ∈ s, IsCompact B ∧ Convex ℝ B)
      (_ : A ⊆ interior (⋃ B ∈ s, B))
      (c' : t00A04_ModTwoLocalHomology (EuclideanSpace ℝ (Fin d)) (⋃ B ∈ s, B) n),
      t00A04_modTwo_restrict _ A (⋃ B ∈ s, B)
        ((‹A ⊆ interior (⋃ B ∈ s, B)›).trans interior_subset) n c' = c := by
  obtain ⟨W, hW, hAW, cW, hcW⟩ :=
    t00A04_compactSupport_lift_aux_open d n A c
  obtain ⟨s, hs, hAint, hsW⟩ :=
    t00A04_compactSupport_lift_aux_finite_convex_neighborhood d A W hA hW hAW
  let c' := t00A04_modTwo_restrict _ (⋃ B ∈ s, B) W hsW n cW
  refine ⟨s, hs, hAint, c', ?_⟩
  rw [t00A04_modTwo_restrict_restrict]
  exact hcW

/-- **F2e.** Finite unions of compact convex Euclidean sets satisfy Hatcher's
conclusion.  F1 and F2 are passed in explicitly. -/
theorem t00A04_hatcherConclusion_finite_union_convex_euclidean_aux
    (d : ℕ)
    (hconv : ∀ A : Set (EuclideanSpace ℝ (Fin d)), IsCompact A → Convex ℝ A →
      t00A04_HatcherConclusion (EuclideanSpace ℝ (Fin d)) d A)
    (hunion : ∀ (A B : Set (EuclideanSpace ℝ (Fin d))), IsCompact A → IsCompact B →
      t00A04_HatcherConclusion _ d A → t00A04_HatcherConclusion _ d B →
      t00A04_HatcherConclusion _ d (A ∩ B) →
      t00A04_HatcherConclusion _ d (A ∪ B))
    {α : Type*} (s : Finset α)
    (f : α → Set (EuclideanSpace ℝ (Fin d)))
    (hs : ∀ a ∈ s, IsCompact (f a) ∧ Convex ℝ (f a)) :
    t00A04_HatcherConclusion _ d (⋃ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
      simpa using hconv (∅ : Set (EuclideanSpace ℝ (Fin d)))
        isCompact_empty convex_empty
  | @insert a s ha ih =>
      have has : IsCompact (f a) ∧ Convex ℝ (f a) := hs a (Finset.mem_insert_self a s)
      have htail : ∀ b ∈ s, IsCompact (f b) ∧ Convex ℝ (f b) := by
        intro b hb
        exact hs b (Finset.mem_insert_of_mem hb)
      have htailConclusion := ih f htail
      have htailCompact : IsCompact (⋃ b ∈ s, f b) := by
        exact Set.Finite.isCompact_biUnion (s.finite_toSet) (fun b hb ↦ (htail b hb).1)
      have hinter : ∀ b ∈ s,
          IsCompact (f a ∩ f b) ∧ Convex ℝ (f a ∩ f b) := by
        intro b hb
        exact ⟨has.1.inter_right (htail b hb).1.isClosed,
          has.2.inter (htail b hb).2⟩
      have hinterConclusion := ih (fun b ↦ f a ∩ f b) hinter
      have hu := hunion (f a) (⋃ b ∈ s, f b) has.1 htailCompact
        (hconv (f a) has.1 has.2) htailConclusion
      rw [Set.inter_iUnion₂] at hu
      exact (by simpa [ha] using hu hinterConclusion)

theorem t00A04_hatcherConclusion_finite_union_convex_euclidean
    (d : ℕ)
    (hconv : ∀ A : Set (EuclideanSpace ℝ (Fin d)), IsCompact A → Convex ℝ A →
      t00A04_HatcherConclusion (EuclideanSpace ℝ (Fin d)) d A)
    (hunion : ∀ (A B : Set (EuclideanSpace ℝ (Fin d))), IsCompact A → IsCompact B →
      t00A04_HatcherConclusion _ d A → t00A04_HatcherConclusion _ d B →
      t00A04_HatcherConclusion _ d (A ∩ B) →
      t00A04_HatcherConclusion _ d (A ∪ B))
    (s : Finset (Set (EuclideanSpace ℝ (Fin d))))
    (hs : ∀ A ∈ s, IsCompact A ∧ Convex ℝ A) :
    t00A04_HatcherConclusion _ d (⋃ A ∈ s, A) := by
  exact t00A04_hatcherConclusion_finite_union_convex_euclidean_aux
    d hconv hunion s id (by simpa using hs)

/-- Radial comparison of the punctured ambient space with the complement
of a positive-radius closed ball makes restriction to its centre injective. -/
theorem t00A04_hatcherConclusion_compact_euclidean_aux_ball_center_injective
    (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : 0 < r) :
    Function.Injective (t00A04_modTwo_pointRestriction _ (Metric.closedBall x r)
      x (Metric.mem_closedBall_self hr.le) d) :=
  (t00A04_hatcherConclusion_compact_convex_euclidean_aux_pointRestriction_bijective d
    (Metric.closedBall x r) (isCompact_closedBall x r) (convex_closedBall x r) x
    (Metric.mem_closedBall_self hr.le) d).1

/-- A zero point restriction persists on a closed ball about an interior point.
This is the local radial/excision calculation for a closed ball. -/
theorem t00A04_hatcherConclusion_compact_euclidean_aux_zero_ball
    (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d)))
    (c : t00A04_ModTwoLocalHomology _ K d)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ interior K)
    (hz : t00A04_modTwo_pointRestriction _ K x (interior_subset hx) d c = 0) :
    ∃ (r : ℝ) (_ : 0 < r) (hsub : Metric.closedBall x r ⊆ K),
      ∀ (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ Metric.closedBall x r),
        t00A04_modTwo_pointRestriction _ K y (hsub hy) d c = 0 := by
  obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hr : 0 < ε / 2 := by linarith
  have hsub : Metric.closedBall x (ε / 2) ⊆ K :=
    (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans
      (hεK.trans interior_subset)
  let b := t00A04_modTwo_restrict _ (Metric.closedBall x (ε / 2)) K hsub d c
  have hb : b = 0 := by
    apply t00A04_hatcherConclusion_compact_euclidean_aux_ball_center_injective
      d x (ε / 2) hr
    rw [map_zero]
    dsimp [b]
    rw [t00A04_modTwo_pointRestriction_restrict]
    exact hz
  refine ⟨ε / 2, hr, hsub, ?_⟩
  intro y hy
  rw [← t00A04_modTwo_pointRestriction_restrict _ (Metric.closedBall x (ε / 2))
    K hsub y hy]
  change t00A04_modTwo_pointRestriction _ _ y hy d b = 0
  rw [hb]
  exact map_zero _

/-- A finite union of zero balls covers the compact support. -/
theorem t00A04_hatcherConclusion_compact_euclidean_aux_zero_cover
    (d : ℕ) (A K : Set (EuclideanSpace ℝ (Fin d))) (hA : IsCompact A)
    (hAK : A ⊆ interior K) (c : t00A04_ModTwoLocalHomology _ K d)
    (hz : ∀ (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ A),
      t00A04_modTwo_pointRestriction _ K x (interior_subset (hAK hx)) d c = 0) :
    ∃ (s : Finset (Set (EuclideanSpace ℝ (Fin d))))
      (_ : ∀ B ∈ s, IsCompact B ∧ Convex ℝ B)
      (_ : A ⊆ ⋃ B ∈ s, B) (hsub : (⋃ B ∈ s, B) ⊆ K),
      ∀ (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ ⋃ B ∈ s, B),
        t00A04_modTwo_pointRestriction _ K x (hsub hx) d c = 0 := by
  classical
  have hb := fun x : A ↦
    t00A04_hatcherConclusion_compact_euclidean_aux_zero_ball d K c x
      (hAK x.property) (hz x x.property)
  choose r hr hsub hzero using hb
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover
    (fun x : A ↦ Metric.ball (x : EuclideanSpace ℝ (Fin d)) (r x))
    (fun _ ↦ Metric.isOpen_ball) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩)
  let s := t.image (fun x : A ↦ Metric.closedBall (x : EuclideanSpace ℝ (Fin d)) (r x))
  have hs : ∀ B ∈ s, IsCompact B ∧ Convex ℝ B := by
    intro B hB
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hB
    exact ⟨isCompact_closedBall _ _, convex_closedBall _ _⟩
  have hcover : A ⊆ ⋃ B ∈ s, B := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion₂.mpr ⟨_, Finset.mem_image.mpr ⟨y, hy, rfl⟩,
      Metric.ball_subset_closedBall hxy⟩
  have hK : (⋃ B ∈ s, B) ⊆ K := by
    intro x hx
    obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hB
    exact hsub y hxB
  refine ⟨s, hs, hcover, hK, ?_⟩
  intro x hx
  obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hB
  exact hzero y x hxB

/-- **LIBRARY F3e.** Hatcher's relative-cycle argument extends the Euclidean
result from finite unions of compact convex sets to every compact set. -/
theorem t00A04_hatcherConclusion_compact_euclidean
    (d : ℕ)
    (hfinite : ∀ (s : Finset (Set (EuclideanSpace ℝ (Fin d)))),
      (∀ A ∈ s, IsCompact A ∧ Convex ℝ A) →
      t00A04_HatcherConclusion _ d (⋃ A ∈ s, A))
    (A : Set (EuclideanSpace ℝ (Fin d))) (hA : IsCompact A) :
    t00A04_HatcherConclusion _ d A := by
  classical
  constructor
  · intro n hn
    have hall (c : t00A04_ModTwoLocalHomology _ A n) : c = 0 := by
      obtain ⟨s, hs, hAs, c', hc'⟩ := t00A04_compactSupport_lift d n A hA c
      have hc0 : c' = 0 := ((hfinite s hs).vanish_above n hn).elim _ _
      rw [← hc', hc0]
      exact map_zero _
    exact ⟨fun a b ↦ (hall a).trans (hall b).symm⟩
  · obtain ⟨r, hAr⟩ := hA.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
    obtain ⟨c, hc⟩ := (t00A04_hatcherConclusion_compact_convex_euclidean d
      (Metric.closedBall 0 r) (isCompact_closedBall _ _) (convex_closedBall _ _)).exists_everywhere_nonzero
    refine ⟨t00A04_modTwo_restrict _ A _ hAr d c, ?_⟩
    intro x hx
    rw [t00A04_modTwo_pointRestriction_restrict]
    exact hc x _
  · intro c
    constructor
    · intro hc x hx
      rw [hc]
      exact map_zero _
    · intro hz
      obtain ⟨s, hs, hAs, c', hc'⟩ := t00A04_compactSupport_lift d d A hA c
      have hpoint : ∀ (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ A),
          t00A04_modTwo_pointRestriction _ (⋃ B ∈ s, B) x
            (interior_subset (hAs hx)) d c' = 0 := by
        intro x hx
        rw [← t00A04_modTwo_pointRestriction_restrict _ A _
          (hAs.trans interior_subset) x hx, hc']
        exact hz x hx
      obtain ⟨t, ht, hAt, htK, hzt⟩ :=
        t00A04_hatcherConclusion_compact_euclidean_aux_zero_cover d A _ hA hAs c' hpoint
      have ht0 : t00A04_modTwo_restrict _ (⋃ B ∈ t, B) _ htK d c' = 0 := by
        apply ((hfinite t ht).eq_zero_iff_pointwise _).mpr
        intro x hx
        rw [t00A04_modTwo_pointRestriction_restrict]
        exact hzt x hx
      rw [← hc', ← t00A04_modTwo_restrict_restrict _ A (⋃ B ∈ t, B) _ hAt htK,
        ht0]
      exact map_zero _

/-- **LIBRARY (chart transport).** The all-compact Euclidean result transported
to an arbitrary compact subset contained in one chart source. -/
theorem t00A04_hatcherConclusion_compact_in_chart_aux_model
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (heuclid : ∀ (d : ℕ) (A : Set (EuclideanSpace ℝ (Fin d))), IsCompact A →
      t00A04_HatcherConclusion _ d A)
    (A : Set E) (hA : IsCompact A) :
    t00A04_HatcherConclusion E (Module.finrank ℝ E) A := by
  classical
  let d := Module.finrank ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [d])
  let B : Set (EuclideanSpace ℝ (Fin d)) := e '' A
  have hB : IsCompact B := hA.image e.continuous
  have hcon := heuclid d B hB
  have hef : Set.MapsTo e Aᶜ Bᶜ := by
    intro x hx hxe
    rcases hxe with ⟨a, ha, hea⟩
    exact hx ((e.injective hea).symm ▸ ha)
  have heg : Set.MapsTo e.symm Bᶜ Aᶜ := by
    intro y hy hya
    apply hy
    exact ⟨e.symm y, hya, e.apply_symm_apply y⟩
  let f : C(E, EuclideanSpace ℝ (Fin d)) := ⟨e, e.continuous⟩
  let g : C(EuclideanSpace ℝ (Fin d), E) := ⟨e.symm, e.symm.continuous⟩
  let F (n : ℕ) := HomologicalComplex.homologyMap
    (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Aᶜ Bᶜ f hef) n
  let G (n : ℕ) := HomologicalComplex.homologyMap
    (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Bᶜ Aᶜ g heg) n
  have hGF (n : ℕ) (c : t00A04_ModTwoLocalHomology E A n) : G n (F n c) = c := by
    change (F n ≫ G n) c = c
    rw [← ConstructionTargets.CoefficientPairNaturality.homology_comp]
    convert ConcreteCategory.congr_hom
      (ConstructionTargets.CoefficientPairNaturality.homology_id (ZMod 2) Aᶜ n) c using 1
    · have hcomp : g.comp f = ContinuousMap.id E := by ext x; simp [f, g]
      simpa only [hcomp]
  have hFG (n : ℕ) (c : t00A04_ModTwoLocalHomology _ B n) : F n (G n c) = c := by
    change (G n ≫ F n) c = c
    rw [← ConstructionTargets.CoefficientPairNaturality.homology_comp]
    convert ConcreteCategory.congr_hom
      (ConstructionTargets.CoefficientPairNaturality.homology_id (ZMod 2) Bᶜ n) c using 1
    · have hcomp : f.comp g = ContinuousMap.id (EuclideanSpace ℝ (Fin d)) := by
        ext x
        simp [f, g]
      simpa only [hcomp]
  have hpoint (x : E) (hx : x ∈ A) (n : ℕ)
      (c : t00A04_ModTwoLocalHomology E A n) :
      t00A04_modTwo_pointRestriction _ B (e x) ⟨x, hx, rfl⟩ n (F n c) =
        HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2)
            ({x} : Set E)ᶜ ({e x} : Set _)ᶜ f (by
              intro y hy hmem
              exact hy (Set.mem_singleton_iff.mpr
                (e.injective (Set.mem_singleton_iff.mp hmem))))) n
          (t00A04_modTwo_pointRestriction E A x hx n c) := by
    change
      ((F n ≫ HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Bᶜ ({e x} : Set _)ᶜ
          (ContinuousMap.id _) _) n) c) =
      ((HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Aᶜ ({x} : Set E)ᶜ
          (ContinuousMap.id _) _) n ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2)
            ({x} : Set E)ᶜ ({e x} : Set _)ᶜ f _) n) c)
    rw [← ConstructionTargets.CoefficientPairNaturality.homology_comp,
      ← ConstructionTargets.CoefficientPairNaturality.homology_comp]
    rfl
  constructor
  · intro i hi
    constructor
    intro a b
    apply (fun h ↦ (hGF i a).symm.trans ((congrArg (fun z ↦ G i z) h).trans (hGF i b)))
    exact hcon.vanish_above i hi |>.elim _ _
  · obtain ⟨c, hc⟩ := hcon.exists_everywhere_nonzero
    refine ⟨G d c, ?_⟩
    intro x hx hzero
    have hcpoint := hc (e x) ⟨x, hx, rfl⟩
    apply hcpoint
    have hp := hpoint x hx d (G d c)
    rw [hFG d c, hzero, map_zero] at hp
    exact hp
  · intro c
    constructor
    · intro hc x hx
      subst c
      exact map_zero _
    · intro hc
      have hFc : F d c = 0 := by
        apply (hcon.eq_zero_iff_pointwise (F d c)).2
        intro y hy
        obtain ⟨x, hx, rfl⟩ := hy
        have hp := hpoint x hx d c
        rw [hc x hx, map_zero] at hp
        exact hp
      exact (hGF d c).symm.trans (by rw [hFc]; exact map_zero _)

/-- `f` as a map into `((range f)ᶜ)ᶜ`, the space left after excising `(range f)ᶜ`. -/
def t00A04_rangeCorestrict {Y W : Type} [TopologicalSpace Y] [TopologicalSpace W]
    (f : Y → W) (hcont : Continuous f) : C(Y, {w : W // w ∈ ((Set.range f)ᶜ)ᶜ}) :=
  ⟨fun y ↦ ⟨f y, by rw [compl_compl]; exact ⟨y, rfl⟩⟩,
    hcont.subtype_mk (fun y ↦ by rw [compl_compl]; exact ⟨y, rfl⟩)⟩

theorem t00A04_rangeCorestrict_mapsTo {Y W : Type} [TopologicalSpace Y] [TopologicalSpace W]
    (f : Y → W) (hinj : Function.Injective f) (hcont : Continuous f) (K : Set Y) :
    Set.MapsTo (t00A04_rangeCorestrict f hcont) Kᶜ
      (ConstructionTargets.SingularExcision.excisedSubspace (f '' K)ᶜ (Set.range f)ᶜ) := by
  intro y hy hmem
  rcases hmem with ⟨k, hk, hfk⟩
  change f k = f y at hfk
  exact hy ((hinj hfk).symm ▸ hk)

/-- Excision for a compact support along an open embedding.  Besides the
group isomorphism supplied by singular excision, this records its naturality
with respect to all maps from the compact support to point supports; that
naturality is exactly what transports the two point-restriction clauses in
`t00A04_HatcherConclusion`. -/
theorem t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_isIso_aux_compactSupportExcision_aux_factor_aux_rangePair_isIso
    {Y W : Type} [TopologicalSpace Y] [TopologicalSpace W]
    (f : Y → W) (hinj : Function.Injective f) (hcont : Continuous f)
    (hopen : ∀ U : Set Y, IsOpen U → IsOpen (f '' U))
    (K : Set Y) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Kᶜ
        (ConstructionTargets.SingularExcision.excisedSubspace
          (f '' K)ᶜ (Set.range f)ᶜ) (t00A04_rangeCorestrict f hcont) (t00A04_rangeCorestrict_mapsTo f hinj hcont K)) q) := by
  let hof : IsOpenMap f := fun U hU ↦ hopen U hU
  let hoe : Topology.IsOpenEmbedding f :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hof
  let hr : Y ≃ₜ Set.range f := hoe.isEmbedding.toHomeomorph
  let hc : {w : W // w ∈ ((Set.range f)ᶜ)ᶜ} ≃ₜ Set.range f :=
    Homeomorph.setCongr (compl_compl (Set.range f))
  let e : C({w : W // w ∈ ((Set.range f)ᶜ)ᶜ}, Y) := ⟨hc.trans hr.symm, (hc.trans hr.symm).continuous⟩
  have he : Set.MapsTo e
      (ConstructionTargets.SingularExcision.excisedSubspace
        (f '' K)ᶜ (Set.range f)ᶜ) Kᶜ := by
    intro z hz hK
    apply hz
    change (z.1 : W) ∈ f '' K
    refine ⟨e z, hK, ?_⟩
    change f (e z) = z.1
    exact congrArg Subtype.val ((hc.trans hr.symm).symm_apply_apply z)
  let F := HomologicalComplex.homologyMap
    (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Kᶜ
      (ConstructionTargets.SingularExcision.excisedSubspace
        (f '' K)ᶜ (Set.range f)ᶜ) (t00A04_rangeCorestrict f hcont)
        (t00A04_rangeCorestrict_mapsTo f hinj hcont K)) q
  let G := HomologicalComplex.homologyMap
    (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2)
      (ConstructionTargets.SingularExcision.excisedSubspace
        (f '' K)ᶜ (Set.range f)ᶜ) Kᶜ e he) q
  have hGF : e.comp (t00A04_rangeCorestrict f hcont) = ContinuousMap.id Y := by
    ext y
    exact (hc.trans hr.symm).apply_symm_apply y
  have hFG : (t00A04_rangeCorestrict f hcont).comp e =
      ContinuousMap.id {w : W // w ∈ ((Set.range f)ᶜ)ᶜ} := by
    ext z
    exact congrArg Subtype.val ((hc.trans hr.symm).symm_apply_apply z)
  apply (CategoryTheory.ConcreteCategory.isIso_iff_bijective F).mpr
  constructor
  · intro a b hab
    have hGa := congrArg (fun z ↦ G z) hab
    change (F ≫ G) a = (F ≫ G) b at hGa
    rw [← ConstructionTargets.CoefficientPairNaturality.homology_comp] at hGa
    simpa only [hGF, ConstructionTargets.CoefficientPairNaturality.homology_id,
      ConcreteCategory.id_apply] using hGa
  · intro b
    refine ⟨G b, ?_⟩
    change (G ≫ F) b = b
    rw [← ConstructionTargets.CoefficientPairNaturality.homology_comp]
    simpa only [hFG, ConstructionTargets.CoefficientPairNaturality.homology_id,
      ConcreteCategory.id_apply]

theorem t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_isIso_aux_compactSupportExcision_aux_factor_aux_composite
    {Y W : Type} [TopologicalSpace Y] [TopologicalSpace W]
    (f : Y → W) (hinj : Function.Injective f) (hcont : Continuous f)
    (K : Set Y) :
    ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Kᶜ
        (ConstructionTargets.SingularExcision.excisedSubspace
          (f '' K)ᶜ (Set.range f)ᶜ) (t00A04_rangeCorestrict f hcont)
          (t00A04_rangeCorestrict_mapsTo f hinj hcont K) ≫
        ConstructionTargets.CoefficientExcision.excisionMap
          (ZMod 2) (f '' K)ᶜ (Set.range f)ᶜ =
      ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Kᶜ (f '' K)ᶜ
        ⟨f, hcont⟩ (by
          intro y hy hfK
          rcases hfK with ⟨k, hk, hfk⟩
          exact hy ((hinj hfk).symm ▸ hk)) := by
  apply (cancel_epi (cokernel.π
    (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2) Kᶜ))).1
  have h1 := ConstructionTargets.CoefficientRadialPair.projection (ZMod 2) Kᶜ
    (ConstructionTargets.SingularExcision.excisedSubspace (f '' K)ᶜ (Set.range f)ᶜ)
    (t00A04_rangeCorestrict f hcont) (t00A04_rangeCorestrict_mapsTo f hinj hcont K)
  have h2 := ConstructionTargets.CoefficientExcision.projection (ZMod 2) (f '' K)ᶜ (Set.range f)ᶜ
  have h3 := ConstructionTargets.CoefficientRadialPair.projection (ZMod 2) Kᶜ (f '' K)ᶜ
    ⟨f, hcont⟩ (by
          intro y hy hfK
          rcases hfK with ⟨k, hk, hfk⟩
          exact hy ((hinj hfk).symm ▸ hk))
  erw [reassoc_of% h1]
  erw [Category.assoc, h2, h3]
  erw [← Category.assoc]
  congr 1
  change (ConstructionTargets.CoefficientRadialPair.chains (ZMod 2)).map _ ≫
      (ConstructionTargets.CoefficientRadialPair.chains (ZMod 2)).map _ =
    (ConstructionTargets.CoefficientRadialPair.chains (ZMod 2)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

theorem t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_isIso_aux_compactSupportExcision_aux_factor
    {Y W : Type} [TopologicalSpace Y] [TopologicalSpace W] [T2Space Y] [T2Space W]
    (f : Y → W) (hinj : Function.Injective f) (hcont : Continuous f)
    (hopen : ∀ U : Set Y, IsOpen U → IsOpen (f '' U))
    (K : Set Y) (q : ℕ) :
    ∃ g : ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2) Kᶜ ⟶
        ConstructionTargets.CoefficientRelativeSmall.relativeChains (ZMod 2)
          (ConstructionTargets.SingularExcision.excisedSubspace
            (f '' K)ᶜ (Set.range f)ᶜ),
      IsIso (HomologicalComplex.homologyMap g q) ∧
      g ≫ ConstructionTargets.CoefficientExcision.excisionMap
          (ZMod 2) (f '' K)ᶜ (Set.range f)ᶜ =
        ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Kᶜ (f '' K)ᶜ
          ⟨f, hcont⟩ (by
            intro y hy hfK
            rcases hfK with ⟨k, hk, hfk⟩
            exact hy (show y ∈ K from (hinj hfk).symm ▸ hk)) := by
  let g := ConstructionTargets.CoefficientRadialPair.pairMap
    (ZMod 2) Kᶜ (ConstructionTargets.SingularExcision.excisedSubspace
      (f '' K)ᶜ (Set.range f)ᶜ) (t00A04_rangeCorestrict f hcont)
      (t00A04_rangeCorestrict_mapsTo f hinj hcont K)
  refine ⟨g, ?_, ?_⟩
  · exact
      t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_isIso_aux_compactSupportExcision_aux_factor_aux_rangePair_isIso
        f hinj hcont hopen K q
  · exact
      t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_isIso_aux_compactSupportExcision_aux_factor_aux_composite
        f hinj hcont K

theorem t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_isIso_aux_compactSupportExcision
    {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y] [T2Space Z]
    (f : Y → Z) (hinj : Function.Injective f) (hcont : Continuous f)
    (hopen : ∀ U : Set Y, IsOpen U → IsOpen (f '' U))
    (K : Set Y) (hK : IsCompact K) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Kᶜ (f '' K)ᶜ
        ⟨f, hcont⟩ (by
          intro y hy hfK
          rcases hfK with ⟨k, hk, hfk⟩
          exact hy (show y ∈ K from (hinj hfk).symm ▸ hk))) q) := by
  have hclosedK : IsClosed (f '' K) := (hK.image hcont).isClosed
  have hclosedC : IsClosed (Set.range f)ᶜ := by
    apply IsOpen.isClosed_compl
    simpa only [Set.image_univ] using hopen Set.univ isOpen_univ
  have hsub : (Set.range f)ᶜ ⊆ interior (f '' K)ᶜ := by
    rw [hclosedK.isOpen_compl.interior_eq]
    intro z hz hzK
    rcases hzK with ⟨y, hyK, rfl⟩
    exact hz ⟨y, rfl⟩
  obtain ⟨g, hg, hgf⟩ :=
    t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_isIso_aux_compactSupportExcision_aux_factor
      f hinj hcont hopen K q
  letI : IsIso (HomologicalComplex.homologyMap g q) := hg
  letI := ConstructionTargets.CoefficientExcision.excision_isIso
    (ZMod 2) (f '' K)ᶜ (Set.range f)ᶜ hclosedC hsub q
  rw [← hgf, HomologicalComplex.homologyMap_comp]
  infer_instance

theorem t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_isIso
    {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y] [T2Space Z]
    (f : Y → Z) (hinj : Function.Injective f) (hcont : Continuous f)
    (hopen : ∀ U : Set Y, IsOpen U → IsOpen (f '' U))
    (B : Set Y) (hB : IsCompact B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Bᶜ (f '' B)ᶜ
        ⟨f, hcont⟩ (by
          intro y hy hfB
          rcases hfB with ⟨b, hb, hfb⟩
          exact hy (show y ∈ B from (hinj hfb).symm ▸ hb))) n) := by
  exact
    t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_isIso_aux_compactSupportExcision
      f hinj hcont hopen B hB n

theorem t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_point
    {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : Y → Z) (hinj : Function.Injective f) (hcont : Continuous f)
    (B : Set Y) (x : Y) (hx : x ∈ B) (n : ℕ)
    (c : t00A04_ModTwoLocalHomology Y B n) :
    t00A04_modTwo_pointRestriction Z (f '' B) (f x) ⟨x, hx, rfl⟩ n
        (HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Bᶜ (f '' B)ᶜ
            ⟨f, hcont⟩ (by
              intro y hy hfB
              rcases hfB with ⟨b, hb, hfb⟩
              exact hy (show y ∈ B from (hinj hfb).symm ▸ hb))) n c) =
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) ({x} : Set Y)ᶜ
          ({f x} : Set Z)ᶜ ⟨f, hcont⟩ (by
            intro y hy hfy
            exact hy (hinj hfy))) n
        (t00A04_modTwo_pointRestriction Y B x hx n c) := by
  change
    (((HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Bᶜ (f '' B)ᶜ
          ⟨f, hcont⟩ _) n) ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) (f '' B)ᶜ
          ({f x} : Set Z)ᶜ (ContinuousMap.id Z) _) n) c) =
    (((HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Bᶜ
          ({x} : Set Y)ᶜ (ContinuousMap.id Y) _) n) ≫
      HomologicalComplex.homologyMap
        (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) ({x} : Set Y)ᶜ
          ({f x} : Set Z)ᶜ ⟨f, hcont⟩ _) n) c)
  rw [← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp,
    ← ConstructionTargets.CoefficientPairNaturality.pair_comp,
    ← ConstructionTargets.CoefficientPairNaturality.pair_comp]
  rfl

/-- `IsIso` of a pairMap homology map depends on the target set only up to
equality (generalized so that `subst` applies; the containment proofs are
irrelevant). -/
theorem t00A04_pairMap_isIso_target_transport
    {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    (S : Set Y) (T T' : Set Z) (hT : T = T') (g : C(Y, Z))
    (h : Set.MapsTo g S T) (h' : Set.MapsTo g S T') (n : ℕ)
    (hiso : IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) S T g h) n)) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) S T' g h') n) := by
  subst hT
  exact hiso

theorem t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_point_injective_aux_cast
    {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y] [T2Space Z]
    (f : Y → Z) (hinj : Function.Injective f) (hcont : Continuous f)
    (x : Y) (n : ℕ)
    (hiso : IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) ({x} : Set Y)ᶜ
        (f '' ({x} : Set Y))ᶜ ⟨f, hcont⟩ (by
          intro y hy hfy
          rcases hfy with ⟨z, hz, hfz⟩
          exact hy (show y ∈ ({x} : Set Y) from (hinj hfz).symm ▸ hz))) n)) :
    IsIso (HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) ({x} : Set Y)ᶜ
        ({f x} : Set Z)ᶜ ⟨f, hcont⟩
          (fun y hy hfy ↦ hy (Set.mem_singleton_iff.mpr
            (hinj (Set.mem_singleton_iff.mp hfy))))) n) := by
  exact t00A04_pairMap_isIso_target_transport ({x} : Set Y)ᶜ (f '' ({x} : Set Y))ᶜ
    ({f x} : Set Z)ᶜ (by rw [Set.image_singleton]) ⟨f, hcont⟩ _ _ n hiso

theorem t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_point_injective
    {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y] [T2Space Z]
    (f : Y → Z) (hinj : Function.Injective f) (hcont : Continuous f)
    (hopen : ∀ U : Set Y, IsOpen U → IsOpen (f '' U)) (x : Y) (n : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap
      (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) ({x} : Set Y)ᶜ
        ({f x} : Set Z)ᶜ ⟨f, hcont⟩
          (fun y hy hfy ↦ hy (Set.mem_singleton_iff.mpr
            (hinj (Set.mem_singleton_iff.mp hfy))))) n) := by
  let F := HomologicalComplex.homologyMap
    (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) ({x} : Set Y)ᶜ
      ({f x} : Set Z)ᶜ ⟨f, hcont⟩
        (fun y hy hfy ↦ hy (Set.mem_singleton_iff.mpr
          (hinj (Set.mem_singleton_iff.mp hfy))))) n
  have hF0 :=
    t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_isIso
      f hinj hcont hopen ({x} : Set Y) isCompact_singleton n
  have hF : IsIso F :=
    t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_point_injective_aux_cast
      f hinj hcont x n hF0
  exact (asIso F).toLinearEquiv.injective

theorem t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding
    {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y] [T2Space Z]
    (f : Y → Z) (hinj : Function.Injective f) (hcont : Continuous f)
    (hopen : ∀ U : Set Y, IsOpen U → IsOpen (f '' U)) (d : ℕ)
    (B : Set Y) (hB : IsCompact B) :
    t00A04_HatcherConclusion Y d B ↔
      t00A04_HatcherConclusion Z d (f '' B) := by
  let F := fun (n : ℕ) ↦ HomologicalComplex.homologyMap
    (ConstructionTargets.CoefficientRadialPair.pairMap (ZMod 2) Bᶜ (f '' B)ᶜ
      ⟨f, hcont⟩ (by
        intro y hy hfB
        rcases hfB with ⟨b, hb, hfb⟩
        exact hy (show y ∈ B from (hinj hfb).symm ▸ hb))) n
  have hFI : ∀ n, IsIso (F n) := fun n ↦
    t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_isIso
      f hinj hcont hopen B hB n
  have hbij : ∀ n, Function.Bijective (F n) := by
    intro n
    exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective (F n)).mp (hFI n)
  constructor
  · intro hY
    constructor
    · intro i hdi
      letI : Subsingleton (t00A04_ModTwoLocalHomology Y B i) :=
        hY.vanish_above i hdi
      constructor
      intro a b
      obtain ⟨a', rfl⟩ := (hbij i).2 a
      obtain ⟨b', rfl⟩ := (hbij i).2 b
      exact congrArg (F i) (Subsingleton.elim a' b')
    · obtain ⟨c, hc⟩ := hY.exists_everywhere_nonzero
      refine ⟨F d c, ?_⟩
      rintro _ ⟨x, hx, rfl⟩ hz
      have hsquare :=
        t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_point
          f hinj hcont B x hx d c
      rw [hz] at hsquare
      apply hc x hx
      apply t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_point_injective
        f hinj hcont hopen x d
      simpa using hsquare.symm
    · intro c
      constructor
      · rintro rfl _ _
        exact map_zero _
      · intro hc
        obtain ⟨c', rfl⟩ := (hbij d).2 c
        have hc'0 : c' = 0 := (hY.eq_zero_iff_pointwise c').mpr (by
          intro x hx
          apply t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_point_injective
            f hinj hcont hopen x d
          rw [map_zero]
          rw [← t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_point
            f hinj hcont B x hx d c']
          exact hc (f x) ⟨x, hx, rfl⟩)
        rw [hc'0, map_zero]
  · intro hZ
    constructor
    · intro i hdi
      letI : Subsingleton (t00A04_ModTwoLocalHomology Z (f '' B) i) :=
        hZ.vanish_above i hdi
      constructor
      intro a b
      exact (hbij i).1 (Subsingleton.elim (F i a) (F i b))
    · obtain ⟨c, hc⟩ := hZ.exists_everywhere_nonzero
      obtain ⟨c', hc'⟩ := (hbij d).2 c
      refine ⟨c', ?_⟩
      intro x hx hz
      apply hc (f x) ⟨x, hx, rfl⟩
      rw [← hc']
      rw [t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_point
        f hinj hcont B x hx d c', hz, map_zero]
    · intro c
      constructor
      · rintro rfl _ _
        exact map_zero _
      · intro hc
        apply (hbij d).1
        rw [map_zero]
        apply (hZ.eq_zero_iff_pointwise (F d c)).mpr
        rintro _ ⟨x, hx, rfl⟩
        rw [t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding_aux_point
          f hinj hcont B x hx d c, hc x hx, map_zero]

/-- Apply open-embedding excision twice, on the source and target of a partial
homeomorphism.  This is the chart-shaped form of the preceding naturality
lemma. -/
theorem t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_partialHomeomorph
    {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y] [T2Space Z]
    (e : PartialEquiv Y Z) (d : ℕ)
    (B : Set Y) (hB : IsCompact B) (hBe : B ⊆ e.source)
    (hopen_source : IsOpen e.source) (hopen_target : IsOpen e.target)
    (hcont : ContinuousOn e e.source) (hcont_symm : ContinuousOn e.symm e.target)
    (hopenExcision : ∀ {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
      [T2Space P] [T2Space Q] (f : P → Q), Function.Injective f → Continuous f →
      (∀ U : Set P, IsOpen U → IsOpen (f '' U)) →
      (C : Set P) → IsCompact C →
      (t00A04_HatcherConclusion P d C ↔
        t00A04_HatcherConclusion Q d (f '' C))) :
    t00A04_HatcherConclusion Y d B ↔
      t00A04_HatcherConclusion Z d (e '' B) := by
  let S := {y : Y // y ∈ e.source}
  let T := {z : Z // z ∈ e.target}
  let C : Set S := {y | (y : Y) ∈ B}
  let h : S ≃ₜ T :=
    { toFun := fun y ↦ ⟨e y, e.map_source y.2⟩
      invFun := fun z ↦ ⟨e.symm z, e.map_target z.2⟩
      left_inv := fun y ↦ Subtype.ext (e.left_inv y.2)
      right_inv := fun z ↦ Subtype.ext (e.right_inv z.2)
      continuous_toFun := hcont.restrict.subtype_mk _
      continuous_invFun := hcont_symm.restrict.subtype_mk _ }
  have himageC : ((fun y : S ↦ (y : Y)) '' C) = B := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, hBe hy⟩, hy, rfl⟩
  have hC : IsCompact C := by
    rw [Subtype.isCompact_iff, himageC]
    exact hB
  have hincS := hopenExcision (fun y : S ↦ (y : Y))
    Subtype.val_injective continuous_subtype_val
    (fun U hU ↦ hopen_source.isOpenMap_subtype_val U hU) C hC
  have hh := hopenExcision h h.injective h.continuous
    (fun U hU ↦ h.isOpenMap U hU) C hC
  have hTcompact : IsCompact (h '' C) := hC.image h.continuous
  have hincT := hopenExcision (fun z : T ↦ (z : Z))
    Subtype.val_injective continuous_subtype_val
    (fun U hU ↦ hopen_target.isOpenMap_subtype_val U hU) (h '' C) hTcompact
  have himageT : ((fun z : T ↦ (z : Z)) '' (h '' C)) = e '' B := by
    ext z
    constructor
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨h ⟨y, hBe hy⟩, ⟨⟨y, hBe hy⟩, hy, rfl⟩, rfl⟩
  constructor
  · intro hY
    have hTC := hincT.mp (hh.mp (hincS.mpr (himageC ▸ hY)))
    rwa [himageT] at hTC
  · intro hZ
    have hSC := hincS.mp (hh.mpr (hincT.mpr (himageT ▸ hZ)))
    rwa [himageC] at hSC

theorem t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_target_open
    (E X : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [ChartedSpace E X] [IsManifold I ∞ X]
    [BoundarylessManifold I X] (x : X) :
    IsOpen (extChartAt I x).target := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  let y : X := (extChartAt I x).symm z
  have hy : y ∈ (extChartAt I x).source :=
    (extChartAt I x).map_target hz
  have hy' : y ∈ (chartAt E x).source := by
    simpa only [extChartAt_source] using hy
  have hzi : z ∈ interior (extChartAt I x).target := by
    have hi := (I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas E x) hy').mp
      (BoundarylessManifold.isInteriorPoint (I := I) (x := y))
    rw [← (extChartAt I x).right_inv hz]
    simpa only [extChartAt] using hi
  exact mem_interior_iff_mem_nhds.mp hzi

theorem t00A04_hatcherConclusion_compact_in_chart_aux_open_excision
    (E X : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X]
    [IsManifold I ∞ X] [BoundarylessManifold I X]
    (hmodel : ∀ (B : Set E), IsCompact B →
      t00A04_HatcherConclusion E (Module.finrank ℝ E) B)
    (A : Set X) (hA : IsCompact A)
    (hchart : ∃ x : X, A ⊆ (extChartAt I x).source) :
    t00A04_HatcherConclusion X (Module.finrank ℝ E) A := by
  rcases hchart with ⟨x, hx⟩
  let e := extChartAt I x
  have himage : IsCompact (e '' A) :=
    hA.image_of_continuousOn ((continuousOn_extChartAt x).mono hx)
  have hm := hmodel (e '' A) himage
  exact (t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_partialHomeomorph
    e (Module.finrank ℝ E) A hA hx (isOpen_extChartAt_source x)
      (t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_target_open
        E X I x)
    (continuousOn_extChartAt x) (continuousOn_extChartAt_symm x)
    (fun f hinj hcont hopen C hC ↦
      t00A04_hatcherConclusion_compact_in_chart_aux_open_excision_aux_openEmbedding
        f hinj hcont hopen (Module.finrank ℝ E) C hC)).mpr hm

theorem t00A04_hatcherConclusion_compact_in_chart
    (E X : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X]
    [IsManifold I ∞ X] [BoundarylessManifold I X]
    (heuclid : ∀ (d : ℕ) (A : Set (EuclideanSpace ℝ (Fin d))), IsCompact A →
      t00A04_HatcherConclusion _ d A)
    (A : Set X) (hA : IsCompact A)
    (hchart : ∃ x : X, A ⊆ (extChartAt I x).source) :
    t00A04_HatcherConclusion X (Module.finrank ℝ E) A := by
  apply t00A04_hatcherConclusion_compact_in_chart_aux_open_excision E X I
    (t00A04_hatcherConclusion_compact_in_chart_aux_model E heuclid)
    A hA hchart

/-- **LIBRARY F3.** Finite chart induction.  Arbitrary compact single-chart
sets, the union step, and local uniqueness are explicit hypotheses. -/
theorem t00A04_hatcherConclusion_compact_manifold_aux_empty
    (X : Type) [TopologicalSpace X] [IsEmpty X] (d : ℕ) :
    t00A04_HatcherConclusion X d ∅ := by
  have hsub (n : ℕ) :
      Subsingleton (t00A04_ModTwoLocalHomology X ∅ n) := by
    let f := ConstructionTargets.CoefficientRelativeSmall.subspaceMap
      (ZMod 2) (Set.univ : Set X)
    haveI : IsIso f := by
      dsimp [f, ConstructionTargets.CoefficientRelativeSmall.subspaceMap,
        ConstructionTargets.CoefficientRelativeSmall.chains]
      rw [ConstructionTargets.SingularHomologyConcrete.subspaceInclusion_univ]
      apply Functor.map_isIso
    have hz : CategoryTheory.Limits.IsZero
        (ConstructionTargets.CoefficientRelativeSmall.relativeChains
          (ZMod 2) (Set.univ : Set X)) :=
      CategoryTheory.Limits.isZero_cokernel_of_epi f
    have hzero : Subsingleton
        (((ConstructionTargets.CoefficientRelativeSmall.relativeChains
          (ZMod 2) (Set.univ : Set X)).homology n : Type)) :=
      ModuleCat.subsingleton_of_isZero
      (Functor.map_isZero
        (HomologicalComplex.homologyFunctor (ModuleCat (ZMod 2))
          (ComplexShape.down ℕ) n) hz)
    simpa only [t00A04_ModTwoLocalHomology, Set.compl_empty] using hzero
  refine ⟨fun i _ => hsub i, ⟨0, fun x => isEmptyElim x⟩, ?_⟩
  intro c
  exact ⟨fun _ x => isEmptyElim x, fun _ => (hsub d).elim c 0⟩

theorem t00A04_hatcherConclusion_compact_manifold
    (E X : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X]
    [IsManifold I ∞ X] [BoundarylessManifold I X]
    (hlocal : ∀ (A : Set X), IsCompact A →
      (∃ x : X, A ⊆ (extChartAt I x).source) →
      t00A04_HatcherConclusion X (Module.finrank ℝ E) A)
    (hunion : ∀ (A B : Set X), IsCompact A → IsCompact B →
      t00A04_HatcherConclusion X (Module.finrank ℝ E) A →
      t00A04_HatcherConclusion X (Module.finrank ℝ E) B →
      t00A04_HatcherConclusion X (Module.finrank ℝ E) (A ∩ B) →
      (∀ x : X, ∀ a b : t00A04_ModTwoLocalHomology X {x} (Module.finrank ℝ E),
        a ≠ 0 → b ≠ 0 → a = b) →
      t00A04_HatcherConclusion X (Module.finrank ℝ E) (A ∪ B))
    (hloc : ∀ x : X, ∀ a b : t00A04_ModTwoLocalHomology X {x} (Module.finrank ℝ E),
      a ≠ 0 → b ≠ 0 → a = b)
    (A : Set X) (hA : IsCompact A) :
    t00A04_HatcherConclusion X (Module.finrank ℝ E) A := by
  classical
  let U : X → Set X := fun x => (extChartAt I x).source
  have hUopen : ∀ x, IsOpen (U x) := fun x => isOpen_extChartAt_source x
  have hAcov : A ⊆ ⋃ x, U x := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨x, mem_extChartAt_source x⟩
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover U hUopen hAcov
  obtain ⟨K, hKcompact, hKsub, hAK⟩ := hA.finite_compact_cover s U
    (fun x _ => hUopen x) hs
  have key : ∀ t : Finset X,
      t00A04_HatcherConclusion X (Module.finrank ℝ E) (⋃ x ∈ t, K x) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
        by_cases hX : Nonempty X
        · let x : X := Classical.choice hX
          exact hlocal ∅ isCompact_empty ⟨x, Set.empty_subset _⟩
        · haveI : IsEmpty X := not_nonempty_iff.mp hX
          exact t00A04_hatcherConclusion_compact_manifold_aux_empty X _
    | @insert x t hxt ih =>
        rw [Finset.set_biUnion_insert]
        have hKt : IsCompact (⋃ y ∈ t, K y) :=
          t.isCompact_biUnion (fun y _ => hKcompact y)
        apply hunion (K x) (⋃ y ∈ t, K y) (hKcompact x) hKt
        · exact hlocal (K x) (hKcompact x) ⟨x, hKsub x⟩
        · exact ih
        · exact hlocal (K x ∩ ⋃ y ∈ t, K y) ((hKcompact x).inter hKt)
            ⟨x, Set.inter_subset_left.trans (hKsub x)⟩
        · exact hloc
  rw [hAK]
  exact key s

/-- **LIBRARY F4.** At support `A = X`, a nonzero relative fundamental class
is a nonzero absolute top-homology class. -/
theorem t00A04_top_homology_nontrivial_of_hatcherConclusion_univ_aux_emptyMap
    (X : Type) [TopologicalSpace X] :
    ConstructionTargets.CoefficientRelativeSmall.subspaceMap
      (ZMod 2) (∅ : Set X) = 0 := by
  exact
    t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_zero_aux_emptyMap
      (ZMod 2) X

noncomputable def t00A04_top_homology_nontrivial_of_hatcherConclusion_univ_aux_relativeIso
    (X : Type) [TopologicalSpace X] :
    ConstructionTargets.CoefficientRelativeSmall.relativeChains
        (ZMod 2) (∅ : Set X) ≅
      ConstructionTargets.CoefficientH0.SingularChains (ZMod 2) (TopCat.of X) :=
  CategoryTheory.Limits.cokernelIsoOfEq
      (t00A04_top_homology_nontrivial_of_hatcherConclusion_univ_aux_emptyMap X) ≪≫
    CategoryTheory.Limits.cokernelZeroIsoTarget

noncomputable def t00A04_top_homology_nontrivial_of_hatcherConclusion_univ_aux_coefficientIso
    (X : Type) [TopologicalSpace X] (d : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor
        (ModuleCat (ZMod 2)) d).obj (ModuleCat.of (ZMod 2) (ZMod 2))).obj
        (TopCat.of X) ≅
      ((AlgebraicTopology.singularHomologyFunctor
        (ModuleCat (ZMod 2)) d).obj
        (ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2)))).obj (TopCat.of X) :=
  ((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat (ZMod 2)) d).mapIso
      (ULift.moduleEquiv.symm.toModuleIso)).app (TopCat.of X)

theorem t00A04_top_homology_nontrivial_of_hatcherConclusion_univ
    (X : Type) [TopologicalSpace X] [Nonempty X] (d : ℕ)
    (h : t00A04_HatcherConclusion X d Set.univ) :
    Nontrivial (t00A04_ModTwoHomology d X) := by
  rcases h.exists_everywhere_nonzero with ⟨c, hc⟩
  let ciso :=
    t00A04_top_homology_nontrivial_of_hatcherConclusion_univ_aux_relativeIso X
  letI : IsIso ciso.hom := inferInstance
  let relativeHiso := asIso (HomologicalComplex.homologyMap ciso.hom d)
  let hiso := relativeHiso ≪≫
    t00A04_top_homology_nontrivial_of_hatcherConclusion_univ_aux_coefficientIso X d
  have hc0 : c ≠ 0 := by
    let x : X := Classical.choice inferInstance
    intro hzero
    exact hc x (Set.mem_univ x) (hzero ▸ map_zero _)
  let e : t00A04_ModTwoLocalHomology X Set.univ d ≃
      ((ConstructionTargets.CoefficientRelativeSmall.relativeChains
        (ZMod 2) (∅ : Set X)).homology d : Type) :=
    Equiv.cast (by simp only [t00A04_ModTwoLocalHomology, Set.compl_univ])
  have hec : e c ≠ e 0 := fun heq ↦ hc0 (e.injective heq)
  have hinj : Function.Injective hiso.hom :=
    (ModuleCat.mono_iff_injective hiso.hom).mp inferInstance
  exact ⟨hiso.hom (e c), hiso.hom (e 0), fun heq ↦ hec (hinj heq)⟩

/-- The Type-0 fundamental-class assembly from chart transport, union, finite
induction, and evaluation. -/
theorem t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_Type
    (E X : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X]
    [ChartedSpace E X] [IsManifold I ∞ X] [BoundarylessManifold I X] :
    Nontrivial (t00A04_ModTwoHomology (Module.finrank ℝ E) X) := by
  apply t00A04_top_homology_nontrivial_of_hatcherConclusion_univ X
    (Module.finrank ℝ E)
  apply t00A04_hatcherConclusion_compact_manifold E X I
      (fun A hA hchart ↦ t00A04_hatcherConclusion_compact_in_chart E X I
        (fun d B hB ↦ t00A04_hatcherConclusion_compact_euclidean d
          (fun s hs ↦ t00A04_hatcherConclusion_finite_union_convex_euclidean d
            (t00A04_hatcherConclusion_compact_convex_euclidean d)
            (fun C D hC hD hCi hDi hCDi ↦ t00A04_hatcherConclusion_union _ d
              C D hC hD hCi hDi hCDi
              (t00A04_modTwoLocalHomology_unique_nonzero_euclidean d)) s hs)
          B hB) A hA hchart)
      (fun A B hA hB hAi hBi hABi ↦
        t00A04_hatcherConclusion_union X (Module.finrank ℝ E)
          A B hA hB hAi hBi hABi)
      (t00A04_modTwoLocalHomology_unique_nonzero E X I) Set.univ isCompact_univ

/-- **LIBRARY (universe bridge).** Transport the Type-0 fundamental-class
theorem across a small homeomorphic model of an arbitrary-universe compact
finite-dimensional manifold. -/
theorem t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_model_small
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : Small.{0} E := by
  exact small_of_injective (Module.finBasis ℝ E).repr.injective

/-- Compactness reduces the atlas to finitely many chart sources.  Sending a
point to its first source in that finite cover and then to its chart coordinate
embeds the manifold in a finite sum of copies of the small model. -/
theorem t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_space_small
    (E : Type*) (X : Type u) [TopologicalSpace E] [Small.{0} E]
    [TopologicalSpace X] [CompactSpace X] [ChartedSpace E X] : Small.{0} X := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ (chartAt E x).source)
    (fun x ↦ (chartAt E x).open_source)
    (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, mem_chart_source E x⟩)
  let chosen : X → {x // x ∈ s} := fun x ↦
    ⟨Classical.choose (Set.mem_iUnion₂.mp (hs (Set.mem_univ x))),
      (Classical.choose_spec (Set.mem_iUnion₂.mp (hs (Set.mem_univ x)))).1⟩
  have hchosen (x : X) :
      x ∈ (chartAt E (chosen x : X)).source :=
    (Classical.choose_spec (Set.mem_iUnion₂.mp (hs (Set.mem_univ x)))).2
  let f : X → (Fin s.card × E) := fun x ↦
    (s.equivFin (chosen x), chartAt E (chosen x : X) x)
  apply small_of_injective (f := f)
  intro x y hxy
  have hi : chosen x = chosen y := s.equivFin.injective (congrArg Prod.fst hxy)
  have hc : chartAt E (chosen x : X) x = chartAt E (chosen x : X) y := by
    have := congrArg Prod.snd hxy
    change chartAt E (chosen x : X) x = chartAt E (chosen y : X) y at this
    rwa [← hi] at this
  exact (chartAt E (chosen x : X)).injOn (hchosen x) (hi ▸ hchosen y) hc

/-- Once both underlying types are small, transfer all structures to their
`Shrink` models, apply the Type-0 theorem, and use functoriality under
`Shrink.homeomorph` to transport nontriviality of singular homology back. -/
noncomputable def t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_chart
    (E : Type*) (X : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [Small.{0} X]
    (e : OpenPartialHomeomorph X E) :
    OpenPartialHomeomorph (Shrink.{0} X)
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
  let E₀ := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let L : E ≃L[ℝ] E₀ := ContinuousLinearEquiv.ofFinrankEq (by simp [E₀])
  have hI : Topology.IsOpenEmbedding I :=
    ⟨I.isClosedEmbedding.isEmbedding,
      t00A04_boundarylessManifold_of_finiteDimensional_selfModel_aux_openRange E I⟩
  let q : OpenPartialHomeomorph E E₀ :=
    (hI.toOpenPartialHomeomorph I).transHomeomorph L.toHomeomorph
  exact (Shrink.homeomorph X).symm.transOpenPartialHomeomorph (e.trans q)

@[implicit_reducible] noncomputable def t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_chartedSpace
    (E : Type*) (X : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [ChartedSpace E X] [Small.{0} X] :
    ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (Shrink.{0} X) where
  atlas := t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_chart
    E X I '' atlas E X
  chartAt y :=
    t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_chart
      E X I (chartAt E ((Shrink.homeomorph X).symm y))
  mem_chart_source y := by
    simp [t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_chart]
  chart_mem_atlas y := ⟨chartAt E ((Shrink.homeomorph X).symm y),
    chart_mem_atlas E _, rfl⟩

theorem t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_transition_aux_pair
    (E : Type*) (X : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [ChartedSpace E X] [IsManifold I ∞ X]
    [Small.{0} X] (e e' : OpenPartialHomeomorph X E)
    (he : e ∈ atlas E X) (he' : e' ∈ atlas E X) :
    let a := t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_chart
      E X I e
    let b := t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_chart
      E X I e'
    ContDiffOn ℝ ∞ (b ∘ a.symm) (a.target ∩ a.symm ⁻¹' b.source) := by
  dsimp
  let E₀ := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let L : E ≃L[ℝ] E₀ := ContinuousLinearEquiv.ofFinrankEq (by simp [E₀])
  have hI : Topology.IsOpenEmbedding I :=
    ⟨I.isClosedEmbedding.isEmbedding,
      t00A04_boundarylessManifold_of_finiteDimensional_selfModel_aux_openRange E I⟩
  let a := t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_chart
    E X I e
  let b := t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_chart
    E X I e'
  let S := a.target ∩ a.symm ⁻¹' b.source
  let T := I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ Set.range I
  have hold := StructureGroupoid.compatible (contDiffGroupoid ∞ I) he he'
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at hold
  have hcore : ContDiffOn ℝ ∞ (I ∘ (e.symm ≫ₕ e') ∘ I.symm) T := hold.1
  have hmap : Set.MapsTo L.symm S T := by
    intro z hz
    dsimp [S, T, a, b] at hz ⊢
    simp [t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_chart] at hz ⊢
    rcases hz with ⟨⟨hr, het⟩, hes⟩
    rcases hr with ⟨y, hy⟩
    have hq :
        (hI.toOpenPartialHomeomorph I).symm (L.symm z) = I.symm (L.symm z) := by
      rw [← hy]
      exact (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv I hI).trans
        (I.left_inv y).symm
    exact ⟨⟨hq ▸ het, hq ▸ hes⟩, ⟨y, hy⟩⟩
  have hpre := hcore.comp L.symm.contDiff.contDiffOn hmap
  have hout := L.contDiff.comp_contDiffOn hpre
  apply hout.congr
  intro z hz
  dsimp [S, a, b] at hz ⊢
  simp [t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_chart] at hz ⊢
  rcases hz.1.1 with ⟨y, hy⟩
  have hq :
      (hI.toOpenPartialHomeomorph I).symm (L.symm z) = I.symm (L.symm z) := by
    rw [← hy]
    exact (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv I hI).trans
      (I.left_inv y).symm
  dsimp [L, E₀]
  rw [hq]

theorem t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_transition
    (E : Type*) (X : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [ChartedSpace E X] [IsManifold I ∞ X]
    [Small.{0} X] :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) _ _
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) _
      𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞ (Shrink.{0} X) _
      (t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_chartedSpace
        E X I) := by
  let E₀ := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let c :=
    t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_chartedSpace
      E X I
  letI : ChartedSpace E₀ (Shrink.{0} X) := c
  apply isManifold_of_contDiffOn 𝓘(ℝ, E₀) ∞ (Shrink.{0} X)
  rintro a b ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  dsimp [c, E₀,
    t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_chartedSpace]
  simp only [Set.range_id, Set.inter_univ]
  exact
    t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_transition_aux_pair
      E X I e e' he he'

theorem t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport
    (E : Type*) (X : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [ChartedSpace E X] [IsManifold I ∞ X]
    [Small.{0} E] [Small.{0} X] :
    let E₀ := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
    ∃ c : ChartedSpace E₀ (Shrink.{0} X),
      letI := c
      IsManifold 𝓘(ℝ, E₀) ∞ (Shrink.{0} X) := by
  let c :=
    t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_chartedSpace
      E X I
  refine ⟨c, ?_⟩
  exact
    t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport_aux_transition
      E X I

theorem t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model
    (E : Type*) (X : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X]
    [ChartedSpace E X] [IsManifold I ∞ X] [BoundarylessManifold I X]
    [Small.{0} E] [Small.{0} X]
    (hType : ∀ (E₀ X₀ : Type) [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
      [FiniteDimensional ℝ E₀] (I₀ : ModelWithCorners ℝ E₀ E₀)
      [TopologicalSpace X₀] [T2Space X₀] [CompactSpace X₀] [Nonempty X₀]
      [ChartedSpace E₀ X₀] [IsManifold I₀ ∞ X₀] [BoundarylessManifold I₀ X₀],
      Nontrivial (t00A04_ModTwoHomology (Module.finrank ℝ E₀) X₀)) :
    Nontrivial
      (t00A04_ModTwoHomology (Module.finrank ℝ E) (Shrink.{0} X)) := by
  let E₀ := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  obtain ⟨c, hc⟩ :=
    t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model_aux_transport
      E X I
  letI : ChartedSpace E₀ (Shrink.{0} X) := c
  letI : IsManifold 𝓘(ℝ, E₀) ∞ (Shrink.{0} X) := hc
  letI : BoundarylessManifold 𝓘(ℝ, E₀) (Shrink.{0} X) :=
    t00A04_boundarylessManifold_of_finiteDimensional_selfModel E₀
      (Shrink.{0} X) 𝓘(ℝ, E₀)
  letI : T2Space (Shrink.{0} X) := (Shrink.homeomorph X).t2Space
  letI : CompactSpace (Shrink.{0} X) := (Shrink.homeomorph X).compactSpace
  letI : Nonempty (Shrink.{0} X) :=
    ⟨Shrink.homeomorph X (Classical.choice (inferInstance : Nonempty X))⟩
  have h := hType E₀ (Shrink.{0} X) 𝓘(ℝ, E₀)
  simpa [E₀] using h

/-- Universe comparison for mod-two singular homology.  This is the remaining
chain-level statement: lifting both the coefficient module and the space gives
the same homology as first computing in universe zero and then lifting the
result. -/
noncomputable def t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_homology_aux_coefficients_aux_universeComparison_aux_chainIso_aux_simplexEquiv
    (Y : Type) [TopologicalSpace Y] (n : SimplexCategoryᵒᵖ) :
    ((TopCat.toSSet.obj (TopCat.of (ULift.{u} Y))).obj n) ≃
      ULift.{u} ((TopCat.toSSet.obj (TopCat.of Y)).obj n) :=
  (TopCat.toSSetObjEquiv (TopCat.of (ULift.{u} Y)) n).trans
    (((Homeomorph.refl _).continuousMapCongr Homeomorph.ulift).trans
      ((TopCat.toSSetObjEquiv (TopCat.of Y) n).symm.trans
        Equiv.ulift.symm))

/-- The remaining universe comparison before taking alternating face maps.
In each degree this is the direct-sum equivalence obtained from
`ModuleCat.coprodIsoDirectSum`, `ULift.moduleEquiv`, and `Finsupp.mapDomain`
along `..._simplexEquiv`; naturality says that this explicit equivalence
commutes with precomposition of singular simplices. -/
theorem t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_homology_aux_coefficients_aux_universeComparison_aux_chainIso_aux_simplicialIso
    (X : Type u) [TopologicalSpace X] [Small.{0} X] :
    Nonempty
      (((sigmaConst ⋙ SimplicialObject.whiskering _ _).obj
          (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).obj
          (TopCat.toSSet.obj (TopCat.of (ULift.{u} (Shrink.{0} X)))) ≅
        ((SimplicialObject.whiskering
          (ModuleCat.{0} (ZMod 2)) (ModuleCat.{u} (ZMod 2))).obj
          (ModuleCat.uliftFunctor.{u} (ZMod 2))).obj
          (((sigmaConst ⋙ SimplicialObject.whiskering _ _).obj
            (ModuleCat.of (ZMod 2) (ZMod 2))).obj
            (TopCat.toSSet.obj (TopCat.of (Shrink.{0} X))))) := by
  sorry

theorem t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_homology_aux_coefficients_aux_universeComparison_aux_chainIso
    (X : Type u) [TopologicalSpace X] [Small.{0} X] :
    Nonempty
      (((AlgebraicTopology.singularChainComplexFunctor
          (ModuleCat.{u} (ZMod 2))).obj
          (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).obj
          (TopCat.of (ULift.{u} (Shrink.{0} X))) ≅
        (ModuleCat.uliftFunctor.{u} (ZMod 2)).mapHomologicalComplex
          (ComplexShape.down ℕ) |>.obj
          (((AlgebraicTopology.singularChainComplexFunctor
            (ModuleCat.{0} (ZMod 2))).obj
            (ModuleCat.of (ZMod 2) (ZMod 2))).obj
            (TopCat.of (Shrink.{0} X)))) := by
  let S := (((sigmaConst ⋙ SimplicialObject.whiskering _ _).obj
    (ModuleCat.of (ZMod 2) (ZMod 2))).obj
    (TopCat.toSSet.obj (TopCat.of (Shrink.{0} X))))
  let e := Classical.choice
    (t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_homology_aux_coefficients_aux_universeComparison_aux_chainIso_aux_simplicialIso
      X)
  refine ⟨(AlgebraicTopology.alternatingFaceMapComplex
    (ModuleCat.{u} (ZMod 2))).mapIso e ≪≫ ?_⟩
  exact eqToIso (Functor.congr_obj
    (AlgebraicTopology.map_alternatingFaceMapComplex
      (ModuleCat.uliftFunctor.{u} (ZMod 2))).symm S)

theorem t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_homology_aux_coefficients_aux_universeComparison_aux_homologyOfChainIso
    (X : Type u) [TopologicalSpace X] [Small.{0} X] (d : ℕ)
    (e : ((AlgebraicTopology.singularChainComplexFunctor
          (ModuleCat.{u} (ZMod 2))).obj
          (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).obj
          (TopCat.of (ULift.{u} (Shrink.{0} X))) ≅
        (ModuleCat.uliftFunctor.{u} (ZMod 2)).mapHomologicalComplex
          (ComplexShape.down ℕ) |>.obj
          (((AlgebraicTopology.singularChainComplexFunctor
            (ModuleCat.{0} (ZMod 2))).obj
            (ModuleCat.of (ZMod 2) (ZMod 2))).obj
            (TopCat.of (Shrink.{0} X)))) :
    Nonempty
      (ULift.{u}
          (t00A04_ModTwoHomology d (Shrink.{0} X)) ≃
        (((AlgebraicTopology.singularHomologyFunctor
          (ModuleCat.{u} (ZMod 2)) d).obj
          (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).obj
          (TopCat.of (ULift.{u} (Shrink.{0} X))) : Type u)) := by
  let K := (((AlgebraicTopology.singularChainComplexFunctor
    (ModuleCat.{0} (ZMod 2))).obj (ModuleCat.of (ZMod 2) (ZMod 2))).obj
    (TopCat.of (Shrink.{0} X)))
  let L := (((AlgebraicTopology.singularChainComplexFunctor
    (ModuleCat.{u} (ZMod 2))).obj
    (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).obj
    (TopCat.of (ULift.{u} (Shrink.{0} X))))
  let F := ModuleCat.uliftFunctor.{u} (ZMod 2)
  let hpres : (F.obj (K.homology d) : Type u) ≅ (L.homology d : Type u) :=
    ((forget (ModuleCat.{u} (ZMod 2))).mapIso
      ((K.sc d).mapHomologyIso F).symm) ≪≫
    ((forget (ModuleCat.{u} (ZMod 2))).mapIso
      (HomologicalComplex.homologyMapIso e.symm d))
  let K' := (((AlgebraicTopology.singularChainComplexFunctor
    (ModuleCat.{0} (ZMod 2))).obj
    (ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2)))).obj
    (TopCat.of (Shrink.{0} X)))
  let ec : K' ≅ K :=
    ((AlgebraicTopology.singularChainComplexFunctor
      (ModuleCat.{0} (ZMod 2))).mapIso
      (ULift.moduleEquiv.toModuleIso)).app (TopCat.of (Shrink.{0} X))
  let hc : (K'.homology d : Type) ≃ (K.homology d : Type) :=
    ((forget (ModuleCat.{0} (ZMod 2))).mapIso
      (HomologicalComplex.homologyMapIso ec d)).toEquiv
  let hcu : ULift.{u} (K'.homology d : Type) ≃
      ULift.{u} (K.homology d : Type) :=
    (Equiv.ulift.{u, 0}.trans hc).trans Equiv.ulift.{u, 0}.symm
  refine ⟨?_⟩
  simpa [K, K', L, F, t00A04_ModTwoHomology,
    AlgebraicTopology.singularHomologyFunctor] using
      (hcu.trans hpres.toEquiv)

theorem t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_homology_aux_coefficients_aux_universeComparison
    (X : Type u) [TopologicalSpace X] [Small.{0} X] (d : ℕ) :
    Nonempty
      (ULift.{u}
          (t00A04_ModTwoHomology d (Shrink.{0} X)) ≃
        (((AlgebraicTopology.singularHomologyFunctor
          (ModuleCat.{u} (ZMod 2)) d).obj
          (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).obj
          (TopCat.of (ULift.{u} (Shrink.{0} X))) : Type u)) := by
  exact
    t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_homology_aux_coefficients_aux_universeComparison_aux_homologyOfChainIso
      X d (Classical.choice
        (t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_homology_aux_coefficients_aux_universeComparison_aux_chainIso
          X))

theorem t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_homology_aux_coefficients
    (X : Type u) [TopologicalSpace X] [Small.{0} X] (d : ℕ)
    [Nontrivial (t00A04_ModTwoHomology d (Shrink.{0} X))] :
    Nontrivial
      (((AlgebraicTopology.singularHomologyFunctor
        (ModuleCat.{u} (ZMod 2)) d).obj
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).obj
        (TopCat.of (ULift.{u} (Shrink.{0} X))) : Type u) := by
  let e := Classical.choice
    (t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_homology_aux_coefficients_aux_universeComparison
      X d)
  letI : Nontrivial (ULift.{u}
      (t00A04_ModTwoHomology d (Shrink.{0} X))) := inferInstance
  exact Equiv.nontrivial e.symm

theorem t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_homology_aux_homeomorph
    (X : Type u) [TopologicalSpace X] [Small.{0} X] (d : ℕ)
    [Nontrivial
      (((AlgebraicTopology.singularHomologyFunctor
        (ModuleCat.{u} (ZMod 2)) d).obj
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).obj
        (TopCat.of (ULift.{u} (Shrink.{0} X))) : Type u)] :
    Nontrivial (t00A04_ModTwoHomology d X) := by
  let h : X ≃ₜ ULift.{u} (Shrink.{0} X) :=
    (Shrink.homeomorph X).trans Homeomorph.ulift.symm
  let hi : TopCat.of X ≅ TopCat.of (ULift.{u} (Shrink.{0} X)) :=
    TopCat.isoOfHomeo h
  let e :=
    (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} (ZMod 2)) d).obj
      (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).mapIso
      hi).toLinearEquiv
  exact Equiv.nontrivial e.toEquiv

theorem t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_homology
    (X : Type u) [TopologicalSpace X] [Small.{0} X] (d : ℕ)
    [Nontrivial (t00A04_ModTwoHomology d (Shrink.{0} X))] :
    Nontrivial (t00A04_ModTwoHomology d X) := by
  letI : Nontrivial
      (((AlgebraicTopology.singularHomologyFunctor
        (ModuleCat.{u} (ZMod 2)) d).obj
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).obj
        (TopCat.of (ULift.{u} (Shrink.{0} X))) : Type u) :=
    t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_homology_aux_coefficients
      X d
  exact
    t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_homology_aux_homeomorph
      X d

theorem t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink
    (E : Type*) (X : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X]
    [ChartedSpace E X] [IsManifold I ∞ X] [BoundarylessManifold I X]
    [Small.{0} E] [Small.{0} X]
    (hType : ∀ (E₀ X₀ : Type) [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
      [FiniteDimensional ℝ E₀] (I₀ : ModelWithCorners ℝ E₀ E₀)
      [TopologicalSpace X₀] [T2Space X₀] [CompactSpace X₀] [Nonempty X₀]
      [ChartedSpace E₀ X₀] [IsManifold I₀ ∞ X₀] [BoundarylessManifold I₀ X₀],
      Nontrivial (t00A04_ModTwoHomology (Module.finrank ℝ E₀) X₀)) :
    Nontrivial (t00A04_ModTwoHomology (Module.finrank ℝ E) X) := by
  letI : Nontrivial
      (t00A04_ModTwoHomology (Module.finrank ℝ E) (Shrink.{0} X)) :=
    t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_small_model
      E X I hType
  exact
    t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink_aux_homology
      X (Module.finrank ℝ E)

theorem t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial
    (E : Type*) (X : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X]
    [ChartedSpace E X] [IsManifold I ∞ X] [BoundarylessManifold I X]
    (hType : ∀ (E₀ X₀ : Type) [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
      [FiniteDimensional ℝ E₀] (I₀ : ModelWithCorners ℝ E₀ E₀)
      [TopologicalSpace X₀] [T2Space X₀] [CompactSpace X₀] [Nonempty X₀]
      [ChartedSpace E₀ X₀] [IsManifold I₀ ∞ X₀] [BoundarylessManifold I₀ X₀],
      Nontrivial (t00A04_ModTwoHomology (Module.finrank ℝ E₀) X₀)) :
    Nontrivial (t00A04_ModTwoHomology (Module.finrank ℝ E) X) := by
  letI : Small.{0} E :=
    t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_model_small E
  letI : Small.{0} X :=
    t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_space_small E X
  exact
    t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_aux_shrink
      E X I hType

/-- The blueprint's real-parameter notion of null-homotopy restricts to the
unit interval and hence gives Mathlib's standard `ContinuousMap` notion. -/
theorem t00A04_nullhomotopic_to_continuousMap
    (X : Type*) [TopologicalSpace X]
    (hnull : apm_t00a04_NullHomotopic (fun x : X => x)) :
    ContinuousMap.Nullhomotopic (ContinuousMap.id X) := by
  rcases hnull with ⟨y, H, hH, hH0, hH1⟩
  refine ⟨y, ⟨⟨⟨fun p ↦ H (p.2, p.1), ?_⟩, ?_, ?_⟩⟩⟩
  · exact hH.comp
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
  · intro x
    simpa using hH0 x
  · intro x
    simpa using hH1 x

/-- Nonzero positive-degree mod-2 homology obstructs a null-homotopy of the
identity.  All manifold and fundamental-class input has been removed. -/
theorem t00A04_identity_not_nullhomotopic_of_modTwoHomology_nontrivial
    (X : Type u) [TopologicalSpace X] (n : ℕ) (hn : n ≠ 0)
    [Nontrivial (t00A04_ModTwoHomology n X)] :
    ¬ ContinuousMap.Nullhomotopic (ContinuousMap.id X) := by
  intro hnull
  let F := ((AlgebraicTopology.singularHomologyFunctor
    (ModuleCat.{u} (ZMod 2)) n).obj
      (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))))
  rcases hnull with ⟨y, ⟨H⟩⟩
  let cyl : CategoryTheory.MonoidalCategoryStruct.tensorObj (TopCat.of X) TopCat.I ⟶
      TopCat.of X :=
    TopCat.ofHom ⟨fun p ↦ H (TopCat.I.homeomorph p.2, p.1),
      H.continuous.comp
        ((TopCat.I.homeomorph.continuous.comp continuous_snd).prodMk continuous_fst)⟩
  have hcyl0 : TopCat.ι₀ ≫ cyl = TopCat.ofHom (ContinuousMap.id X) := by
    ext x
    change H (0, x) = x
    simp
  have hcyl1 : TopCat.ι₁ ≫ cyl = TopCat.ofHom (ContinuousMap.const X y) := by
    ext x
    change H (1, x) = y
    simp
  have heq := ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_topCatHomotopy
      (ModuleCat.{u} (ZMod 2))
      (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) cyl hcyl0 hcyl1 n
  let U := ULift.{u} Unit
  let p : C(X, U) := ContinuousMap.const X (ULift.up ())
  let q : C(U, X) := ContinuousMap.const U y
  have hfactor : ContinuousMap.const X y = q.comp p := by
    ext
    rfl
  have hzero : CategoryTheory.Limits.IsZero (F.obj (TopCat.of U)) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{u} (ZMod 2)) n
      (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) (TopCat.of U) hn
  set_option maxHeartbeats 1000000 in
   have hconst : F.map (TopCat.ofHom (ContinuousMap.const X y)) = 0 := by
    rw [hfactor]
    change F.map (TopCat.ofHom p ≫ TopCat.ofHom q) = 0
    rw [F.map_comp]
    have hq : F.map (TopCat.ofHom q) = 0 := hzero.eq_of_src _ _
    rw [hq]
    simp
  have hz : F.map (TopCat.ofHom (ContinuousMap.id X)) = 0 := heq.trans hconst
  have hidzero : 𝟙 (F.obj (TopCat.of X)) = 0 := by
    simpa [F] using hz
  have hsub : Subsingleton (t00A04_ModTwoHomology n X) := by
    constructor
    intro a b
    have ha := congrArg (fun f ↦ f a) hidzero
    have hb := congrArg (fun f ↦ f b) hidzero
    have ha0 : a = 0 := by simpa using ha
    have hb0 : b = 0 := by simpa using hb
    exact ha0.trans hb0.symm
  exact not_subsingleton_iff_nontrivial.mpr inferInstance hsub

/-- Positive-dimensional compact boundaryless manifolds are not
null-homotopic.  This is a sorry-free assembly of the fundamental-class and
homotopy-invariance leaves. -/
theorem t00A04_positive_dimensional_manifold_identity_not_nullhomotopic
    (E X : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nontrivial X]
    [ChartedSpace E X] [IsManifold I ∞ X]
    (hdim : 0 < Module.finrank ℝ E) :
    ¬ apm_t00a04_NullHomotopic (fun x : X => x) := by
  intro hnull
  letI : BoundarylessManifold I X :=
    t00A04_boundarylessManifold_of_finiteDimensional_selfModel E X I
  letI : Nontrivial
      (t00A04_ModTwoHomology (Module.finrank ℝ E) X) :=
    t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial E X I
      t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_Type
  exact (t00A04_identity_not_nullhomotopic_of_modTwoHomology_nontrivial X
      (Module.finrank ℝ E) (Nat.ne_of_gt hdim))
    (t00A04_nullhomotopic_to_continuousMap X hnull)

/-- A nontrivial compact manifold without boundary cannot have its identity
map homotopic to a constant.  This theorem only assembles the independent
zero- and positive-dimensional leaves above. -/
theorem t00A04_manifold_identity_not_nullhomotopic
    (E X : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nontrivial X]
    [ChartedSpace E X] [IsManifold I ∞ X] :
    ¬ apm_t00a04_NullHomotopic (fun x : X => x) := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hdim | hdim
  · letI : Subsingleton E :=
      t00A04_model_subsingleton_of_finrank_zero E hdim
    letI : DiscreteTopology X :=
      t00A04_manifold_discrete_of_model_subsingleton E X I
    intro hnull
    exact t00A04_nontrivial_not_subsingleton X
      (t00A04_discrete_nullhomotopic_identity_subsingleton X hnull)
  · exact t00A04_positive_dimensional_manifold_identity_not_nullhomotopic
      E X I hdim

/-- Composing a null-homotopy with a retraction would null-homotope the
identity. -/
theorem t00A04_retract_inclusion_not_nullhomotopic
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    (ι : X → Y) (r : Y → X)
    (hr : Continuous r) (hret : ∀ x, r (ι x) = x)
    (hid : ¬ apm_t00a04_NullHomotopic (fun x : X => x)) :
    ¬ apm_t00a04_NullHomotopic ι := by
  intro hnull
  rcases hnull with ⟨y, H, hH, hH0, hH1⟩
  apply hid
  refine ⟨r y, fun z ↦ r (H z), hr.comp hH, ?_, ?_⟩
  · intro x
    change r (H (x, 0)) = x
    rw [hH0 x, hret x]
  · intro x
    change r (H (x, 1)) = r y
    rw [hH1 x]

theorem apm_t00a04 :
    ∀ (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
      [FiniteDimensional ℝ F] (I : ModelWithCorners ℝ E E)
      (J : ModelWithCorners ℝ F F)
      (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
      [T2Space X] [CompactSpace X] [Nontrivial X]
      [T2Space Y] [CompactSpace Y]
      [ChartedSpace E X] [IsManifold I ∞ X]
      [ChartedSpace F Y] [IsManifold J ∞ Y],
      ∀ (ι : C(X, Y)) (r : C(Y, X)),
      ContMDiff I J ∞ ι → ContMDiff J I ∞ r →
      (∀ x, r (ι x) = x) → ¬ apm_t00a04_NullHomotopic ι := by
  intro E F _ _ _ _ _ _ I J X Y _ _ _ _ _ _ _ _ _ _ _ ι r hι hr hret
  exact t00A04_retract_inclusion_not_nullhomotopic X Y ι r r.continuous hret
    (t00A04_manifold_identity_not_nullhomotopic E X I)

#print axioms apm_t00a04
