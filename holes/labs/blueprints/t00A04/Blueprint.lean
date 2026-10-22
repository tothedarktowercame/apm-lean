import Mathlib
import ConstructionTargets.SingularHomologyHomotopy
import ConstructionTargets.CoefficientRadialPair
import ConstructionTargets.CoefficientCompactComplementTransportedExactness
import ConstructionTargets.CoefficientModelLocal
import ConstructionTargets.CoefficientManifoldLocalComparison

open scoped ContDiff Manifold
open CategoryTheory

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
theorem t00A04_boundarylessManifold_of_finiteDimensional_selfModel
    (E X : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : ModelWithCorners ℝ E E)
    [TopologicalSpace X] [ChartedSpace E X] [IsManifold I ∞ X] :
    BoundarylessManifold I X := by
  sorry

/-- **LIBRARY F1.** Hatcher 3.27 for a compact convex subset of the
finite-dimensional Euclidean model. -/
theorem t00A04_hatcherConclusion_compact_convex_euclidean
    (d : ℕ) (A : Set (EuclideanSpace ℝ (Fin d)))
    (hA : IsCompact A) (hconv : Convex ℝ A) :
    t00A04_HatcherConclusion (EuclideanSpace ℝ (Fin d)) d A := by
  sorry

/-- **LIBRARY F2.** The relative compact-complement Mayer--Vietoris union
step in Hatcher 3.27.  Its three inputs are explicit so seats are independent. -/
theorem t00A04_hatcherConclusion_union
    (X : Type) [TopologicalSpace X] [T2Space X] (d : ℕ)
    (A B : Set X) (hA : IsCompact A) (hB : IsCompact B)
    (hAi : t00A04_HatcherConclusion X d A)
    (hBi : t00A04_HatcherConclusion X d B)
    (hABi : t00A04_HatcherConclusion X d (A ∩ B))
    (hloc : ∀ x : X, ∀ a b : t00A04_ModTwoLocalHomology X {x} d,
      a ≠ 0 → b ≠ 0 → a = b) :
    t00A04_HatcherConclusion X d (A ∪ B) := by
  sorry

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
  sorry

theorem t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_one_aux_coordinates :
    (t00A04_modTwoLocalHomology_unique_nonzero_aux_euclidean_aux_origin_one_aux_punctureIso).hom ≫
        ConstructionTargets.CoefficientCodiagonalKernel.sumMap (ZMod 2) =
      HomologicalComplex.homologyMap
          (ConstructionTargets.CoefficientRelativeSmall.subspaceMap (ZMod 2)
          (ConstructionTargets.CoefficientModelLocal.puncture 1)) 0 ≫
        (ConstructionTargets.CoefficientH0.h0Iso (ZMod 2)
          (0 : EuclideanSpace ℝ (Fin 1))).hom := by
  sorry

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

/-- **LIBRARY F3e.** Hatcher's relative-cycle argument extends the Euclidean
result from finite unions of compact convex sets to every compact set. -/
theorem t00A04_hatcherConclusion_compact_euclidean
    (d : ℕ)
    (hfinite : ∀ (s : Finset (Set (EuclideanSpace ℝ (Fin d)))),
      (∀ A ∈ s, IsCompact A ∧ Convex ℝ A) →
      t00A04_HatcherConclusion _ d (⋃ A ∈ s, A))
    (A : Set (EuclideanSpace ℝ (Fin d))) (hA : IsCompact A) :
    t00A04_HatcherConclusion _ d A := by
  sorry

/-- **LIBRARY (chart transport).** The all-compact Euclidean result transported
to an arbitrary compact subset contained in one chart source. -/
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
  sorry

/-- **LIBRARY F3.** Finite chart induction.  Arbitrary compact single-chart
sets, the union step, and local uniqueness are explicit hypotheses. -/
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
  sorry

/-- **LIBRARY F4.** At support `A = X`, a nonzero relative fundamental class
is a nonzero absolute top-homology class. -/
theorem t00A04_top_homology_nontrivial_of_hatcherConclusion_univ
    (X : Type) [TopologicalSpace X] [Nonempty X] (d : ℕ)
    (h : t00A04_HatcherConclusion X d Set.univ) :
    Nontrivial (t00A04_ModTwoHomology d X) := by
  sorry

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
  sorry

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
