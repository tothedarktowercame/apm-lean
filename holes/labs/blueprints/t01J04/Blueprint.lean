import Mathlib
import ConstructionTargets.SardGenuineSmoothManifoldVector

open scoped ContDiff Manifold Topology

noncomputable section

abbrev apm_t01J04_Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

def apm_t01J04_IsSmoothEmbeddedManifoldWithBoundary
    (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    (IX : ModelWithCorners ℝ (apm_t01J04_Euclidean n)
      (apm_t01J04_Euclidean n))
    (S : Type*) [TopologicalSpace S] (ι : S → X) : Prop :=
  (n = 0 ∧
    ∃ charts : ChartedSpace (apm_t01J04_Euclidean n) S,
      let _ := charts
      IsManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n))
          (⊤ : ℕ∞) S ∧
        ContMDiff (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n)) IX
          (⊤ : ℕ∞) ι ∧
        ∀ z, Function.Injective
          (mfderiv (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n)) IX ι z)) ∨
  (∃ hn : NeZero n,
    let _ := hn
    ∃ charts : ChartedSpace (EuclideanHalfSpace n) S,
      let _ := charts
      IsManifold (modelWithCornersEuclideanHalfSpace n) (⊤ : ℕ∞) S ∧
        ContMDiff (modelWithCornersEuclideanHalfSpace n) IX (⊤ : ℕ∞) ι ∧
        ∀ z, Function.Injective
          (mfderiv (modelWithCornersEuclideanHalfSpace n) IX ι z))

theorem apm_t01J04_zero_dimensional_domain
    (n m : ℕ) (hn : n = 0)
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [RegularSpace Y]
    [SecondCountableTopology X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [ChartedSpace (apm_t01J04_Euclidean m) Y]
    [IsManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n)) (⊤ : ℕ∞) X]
    [IsManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean m)) (⊤ : ℕ∞) Y]
    [BoundarylessManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n)) X]
    [BoundarylessManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean m)) Y]
    (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n))
      (modelWithCornersSelf ℝ (apm_t01J04_Euclidean m)) (⊤ : ℕ∞) f)
    (y : Y) (U : Set Y) (hU : U ∈ nhds y) :
    ∃ V : Set Y, V ∈ nhds y ∧ closure V ⊆ U ∧
      apm_t01J04_IsSmoothEmbeddedManifoldWithBoundary n X
        (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n))
        {x : X // x ∈ f ⁻¹' closure V} Subtype.val := by
  subst n
  letI : DiscreteTopology X := ChartedSpace.discreteTopology
    (apm_t01J04_Euclidean 0) X
  obtain ⟨V, hVy, hVclosed, hVU⟩ := exists_mem_nhds_isClosed_subset hU
  refine ⟨V, hVy, ?_, Or.inl ⟨rfl, ?_⟩⟩
  · rwa [hVclosed.closure_eq]
  · let charts : ChartedSpace (apm_t01J04_Euclidean 0)
        {x : X // x ∈ f ⁻¹' closure V} :=
      ChartedSpace.of_discreteTopology
    refine ⟨charts, ?_, ?_, ?_⟩
    · exact IsManifold.of_discreteTopology _
    · exact contMDiff_of_discreteTopology
    · intro z
      intro v w hvw
      unfold TangentSpace at v w
      exact Subsingleton.elim v w

/-- LIBRARY: Sard selection plus the regular-sublevel-set theorem, including
construction of the literal half-space atlas and smooth immersed inclusion. -/
theorem apm_t01J04_positive_dimensional_regular_domain
    (n m : ℕ) (hn : NeZero n)
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [RegularSpace Y]
    [SecondCountableTopology X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [ChartedSpace (apm_t01J04_Euclidean m) Y]
    [IsManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n)) (⊤ : ℕ∞) X]
    [IsManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean m)) (⊤ : ℕ∞) Y]
    [BoundarylessManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n)) X]
    [BoundarylessManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean m)) Y]
    (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n))
      (modelWithCornersSelf ℝ (apm_t01J04_Euclidean m)) (⊤ : ℕ∞) f)
    (y : Y) (U : Set Y) (hU : U ∈ nhds y) :
    ∃ V : Set Y, V ∈ nhds y ∧ closure V ⊆ U ∧
      apm_t01J04_IsSmoothEmbeddedManifoldWithBoundary n X
        (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n))
        {x : X // x ∈ f ⁻¹' closure V} Subtype.val := by
  sorry

theorem apm_t01j04
    (n m : ℕ) (X Y : Type*)
    [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [RegularSpace Y]
    [SecondCountableTopology X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [ChartedSpace (apm_t01J04_Euclidean m) Y]
    [IsManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n)) (⊤ : ℕ∞) X]
    [IsManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean m)) (⊤ : ℕ∞) Y]
    [BoundarylessManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n)) X]
    [BoundarylessManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean m)) Y]
    (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n))
      (modelWithCornersSelf ℝ (apm_t01J04_Euclidean m)) (⊤ : ℕ∞) f)
    (y : Y) (U : Set Y) (hU : U ∈ nhds y) :
    ∃ V : Set Y, V ∈ nhds y ∧ closure V ⊆ U ∧
      apm_t01J04_IsSmoothEmbeddedManifoldWithBoundary n X
        (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n))
        {x : X // x ∈ f ⁻¹' closure V} Subtype.val := by
  by_cases hn : n = 0
  · exact apm_t01J04_zero_dimensional_domain n m hn X Y f hf y U hU
  · letI : NeZero n := ⟨hn⟩
    exact apm_t01J04_positive_dimensional_regular_domain n m inferInstance X Y f hf y U hU

#print axioms apm_t01j04
