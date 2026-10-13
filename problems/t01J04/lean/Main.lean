import Mathlib

open scoped ContDiff Manifold Topology

noncomputable section

abbrev apm_t01J04_Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A smooth manifold-with-boundary structure on `S` for which the displayed
map is a smooth immersion into the ambient manifold.  Thus the existentially
chosen atlas is not unrelated to the ambient smooth structure. -/
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

theorem apm_t01j04
    (n m : ℕ)
    (X Y : Type*)
    [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [RegularSpace Y]
    [SecondCountableTopology X]
    [ChartedSpace (apm_t01J04_Euclidean n) X]
    [ChartedSpace (apm_t01J04_Euclidean m) Y]
    [IsManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n))
      (⊤ : ℕ∞) X]
    [IsManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean m))
      (⊤ : ℕ∞) Y]
    [BoundarylessManifold
      (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n)) X]
    [BoundarylessManifold
      (modelWithCornersSelf ℝ (apm_t01J04_Euclidean m)) Y]
    (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n))
      (modelWithCornersSelf ℝ (apm_t01J04_Euclidean m)) (⊤ : ℕ∞) f)
    (y : Y) (U : Set Y) (hU : U ∈ nhds y) :
    ∃ V : Set Y,
      V ∈ nhds y ∧
      closure V ⊆ U ∧
      apm_t01J04_IsSmoothEmbeddedManifoldWithBoundary n X
        (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n))
        {x : X // x ∈ f ⁻¹' closure V} Subtype.val := by
  sorry
