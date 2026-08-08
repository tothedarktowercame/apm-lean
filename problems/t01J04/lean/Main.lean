import Mathlib

/-!
# APM t01J04 — regular preimages of closed neighborhoods

## Statement repairs

Mathlib's manifold typeclasses do not include the usual Hausdorff separation
convention.  `T2Space` is therefore required for both manifolds, and
`RegularSpace Y` is required explicitly for the neighborhood-shrinking step
`closure V ⊆ U`.  Without it, the line with doubled origin gives a
counterexample even for the identity map.

## Encoding questions

The manifolds are encoded as finite-dimensional real smooth manifolds without
boundary.  The conclusion uses the standard Euclidean half-space model when
the source dimension is positive, and the ordinary Euclidean model in
dimension zero.  Thus "manifold with boundary" is not weakened to a
regularity condition or to a scalar surrogate.
-/

open scoped ContDiff Manifold Topology

noncomputable section

abbrev apm_t01J04_Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

def apm_t01J04_IsSmoothManifoldWithBoundary (n : ℕ) (S : Type*)
    [TopologicalSpace S] : Prop :=
  (n = 0 ∧
    ∃ charts : ChartedSpace (apm_t01J04_Euclidean n) S,
      let _ := charts
      IsManifold (modelWithCornersSelf ℝ (apm_t01J04_Euclidean n))
        (⊤ : ℕ∞) S) ∨
  (∃ hn : NeZero n,
    let _ := hn
    ∃ charts : ChartedSpace (EuclideanHalfSpace n) S,
      let _ := charts
      IsManifold (modelWithCornersEuclideanHalfSpace n) (⊤ : ℕ∞) S)

theorem apm_t01j04
    (n m : ℕ)
    (X Y : Type*)
    [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [RegularSpace Y]
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
      apm_t01J04_IsSmoothManifoldWithBoundary n
        {x : X // x ∈ f ⁻¹' closure V} := by
  sorry
