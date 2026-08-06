import Mathlib

/-!
# APM t01J04: regular preimages of closed neighborhoods

## Statement repairs

None.

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
  /-
  Boundary (skipped): even the topological shrinking step requires
  `RegularSpace Y`, which is not implied by the frozen Mathlib manifold
  hypotheses (instance synthesis confirms this). Thus the statement is false
  without a separation axiom: a non-Hausdorff locally Euclidean manifold such
  as the line with doubled origin has a neighborhood `U` of one origin for
  which every smaller neighborhood has closure containing the other origin.
  Taking `f` to be the identity already defeats `closure V ⊆ U`. Beyond that,
  the intended proof also needs manifold Sard and a regular-sublevel theorem
  constructing half-space charts. I searched the `mfderiv`, critical-value,
  Sard, submersion, model-with-corners, and subtype-chart APIs; those packaged
  results are not available in the required generality.
  -/
  sorry
