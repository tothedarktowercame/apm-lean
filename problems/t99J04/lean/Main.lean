import Mathlib

/-!
# APM t99J04 — inverse function theorem and compact local diffeomorphisms

## Statement repairs

In part (a), `X in an n-dimensional manifold` is read as `X is an
n-dimensional manifold`. In part (b), the customary implicit assumption that
the manifold `X` is nonempty is made explicit: without it the empty compact
manifold would give a counterexample to surjectivity.

## Encoding questions

None. The differentials, their linear independence, local coordinate systems,
and the everywhere-invertible derivative are represented by Mathlib's genuine
manifold derivative and local-diffeomorphism structures.
-/

open scoped Manifold

noncomputable section

abbrev apm_t99J04_Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

def apm_t99J04_coordinateMap {n : ℕ} {X : Type} (f : Fin n → X → ℝ) :
    X → apm_t99J04_Euclidean n :=
  fun p ↦ WithLp.toLp 2 (fun i ↦ f i p)

theorem apm_t99j04 :
    (∀ (n : ℕ) (X : Type) [TopologicalSpace X]
      [ChartedSpace (apm_t99J04_Euclidean n) X]
      [IsManifold (𝓘(ℝ, apm_t99J04_Euclidean n)) ⊤ X]
      (x : X) (f : Fin n → X → ℝ),
      (∀ i, ContMDiff (𝓘(ℝ, apm_t99J04_Euclidean n)) 𝓘(ℝ, ℝ) ⊤ (f i)) →
      LinearIndependent ℝ
        (fun i : Fin n ↦
          (NormedSpace.fromTangentSpace (f i x)).toContinuousLinearMap ∘L
            mfderiv (𝓘(ℝ, apm_t99J04_Euclidean n)) 𝓘(ℝ, ℝ) (f i) x) →
      IsLocalDiffeomorphAt (𝓘(ℝ, apm_t99J04_Euclidean n))
        𝓘(ℝ, apm_t99J04_Euclidean n) ⊤ (apm_t99J04_coordinateMap f) x) ∧
    (∀ (E E' : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
      [NormedAddCommGroup E'] [NormedSpace ℝ E']
      [FiniteDimensional ℝ E'] [CompleteSpace E']
      (X Y : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
      [Nonempty X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ⊤ X]
      [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
      [ChartedSpace E' Y] [IsManifold (𝓘(ℝ, E')) ⊤ Y]
      (f : X → Y),
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E')) ⊤ f →
      (∀ x, Function.Bijective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E')) f x)) →
      Function.Surjective f) := by
  sorry
