import Mathlib

/-!
# APM t95J04 — low-dimensional maps to spheres and six-manifolds

Part (a) uses genuine finite-dimensional Mathlib manifolds and `ContMDiff`
maps.  The Sard/dimension consequence—nullity of the image and hence failure
of surjectivity—is in the conclusion, not stored in the definition of a
“smooth map.”  Part (b) uses the concrete metric spheres and their products.

## Statement repairs

None.

## Encoding questions

Non-diffeomorphism in part (b) is stated via the stronger conclusion that the
underlying spaces are not homeomorphic.  This avoids introducing a surrogate
diffeomorphism predicate while still implying the source claim.
-/

open Set MeasureTheory
open scoped ContDiff Manifold ENNReal

noncomputable section

abbrev T95J04E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev T95J04I (n : ℕ) := 𝓘(ℝ, T95J04E n)
abbrev T95J04Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

abbrev T95J04SphereSix := T95J04Sphere 6
abbrev T95J04SphereTwoFour := T95J04Sphere 2 × T95J04Sphere 4
abbrev T95J04SphereThreeThree := T95J04Sphere 3 × T95J04Sphere 3

def t95J04NullHomotopic {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf : Continuous f) : Prop :=
  ∃ y : Y,
    ContinuousMap.Homotopic ⟨f, hf⟩ (ContinuousMap.const X y)

theorem apm_t95j04 :
    (∀ (k n : ℕ), k < n →
      ∀ (M : Type*) [TopologicalSpace M] [T2Space M]
        [SecondCountableTopology M] [CompactSpace M]
        [ChartedSpace (T95J04E k) M] [IsManifold (T95J04I k) ∞ M]
        (f : M → T95J04Sphere n),
        ∀ hf : ContMDiff (T95J04I k) (T95J04I n) ∞ f,
        μH[n] (Set.range f) = 0 ∧
        ¬ Function.Surjective f ∧
        t95J04NullHomotopic f hf.continuous) ∧
    SimplyConnectedSpace T95J04SphereSix ∧
    SimplyConnectedSpace T95J04SphereTwoFour ∧
    SimplyConnectedSpace T95J04SphereThreeThree ∧
    ¬ Nonempty (T95J04SphereSix ≃ₜ T95J04SphereTwoFour) ∧
    ¬ Nonempty (T95J04SphereSix ≃ₜ T95J04SphereThreeThree) ∧
    ¬ Nonempty (T95J04SphereTwoFour ≃ₜ T95J04SphereThreeThree) := by
  sorry
