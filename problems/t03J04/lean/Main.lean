import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t03J04: Euler characteristic under a torus local diffeomorphism

## Statement repairs

* We assume `n ≥ 1`.  For `n = 0`, the requested first-coordinate vector
  field does not exist and `T⁰` has Euler characteristic `1`, not `0`.
* We assume `X` is connected.  Otherwise the torus maps onto one component
  while arbitrary additional components make the Euler characteristic of all
  of `X` unconstrained.

## Encoding questions

Mathlib does not provide orientations of manifolds.  Orientation preservation
is therefore a documented `sorry`-typed predicate on the actual smooth local
diffeomorphism.  The torus is the genuine finite product of circles, the
constant vector field is explicit in its standard global frame, and Euler
characteristic is the alternating sum of rational singular-homology ranks.
-/

open CategoryTheory
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t03J04_Torus (n : ℕ) := Fin n → Circle
abbrev apm_t03J04_E (n : ℕ) :=
  Fin n → EuclideanSpace ℝ (Fin 1)
abbrev apm_t03J04_HModel (n : ℕ) :=
  ModelPi (fun _ : Fin n ↦ EuclideanSpace ℝ (Fin 1))
abbrev apm_t03J04_Model (n : ℕ) :=
  ModelWithCorners.pi (fun _ : Fin n ↦
    modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))

def apm_t03J04_constantVectorField (n : ℕ) [NeZero n] :
    apm_t03J04_Torus n → apm_t03J04_E n :=
  fun _ i ↦ if i = 0 then EuclideanSpace.single 0 (1 : ℝ) else 0

abbrev apm_t03J04_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of X))

def apm_t03J04_eulerCharacteristic (n : ℕ) (X : Type)
    [TopologicalSpace X] : ℤ :=
  ∑ k : Fin (n + 1),
    (-1 : ℤ) ^ (k : ℕ) * (Module.finrank ℚ (apm_t03J04_H k X) : ℤ)

def apm_t03J04_IsOrientationPreserving
    {n : ℕ} {X : Type}
    [TopologicalSpace X] [ChartedSpace (apm_t03J04_E n) X]
    (_phi : apm_t03J04_Torus n → X) : Prop := by
  sorry

theorem apm_t03j04
    (n : ℕ) [NeZero n]
    [ChartedSpace (apm_t03J04_HModel n) (apm_t03J04_Torus n)]
    [IsManifold (apm_t03J04_Model n) (⊤ : ℕ∞) (apm_t03J04_Torus n)] :
    (∀ q : apm_t03J04_Torus n,
      apm_t03J04_constantVectorField n q ≠ 0) ∧
    apm_t03J04_eulerCharacteristic n (apm_t03J04_Torus n) = 0 ∧
    ∀ (X : Type)
        [TopologicalSpace X]
        [ChartedSpace (apm_t03J04_E n) X]
        [IsManifold (modelWithCornersSelf ℝ (apm_t03J04_E n))
          (⊤ : ℕ∞) X]
        [BoundarylessManifold
          (modelWithCornersSelf ℝ (apm_t03J04_E n)) X]
        [ConnectedSpace X]
        (phi : apm_t03J04_Torus n → X),
      IsLocalDiffeomorph (apm_t03J04_Model n)
          (modelWithCornersSelf ℝ (apm_t03J04_E n)) (⊤ : ℕ∞) phi →
      apm_t03J04_IsOrientationPreserving phi →
      apm_t03J04_eulerCharacteristic n X = 0 := by
  sorry
