import Mathlib

/-! Rational singular-homology definitions of finite Euler/Lefschetz numbers.
The finite-support and finite-dimensional certificates are part of the
predicate, so the default value of trace on infinite modules cannot fabricate
an invariant. No homology computation or fixed-point formula is assumed. -/

open CategoryTheory
noncomputable section
namespace ConstructionTargets.RationalLefschetz

abbrev Homology (X : Type) [TopologicalSpace X] (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of X))

def induced {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (k : ℕ) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom f)

/-- The alternating trace, with explicit existence of legitimate homology bounds. -/
def HasLefschetzNumber {X : Type} [TopologicalSpace X]
    (f : C(X, X)) (value : ℚ) : Prop :=
  (∀ k, FiniteDimensional ℚ (Homology X k)) ∧
  ∃ bound : ℕ, (∀ k, bound < k → Subsingleton (Homology X k)) ∧
    (∑ k ∈ Finset.range (bound + 1),
      (-1 : ℚ)^k * LinearMap.trace ℚ (Homology X k) (induced f k).hom) = value

/-- Euler characteristic is the alternating trace of the actual identity map. -/
def HasEulerCharacteristic (X : Type) [TopologicalSpace X] (value : ℚ) : Prop :=
  HasLefschetzNumber (ContinuousMap.id X) value

end ConstructionTargets.RationalLefschetz
