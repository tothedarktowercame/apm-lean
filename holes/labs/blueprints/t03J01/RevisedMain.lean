import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Repaired statement for APM t03J01

The earlier encoding put the homological consequences of separating and
nonseparating curves into the cutting predicates.  The repair records only
whether the actual complement is connected; primitivity/null-homology must be
proved from that geometric condition.
-/

open CategoryTheory Set
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t03j01_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t03j01_Model := modelWithCornersSelf ℝ apm_t03j01_E2

abbrev apm_t03j01_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t03j01_HasGenusTwoHomology
    (X : Type) [TopologicalSpace X] : Prop :=
  Nonempty (apm_t03j01_H 0 X ≅ ModuleCat.of ℤ ℤ) ∧
  Nonempty (apm_t03j01_H 1 X ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
  Nonempty (apm_t03j01_H 2 X ≅ ModuleCat.of ℤ ℤ) ∧
  ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t03j01_H k X)

def apm_t03j01_IsCurve
    {X : Type*} [TopologicalSpace X] (J : Set X) : Prop :=
  Nonempty (Circle ≃ₜ J)

/-- Repaired: the nonseparating cut is represented by connectivity alone. -/
def apm_t03j01_CutsIntoTwicePuncturedTorus
    {X : Type} [TopologicalSpace X] (J : Set X) : Prop :=
  IsConnected (Jᶜ)

/-- Repaired: the separating cut is represented by disconnectedness alone. -/
def apm_t03j01_CutsIntoTwoOncePuncturedTori
    {X : Type} [TopologicalSpace X] (J : Set X) : Prop :=
  ¬IsConnected (Jᶜ)

def apm_t03j01_RetractsOnto
    {X : Type*} [TopologicalSpace X] (J : Set X) : Prop :=
  ∃ r : C(X, J), ∀ y : J, r y = y

theorem apm_t03j01
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [PathConnectedSpace X] [ChartedSpace apm_t03j01_E2 X]
    [IsManifold apm_t03j01_Model ∞ X]
    (hX : apm_t03j01_HasGenusTwoHomology X)
    (J₁ J₂ : Set X)
    (hcurve₁ : apm_t03j01_IsCurve J₁)
    (hcurve₂ : apm_t03j01_IsCurve J₂)
    (hcut₁ : apm_t03j01_CutsIntoTwicePuncturedTorus J₁)
    (hcut₂ : apm_t03j01_CutsIntoTwoOncePuncturedTori J₂) :
    apm_t03j01_RetractsOnto J₁ ∧
      ¬apm_t03j01_RetractsOnto J₂ := by
  sorry
