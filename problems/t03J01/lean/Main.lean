import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t03J01

## Statement repairs

The source says that cutting the genus-two surface along `J₁` gives a
twice-punctured sphere. Cutting preserves Euler characteristic, but the former
has Euler characteristic `-2` while a twice-punctured sphere has Euler
characteristic `0`. Following the intended nonseparating case used by the
solution, this is corrected to a twice-punctured torus.

## Encoding questions

The double torus is an actual compact connected 2-manifold with its integral
homology `H₀ = ℤ`, `H₁ = ℤ⁴`, `H₂ = ℤ`. Cutting is recorded by connectivity of
the actual complement together with the corresponding induced integral
homology fact: the nonseparating curve has primitive class, while the
separating curve is null-homologous.
-/

open CategoryTheory Set
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t03j01_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t03j01_Model := 𝓘(ℝ, apm_t03j01_E2)

abbrev apm_t03j01_H1 (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

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

def apm_t03j01_inclusion {X : Type} [TopologicalSpace X] (J : Set X) : C(J, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def apm_t03j01_H1Map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

def apm_t03j01_HasPrimitiveClass
    {X : Type} [TopologicalSpace X] (J : Set X) : Prop :=
  ∃ orientation : apm_t03j01_H1 J ≅ ModuleCat.of ℤ ℤ,
    ∃ dual : apm_t03j01_H1 X ⟶ ModuleCat.of ℤ ℤ,
      ∃ a : apm_t03j01_H1 J,
        orientation.hom a = 1 ∧
        dual (apm_t03j01_H1Map (apm_t03j01_inclusion J) a) = 1

def apm_t03j01_IsNullHomologous
    {X : Type} [TopologicalSpace X] (J : Set X) : Prop :=
  apm_t03j01_H1Map (apm_t03j01_inclusion J) = 0

def apm_t03j01_CutsIntoTwicePuncturedTorus
    {X : Type} [TopologicalSpace X] (J : Set X) : Prop :=
  IsConnected (Jᶜ) ∧ apm_t03j01_HasPrimitiveClass J

def apm_t03j01_CutsIntoTwoOncePuncturedTori
    {X : Type} [TopologicalSpace X] (J : Set X) : Prop :=
  ¬IsConnected (Jᶜ) ∧ apm_t03j01_IsNullHomologous J

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
