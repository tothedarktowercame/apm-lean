import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t01J01

## Statement repairs

The former genus-two and null-homology hypotheses were opaque predicates.
They are replaced by a genuine compact connected 2-manifold with its
characteristic integral homology groups, and by vanishing of the morphism on
actual first singular homology induced by each curve. No source claim is
changed.

## Encoding questions

Mathlib has no packaged surface-genus predicate. As in `t00A02`, genus two is
encoded by the integral homology of an actual compact connected 2-manifold.
The curves, embeddedness, disjointness, null-homotopies, annular subset,
homeomorphism `A ≃ S¹ × I`, and boundary equality remain explicit.
-/

open CategoryTheory Set
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t01j01_I := Set.Icc (0 : ℝ) 1
abbrev apm_t01j01_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t01j01_Model := 𝓘(ℝ, apm_t01j01_E2)

abbrev apm_t01j01_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t01j01_HasGenusTwoHomology
    (S : Type) [TopologicalSpace S] : Prop :=
  Nonempty (apm_t01j01_H 0 S ≅ ModuleCat.of ℤ ℤ) ∧
  Nonempty (apm_t01j01_H 1 S ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
  Nonempty (apm_t01j01_H 2 S ≅ ModuleCat.of ℤ ℤ) ∧
  ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t01j01_H k S)

def apm_t01j01_HomologyMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (k : ℕ) (f : C(X, Y)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

def apm_t01j01_IsNullHomologous
    {S : Type} [TopologicalSpace S] (γ : C(Circle, S)) : Prop :=
  apm_t01j01_HomologyMap 1 γ = 0

def apm_t01j01_IsNullHomotopic
    {S : Type*} [TopologicalSpace S] (γ : C(Circle, S)) : Prop :=
  ∃ (x : S) (H : Circle × apm_t01j01_I → S),
    Continuous H ∧
      (∀ z : Circle, H (z, ⟨0, by norm_num⟩) = γ z) ∧
      ∀ z : Circle, H (z, ⟨1, by norm_num⟩) = x

def apm_t01j01_IsAnnulusBetween
    {S : Type*} [TopologicalSpace S]
    (A : Set S) (γ₁ γ₂ : C(Circle, S)) : Prop :=
  Nonempty (A ≃ₜ Circle × apm_t01j01_I) ∧
    frontier A = Set.range γ₁ ∪ Set.range γ₂

theorem apm_t01j01
    (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t01j01_E2 S]
    [IsManifold apm_t01j01_Model ∞ S]
    (hS : apm_t01j01_HasGenusTwoHomology S)
    (γ₁ γ₂ : C(Circle, S))
    (hγ₁ : Topology.IsEmbedding (γ₁ : Circle → S))
    (hγ₂ : Topology.IsEmbedding (γ₂ : Circle → S))
    (hdisjoint : Disjoint (Set.range γ₁) (Set.range γ₂))
    (hhom₁ : apm_t01j01_IsNullHomologous γ₁)
    (hhom₂ : apm_t01j01_IsNullHomologous γ₂)
    (hπ₁ : ¬apm_t01j01_IsNullHomotopic γ₁)
    (hπ₂ : ¬apm_t01j01_IsNullHomotopic γ₂) :
    ∃ A : Set S, apm_t01j01_IsAnnulusBetween A γ₁ γ₂ := by
  sorry
