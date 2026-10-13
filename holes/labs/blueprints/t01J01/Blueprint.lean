import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.Surfaces
import ConstructionTargets.SurfaceClassification

/-! # Blueprint for APM t01J01 -/

open CategoryTheory Set
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t01j01_I := Set.Icc (0 : ℝ) 1
abbrev apm_t01j01_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t01j01_Model := 𝓘(ℝ, apm_t01j01_E2)

abbrev apm_t01j01_H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

/-- `S` is homeomorphic to the standard closed orientable genus-two polygon
surface. -/
def apm_t01j01_IsGenusTwoSurface
    (S : Type) [TopologicalSpace S] : Prop :=
  Nonempty (S ≃ₜ ConstructionTargets.Surfaces.Surface true 2)

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

/-- **LIBRARY: homology/intersection theory for oriented surfaces.**
An embedded circle with zero integral first-homology class separates the
closed orientable surface. -/
theorem apm_t01J01_nullHomologySeparates
    (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t01j01_E2 S]
    [IsManifold apm_t01j01_Model ∞ S]
    (hS : apm_t01j01_IsGenusTwoSurface S)
    (γ : C(Circle, S))
    (hγ : Topology.IsEmbedding (γ : Circle → S))
    (hhom : apm_t01j01_IsNullHomologous γ) :
    ¬IsPreconnected ((Set.range γ)ᶜ : Set S) := by
  sorry

/-- **LIBRARY: cutting and classification of compact orientable surfaces.**
Two disjoint essential separating circles in a closed genus-two surface
cobound a closed annular subsurface with exactly the prescribed frontier. -/
theorem apm_t01J01_separatingCurvesCoboundAnnulus
    (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t01j01_E2 S]
    [IsManifold apm_t01j01_Model ∞ S]
    (hS : apm_t01j01_IsGenusTwoSurface S)
    (γ₁ γ₂ : C(Circle, S))
    (hγ₁ : Topology.IsEmbedding (γ₁ : Circle → S))
    (hγ₂ : Topology.IsEmbedding (γ₂ : Circle → S))
    (hdisjoint : Disjoint (Set.range γ₁) (Set.range γ₂))
    (hsep₁ : ¬IsPreconnected ((Set.range γ₁)ᶜ : Set S))
    (hsep₂ : ¬IsPreconnected ((Set.range γ₂)ᶜ : Set S))
    (hπ₁ : ¬apm_t01j01_IsNullHomotopic γ₁)
    (hπ₂ : ¬apm_t01j01_IsNullHomotopic γ₂) :
    ∃ A : Set S, apm_t01j01_IsAnnulusBetween A γ₁ γ₂ := by
  sorry

theorem apm_t01j01
    (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S] [ChartedSpace apm_t01j01_E2 S]
    [IsManifold apm_t01j01_Model ∞ S]
    (hS : apm_t01j01_IsGenusTwoSurface S)
    (γ₁ γ₂ : C(Circle, S))
    (hγ₁ : Topology.IsEmbedding (γ₁ : Circle → S))
    (hγ₂ : Topology.IsEmbedding (γ₂ : Circle → S))
    (hdisjoint : Disjoint (Set.range γ₁) (Set.range γ₂))
    (hhom₁ : apm_t01j01_IsNullHomologous γ₁)
    (hhom₂ : apm_t01j01_IsNullHomologous γ₂)
    (hπ₁ : ¬apm_t01j01_IsNullHomotopic γ₁)
    (hπ₂ : ¬apm_t01j01_IsNullHomotopic γ₂) :
    ∃ A : Set S, apm_t01j01_IsAnnulusBetween A γ₁ γ₂ := by
  apply apm_t01J01_separatingCurvesCoboundAnnulus S hS γ₁ γ₂ hγ₁ hγ₂ hdisjoint
  · exact apm_t01J01_nullHomologySeparates S hS γ₁ hγ₁ hhom₁
  · exact apm_t01J01_nullHomologySeparates S hS γ₂ hγ₂ hhom₂
  · exact hπ₁
  · exact hπ₂

#print axioms apm_t01j01
