import Mathlib

/-!
# APM t01J01

## Statement repairs

None.

## Encoding questions

Mathlib has no packaged genus or integral singular-homology API for surfaces.
Those two predicates are isolated as typed placeholders. The curves, their
embeddedness and disjointness, null-homotopies, annular subset, homeomorphism
`A ≃ S¹ × I`, and boundary equality remain explicit.
-/

noncomputable section

abbrev apm_t01j01_I := Set.Icc (0 : ℝ) 1

opaque apm_t01j01_IsClosedOrientableGenusTwoSurface
    (S : Type*) [TopologicalSpace S] : Prop

opaque apm_t01j01_IsNullHomologous
    {S : Type*} [TopologicalSpace S] (γ : C(Circle, S)) : Prop

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
    (S : Type*) [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (hS : apm_t01j01_IsClosedOrientableGenusTwoSurface S)
    (γ₁ γ₂ : C(Circle, S))
    (hγ₁ : IsEmbedding (γ₁ : Circle → S))
    (hγ₂ : IsEmbedding (γ₂ : Circle → S))
    (hdisjoint : Disjoint (Set.range γ₁) (Set.range γ₂))
    (hhom₁ : apm_t01j01_IsNullHomologous γ₁)
    (hhom₂ : apm_t01j01_IsNullHomologous γ₂)
    (hπ₁ : ¬apm_t01j01_IsNullHomotopic γ₁)
    (hπ₂ : ¬apm_t01j01_IsNullHomotopic γ₂) :
    ∃ A : Set S, apm_t01j01_IsAnnulusBetween A γ₁ γ₂ := by
  sorry
