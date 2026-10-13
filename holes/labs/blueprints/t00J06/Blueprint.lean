import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Blueprint for APM t00J06

The proof is split at the natural interface between the surface-group
calculation and the covering-subgroup correspondence.  Both library lemmas
can therefore be developed independently.
-/

open CategoryTheory Set
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t00J06_Torus := Circle × Circle
abbrev apm_t00J06_E := EuclideanSpace ℝ (Fin 2)

abbrev apm_t00J06_H (k : ℕ) (S : Type) [TopologicalSpace S] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of S))

def apm_t00J06_hasGenusTwoHomology (S : Type) [TopologicalSpace S] : Prop :=
  Nonempty (apm_t00J06_H 0 S ≅ ModuleCat.of ℤ ℤ) ∧
  Nonempty (apm_t00J06_H 1 S ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) ∧
  Nonempty (apm_t00J06_H 2 S ≅ ModuleCat.of ℤ ℤ) ∧
  ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t00J06_H k S)

/-- A fixed basepoint of the product-circle model of the torus. -/
def apm_t00J06_torusBase : apm_t00J06_Torus := (1, 1)

/-- The subgroup of the surface fundamental group carried by the map from
the torus. -/
def apm_t00J06_imageSubgroup
    {S : Type} [TopologicalSpace S]
    (f : C(apm_t00J06_Torus, S)) :
    Subgroup (FundamentalGroup S (f apm_t00J06_torusBase)) :=
  (FundamentalGroup.map f apm_t00J06_torusBase).range

/-- **LIBRARY (surface classification / finite-cover homology).**  The image
of the fundamental group of a torus in a closed orientable genus-two surface
has infinite index.  Mathlib encodes infinite subgroup index by `0`. -/
theorem apm_t00J06_torus_image_index_zero
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S]
    [ChartedSpace apm_t00J06_E S]
    [IsManifold (𝓘(ℝ, apm_t00J06_E)) ∞ S]
    (hS : apm_t00J06_hasGenusTwoHomology S)
    (f : C(apm_t00J06_Torus, S)) :
    (apm_t00J06_imageSubgroup f).index = 0 := by
  sorry

/-- **LIBRARY (covering-subgroup correspondence).**  An infinite-index image
subgroup is realized by a connected cover, the original map lifts to that
cover, and cosets identify every fiber with an infinite set. -/
theorem apm_t00J06_connected_infinite_cover_of_image_index_zero
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S]
    [ChartedSpace apm_t00J06_E S]
    [IsManifold (𝓘(ℝ, apm_t00J06_E)) ∞ S]
    (f : C(apm_t00J06_Torus, S))
    (hindex : (apm_t00J06_imageSubgroup f).index = 0) :
    ∃ (X : Type*) (_ : TopologicalSpace X) (_ : ConnectedSpace X) (p : X → S),
      IsCoveringMap p ∧
      (∀ s : S, (p ⁻¹' ({s} : Set S)).Infinite) ∧
      ∃ lift : C(apm_t00J06_Torus, X), ∀ x, p (lift x) = f x := by
  sorry

/-- Every map from the torus to the closed oriented genus-two surface lifts to
a connected infinite-sheeted covering. -/
theorem apm_t00j06
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S]
    [ChartedSpace apm_t00J06_E S]
    [IsManifold (𝓘(ℝ, apm_t00J06_E)) ∞ S]
    (hS : apm_t00J06_hasGenusTwoHomology S)
    (f : C(apm_t00J06_Torus, S)) :
    ∃ (X : Type*) (_ : TopologicalSpace X) (_ : ConnectedSpace X) (p : X → S),
      IsCoveringMap p ∧
      (∀ s : S, (p ⁻¹' ({s} : Set S)).Infinite) ∧
      ∃ lift : C(apm_t00J06_Torus, X), ∀ x, p (lift x) = f x := by
  apply apm_t00J06_connected_infinite_cover_of_image_index_zero f
  exact apm_t00J06_torus_image_index_zero hS f

#print axioms apm_t00j06
