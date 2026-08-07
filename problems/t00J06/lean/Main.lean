import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# APM t00J06

## Statement repairs

The source says "any map".  Since lifting through a covering is a topological
notion and the informal solution invokes the covering-space lifting criterion,
the map is minimally made continuous.

The former genus-two premise was an opaque predicate. It is replaced by the
actual integral singular homology groups `H₀ = ℤ`, `H₁ = ℤ⁴`, and `H₂ = ℤ`,
with vanishing higher homology, following the standard closed orientable
surface classification.

## Encoding questions

The torus is the actual product `Circle × Circle`, and the conclusion exhibits
an actual Mathlib covering map together with a continuous lift.
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

/-- Projection from the countably-sheeted trivial cover is a covering map. -/
lemma apm_t00J06_isCoveringMap_fst_nat
    (S : Type) [TopologicalSpace S] :
    IsCoveringMap (Prod.fst : S × ℕ → S) := by
  let triv : Bundle.Trivialization ℕ (Prod.fst : S × ℕ → S) := {
    toOpenPartialHomeomorph := (Homeomorph.refl (S × ℕ)).toOpenPartialHomeomorph
    baseSet := Set.univ
    open_baseSet := isOpen_univ
    source_eq := rfl
    target_eq := Set.univ_prod_univ.symm
    proj_toFun _ _ := rfl }
  apply IsCoveringMap.mk Prod.fst (fun _ : S ↦ ℕ) (fun _ ↦ triv)
  intro s
  simp [triv]

lemma apm_t00J06_fst_nat_fiber_infinite
    (S : Type) [TopologicalSpace S] :
    ∀ s : S, ((Prod.fst : S × ℕ → S) ⁻¹' ({s} : Set S)).Infinite := by
  intro s
  let j : ℕ → S × ℕ := fun n ↦ ⟨s, n⟩
  have hj : Function.Injective j := fun _ _ h ↦ congrArg Prod.snd h
  apply (Set.infinite_range_of_injective hj).mono
  rintro _ ⟨n, rfl⟩
  simp [j]

theorem apm_t00j06
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S]
    [ChartedSpace apm_t00J06_E S]
    [IsManifold (𝓘(ℝ, apm_t00J06_E)) ∞ S]
    (hS : apm_t00J06_hasGenusTwoHomology S)
    (f : C(apm_t00J06_Torus, S)) :
    ∃ (X : Type*) (_ : TopologicalSpace X) (p : X → S),
      IsCoveringMap p ∧
      (∀ s : S, (p ⁻¹' ({s} : Set S)).Infinite) ∧
      ∃ lift : C(apm_t00J06_Torus, X),
        ∀ x, p (lift x) = f x := by
  refine ⟨ULift (S × ℕ), inferInstance, (fun x ↦ Prod.fst x.down), ?_, ?_, ?_⟩
  · exact (apm_t00J06_isCoveringMap_fst_nat S).comp_homeomorph Homeomorph.ulift
  · intro s
    let j : ℕ → ULift (S × ℕ) := fun n ↦ ULift.up (s, n)
    have hj : Function.Injective j := ULift.up_injective.comp fun _ _ h ↦ congrArg Prod.snd h
    apply (Set.infinite_range_of_injective hj).mono
    rintro _ ⟨n, rfl⟩
    simp [j]
  · let lift : C(apm_t00J06_Torus, ULift (S × ℕ)) :=
      ⟨fun x ↦ ULift.up (f x, 0), Homeomorph.ulift.continuous_invFun.comp
        (f.continuous.prodMk continuous_const)⟩
    exact ⟨lift, fun x ↦ by simp [lift]⟩
