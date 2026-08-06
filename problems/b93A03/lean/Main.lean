import Mathlib

/-!
# APM b93A03 — tensor exactness and flat cyclic abelian groups

## Statement repairs

None.

## Encoding notes

Abelian groups are represented as `ℤ`-modules.  Flatness is defined from the
source definition itself: tensoring with `M` preserves injectivity of every
`ℤ`-linear map.  It is not replaced by the equivalent torsion-free criterion.
-/

def apm_b93a03_flat (M : Type) [AddCommGroup M] : Prop :=
  ∀ (B C : Type) [AddCommGroup B] [AddCommGroup C]
    (f : B →ₗ[ℤ] C), Function.Injective f →
      Function.Injective
        (TensorProduct.map f (LinearMap.id : M →ₗ[ℤ] M))

theorem apm_b93a03 :
    (∀ (B C M : Type) [AddCommGroup B] [AddCommGroup C] [AddCommGroup M]
      (f : B →ₗ[ℤ] C), Function.Surjective f →
        Function.Surjective
          (TensorProduct.map f (LinearMap.id : M →ₗ[ℤ] M))) ∧
    (∀ f : ℤ →+ ℤ, ∃! a : ℤ, ∀ n : ℤ, f n = a * n) ∧
    Nonempty (TensorProduct ℤ ℤ (ZMod 2) ≃ₗ[ℤ] ZMod 2) ∧
    Function.Injective ((LinearMap.lsmul ℤ ℤ) 2) ∧
    ¬Function.Injective
      (TensorProduct.map ((LinearMap.lsmul ℤ ℤ) 2)
        (LinearMap.id : ZMod 2 →ₗ[ℤ] ZMod 2)) ∧
    apm_b93a03_flat ℤ ∧
    apm_b93a03_flat (ZMod 1) ∧
    (∀ n : ℕ, 2 ≤ n → ¬apm_b93a03_flat (ZMod n)) ∧
    (∀ (M : Type) [AddCommGroup M] [IsAddCyclic M],
      apm_b93a03_flat M ↔ Nonempty (M ≃+ ℤ) ∨ Subsingleton M) := by
  sorry
