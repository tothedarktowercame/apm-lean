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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro B C M _ _ _ f hf
    exact TensorProduct.map_surjective hf Function.surjective_id
  · intro f
    refine ⟨f 1, ?_, ?_⟩
    · intro n
      simpa [mul_comm] using f.map_zsmul (1 : ℤ) n
    · intro a ha
      simpa using (ha 1).symm
  · exact ⟨TensorProduct.lid ℤ (ZMod 2)⟩
  · intro a b hab
    change 2 * a = 2 * b at hab
    omega
  · /- PASS-1 boundary: right-exactness, the classification of additive
       endomorphisms of `ℤ`, the equivalence `ℤ ⊗ ZMod 2 ≃ ZMod 2`, and
       injectivity of multiplication by two are proved above using
       `TensorProduct.map_surjective`, `AddMonoidHom.map_zsmul`, and
       `TensorProduct.lid`.  I searched `TensorProduct.lid_tmul`,
       `TensorProduct.map_tmul`, and the flat/torsion-free API.  The remaining
       blocker is proving that `TensorProduct.map (lsmul 2) id` kills the
       nonzero tensor corresponding to `1 : ZMod 2`, then generalizing this
       uniformly to `ZMod n` and transporting flatness across the cyclic-group
       classification. -/
    sorry
