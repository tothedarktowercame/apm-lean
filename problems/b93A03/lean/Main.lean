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
  · have hmap_not_injective (n : ℕ) (hn : 2 ≤ n) :
        ¬Function.Injective
          (TensorProduct.map ((LinearMap.lsmul ℤ ℤ) (n : ℤ))
            (LinearMap.id : ZMod n →ₗ[ℤ] ZMod n)) := by
      intro hinj
      let z : TensorProduct ℤ ℤ (ZMod n) := (1 : ℤ) ⊗ₜ[ℤ] (1 : ZMod n)
      have hz0 : z ≠ 0 := by
        intro hz
        have := congrArg (TensorProduct.lid ℤ (ZMod n)) hz
        have hone : (1 : ZMod n) ≠ 0 := by
          intro h10
          have h10' : ((1 : ℤ) : ZMod n) = ((0 : ℤ) : ZMod n) := by simpa using h10
          have hd : (n : ℤ) ∣ -1 := by
            simpa using (ZMod.intCast_eq_intCast_iff_dvd_sub 1 0 n).mp h10'
          have hle := Int.natAbs_le_of_dvd_ne_zero hd (by norm_num : (-1 : ℤ) ≠ 0)
          simp at hle
          omega
        exact hone (by simpa [z] using this)
      apply hz0
      apply hinj
      apply (TensorProduct.lid ℤ (ZMod n)).injective
      simp [z, TensorProduct.map_tmul]
    refine ⟨hmap_not_injective 2 (by omega), ?_, ?_, ?_, ?_⟩
    · intro B C _ _ f hf x y hxy
      apply (TensorProduct.rid ℤ B).injective
      apply hf
      have h := congrArg (TensorProduct.rid ℤ C) hxy
      have hnat (w : TensorProduct ℤ B ℤ) :
          TensorProduct.rid ℤ C (TensorProduct.map f LinearMap.id w) =
            f (TensorProduct.rid ℤ B w) := by
        induction w using TensorProduct.induction_on with
        | zero => simp
        | tmul b z => simp [TensorProduct.map_tmul]
        | add x y hx hy => simp [hx, hy]
      simpa [hnat] using h
    · intro B C _ _ f hf x y _
      exact Subsingleton.elim x y
    · intro n hn hflat
      exact hmap_not_injective n hn (hflat ℤ ℤ ((LinearMap.lsmul ℤ ℤ) (n : ℤ)) (by
        intro a b hab
        change (n : ℤ) * a = n * b at hab
        have hn0 : (n : ℤ) ≠ 0 := by omega
        exact mul_left_cancel₀ hn0 hab))
    · /- PASS-1 boundary: right-exactness, the classification of additive
       endomorphisms of `ℤ`, the equivalence `ℤ ⊗ ZMod 2 ≃ ZMod 2`, and
       injectivity of multiplication by two are proved above using
       `TensorProduct.map_surjective`, `AddMonoidHom.map_zsmul`, and
       `TensorProduct.lid`.  The counterexample is now proved uniformly for
       every `ZMod n`, `2 ≤ n`, by the nonzero tensor `1 ⊗ₜ 1`; flatness of
       `ℤ` follows by `TensorProduct.rid`, and `ZMod 1` is subsingleton.

       The remaining classification boundary is transport of this custom
       source-oriented flatness predicate across an additive equivalence.
       Research found `intCyclicAddEquiv` for infinite cyclic groups and
       `zmodAddCyclicAddEquiv` for finite cyclic groups, as well as
       `Module.Flat.iff_rTensor_preserves_injective_linearMapₛ` and
       `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`.  A closure route is
       to prove `apm_b93a03_flat M ↔ Module.Flat ℤ M`, use torsion-freeness to
       exclude every finite cyclic group of cardinality at least two, and
       transport the positive cases through `intCyclicAddEquiv`.  I did not
       complete the universe/equivalence transport bridge in this pass. -/
      sorry
