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

private theorem apm_b93a03_flat_int : apm_b93a03_flat ℤ := by
  intro B C _ _ f hf x y hxy
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

-- Flatness in the statement is invariant under an additive equivalence.  Over
-- `ℤ`, every additive equivalence is automatically a linear equivalence.
private theorem apm_b93a03_flat_of_addEquiv {M N : Type}
    [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) :
    apm_b93a03_flat M → apm_b93a03_flat N := by
  intro h B C _ _ f hf x y hxy
  let eL : M ≃ₗ[ℤ] N := e.toIntLinearEquiv
  let EB : TensorProduct ℤ B M ≃ₗ[ℤ] TensorProduct ℤ B N := eL.lTensor B
  let EC : TensorProduct ℤ C M ≃ₗ[ℤ] TensorProduct ℤ C N := eL.lTensor C
  apply EB.symm.injective
  apply h B C f hf
  apply EC.injective
  have hn (z : TensorProduct ℤ B N) :
      EC (TensorProduct.map f LinearMap.id (EB.symm z)) =
        TensorProduct.map f LinearMap.id z := by
    induction z using TensorProduct.induction_on with
    | zero => simp [EB, EC]
    | tmul b n =>
        have hb : EB.symm (b ⊗ₜ[ℤ] n) = b ⊗ₜ[ℤ] eL.symm n := by
          exact LinearEquiv.lTensor_symm_tmul (M := B) eL b n
        rw [hb, TensorProduct.map_tmul]
        have hc : EC (f b ⊗ₜ[ℤ] eL.symm n) = f b ⊗ₜ[ℤ] n := by
          dsimp [EC]
          change f b ⊗ₜ[ℤ] eL (eL.symm n) = f b ⊗ₜ[ℤ] n
          rw [eL.apply_symm_apply]
        exact hc
    | add x y hx hy => simp [hx, hy]
  rw [hn x, hn y]
  exact hxy

private theorem apm_b93a03_flat_addEquiv {M N : Type}
    [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) :
    apm_b93a03_flat M ↔ apm_b93a03_flat N :=
  ⟨apm_b93a03_flat_of_addEquiv e, apm_b93a03_flat_of_addEquiv e.symm⟩

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
    · -- Mathlib: `intCyclicAddEquiv`, `zmodAddCyclicAddEquiv`.
      -- Flatness is transported by `apm_b93a03_flat_addEquiv` above.
      intro M _ hcyc
      cases finite_or_infinite M with
      | inr hinf =>
          letI : Infinite M := hinf
          constructor
          · intro _
            exact Or.inl ⟨(intCyclicAddEquiv (G := M)).symm⟩
          · intro he
            rcases he with he | hsub
            · rcases he with ⟨e⟩
              exact (apm_b93a03_flat_addEquiv e).mpr apm_b93a03_flat_int
            · exact False.elim (not_subsingleton M hsub)
      | inl hfin =>
          letI : Finite M := hfin
          let e : ZMod (Nat.card M) ≃+ M := zmodAddCyclicAddEquiv hcyc
          by_cases hsub : Subsingleton M
          · constructor
            · intro _
              exact Or.inr hsub
            · intro _ B C _ _ f hf x y _
              exact Subsingleton.elim x y
          · have hcard : 2 ≤ Nat.card M := by
              have hpos : 0 < Nat.card M := Nat.card_pos
              have hne : Nat.card M ≠ 1 := by
                intro hc
                exact hsub ((Nat.card_eq_one_iff_unique.mp hc).1)
              omega
            constructor
            · intro hflat
              have hzflat : apm_b93a03_flat (ZMod (Nat.card M)) :=
                (apm_b93a03_flat_addEquiv e).mpr hflat
              exact False.elim (hmap_not_injective (Nat.card M) hcard
                (hzflat ℤ ℤ ((LinearMap.lsmul ℤ ℤ) (Nat.card M : ℤ)) (by
                  intro a b hab
                  change (Nat.card M : ℤ) * a = Nat.card M * b at hab
                  exact mul_left_cancel₀ (by omega) hab)))
            · intro he
              rcases he with he | hs
              · rcases he with ⟨eM⟩
                letI : Finite ℤ := Finite.of_equiv M eM.toEquiv
                exact False.elim (not_finite ℤ)
              · exact False.elim (hsub hs)
