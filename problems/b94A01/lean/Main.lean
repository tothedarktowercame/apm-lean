import Mathlib

/-!
# APM b94A01

## Statement repairs

The displayed ten-element list in part (d) repeats no element in place of the
missing element `x`; it is understood as the standard normal-form list
`1, x, x², x³, x⁴, y, xy, x²y, x³y, x⁴y`. The lowercase `q` is corrected to
the previously defined subgroup `Q`.

## Encoding questions

None. `P` and `Q` are Mathlib Sylow subgroups, their generators live in the
subgroup types, and part (c) uses Mathlib's actual semidirect product.
-/

theorem apm_b94a01 :
    ∀ (G : Type*) [Group G] [Fintype G]
        (P : Sylow 5 G) (Q : Sylow 2 G) (x : P) (y : Q),
      Fintype.card G = 10 →
      Subgroup.zpowers x = ⊤ →
      Subgroup.zpowers y = ⊤ →
      ∃ Ψ : Fin 4 → MulAut P,
        Function.Injective Ψ ∧
        (∀ φ : MulAut P, ∃ n : Fin 4, φ = Ψ n) ∧
        (∀ (n : Fin 4) (i : ℕ), Ψ n (x ^ i) = x ^ (((n : ℕ) + 1) * i)) ∧
        (∃ φtriv φinv : Q →* MulAut P,
          φtriv y = Ψ 0 ∧
          φinv y = Ψ 3 ∧
          φtriv ≠ φinv ∧
          ∀ φ : Q →* MulAut P, φ = φtriv ∨ φ = φinv) ∧
        ((P : Subgroup G).Normal ∧
          Disjoint (P : Subgroup G) (Q : Subgroup G) ∧
          (P : Subgroup G) ⊔ (Q : Subgroup G) = ⊤ ∧
          ∃ φ : Q →* MulAut P, Nonempty (G ≃* (P ⋊[φ] Q))) ∧
        ((∃ a b : G, a * b ≠ b * a) →
          (y : G) * (x : G) = ((x ^ 4 : P) : G) * (y : G) ∧
          (((x ^ 2 : P) : G) * (y : G)) * (((x ^ 3 : P) : G) * (y : G)) =
            ((x ^ 4 : P) : G)) := by
  intro G _ _ P Q x y hcard hx hy
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  -- (Sibling: b93A01)
  have hPcard : Nat.card (P : Subgroup G) = 5 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, hcard]
    have hv : (Nat.factorization 10) 5 = 1 := by native_decide
    rw [hv]
    norm_num
  have hQcard : Nat.card (Q : Subgroup G) = 2 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, hcard]
    have hv : (Nat.factorization 10) 2 = 1 := by native_decide
    rw [hv]
    norm_num
  have hPindex : (P : Subgroup G).index = 2 := by
    have hm := Subgroup.card_mul_index (P : Subgroup G)
    rw [hPcard, Nat.card_eq_fintype_card, hcard] at hm
    omega
  have hSylow5card : Nat.card (Sylow 5 G) = 1 := by
    have hdvd : Nat.card (Sylow 5 G) ∣ 2 := hPindex ▸ Sylow.card_dvd_index P
    have hmod := card_sylow_modEq_one 5 G
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h | h
    · exact h
    · rw [h] at hmod
      norm_num [Nat.ModEq] at hmod
  haveI : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp hSylow5card).1
  have hPnormal : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  /- PASS-1 boundary: the Sylow sizes and normality of `P` are now proved
     locally (`hPcard`, `hQcard`, `hPnormal`) using the route validated in
     sibling `b93A01`.  I searched the Sylow and cyclic-group APIs, including
     `Sylow.card_eq_multiplicity`, `card_sylow_modEq_one`,
     `Sylow.normal_of_subsingleton`, `IsCyclic.mulAutMulEquiv`, and
     `IsCyclic.card_mulAut`, together with the semidirect-product recognition
     results.  The remaining route is to enumerate `MulAut P` via the units
     of `ZMod 5`, classify the two homomorphisms `Q →* MulAut P`, prove the
     Sylow intersection/join complement conditions, and identify conjugation
     with the semidirect action.  The explicit `Fin 4` enumeration and the
     bridge from Mathlib's internal semidirect-product equivalence to the final
     concrete multiplication identities remain unresolved. -/
  sorry
