import Mathlib

noncomputable section

/-!
# APM b96A03

## Statement repairs

None.

## Encoding notes

The polynomial ring is the genuine `MvPolynomial (Fin n) F`. The orbit product
uses `Finset.image`, so repeated orbit elements are removed exactly as required.
The invariant ring is defined as the actual fixed-element subring.
-/

def apmFPure (F G : Type*) [Field F] [Group G] : Prop :=
  ∀ (H : Subgroup G) (chi : H →* Fˣ) (h : H), chi h = 1

noncomputable def apmOrbitProduct {F n : Type*} [Field F] [Fintype n]
    (G : Subgroup (MvPolynomial n F ≃ₐ[F] MvPolynomial n F)) [Fintype G]
    (π : MvPolynomial n F) : MvPolynomial n F := by
  classical
  exact ∏ δ ∈ Finset.univ.image (fun g : G ↦ g.1 π), δ

def apmFixedRing {F n : Type*} [Field F] [Fintype n]
    (G : Subgroup (MvPolynomial n F ≃ₐ[F] MvPolynomial n F)) :
    Subring (MvPolynomial n F) where
  carrier := {a | ∀ g : G, g.1 a = a}
  zero_mem' := fun g ↦ map_zero g.1
  one_mem' := fun g ↦ map_one g.1
  add_mem' ha hb g := by rw [map_add, ha g, hb g]
  neg_mem' ha g := by rw [map_neg, ha g]
  mul_mem' ha hb g := by rw [map_mul, ha g, hb g]

theorem apm_b96a03 :
    (∀ (G : Type*) [Group G] [Fintype G], Odd (Fintype.card G) →
      apmFPure ℚ G) ∧
    (∀ (F : Type*) [Field F] (n : Type*) [Fintype n]
      (G : Subgroup (MvPolynomial n F ≃ₐ[F] MvPolynomial n F)) [Fintype G],
      (∀ (g : G) (α : MvPolynomial n F), Prime (g.1 α) ↔ Prime α) ∧
      (apmFPure F G →
        (∀ (g : G) (π : MvPolynomial n F), Prime π →
          g.1 π = π ∨ (Prime (g.1 π) ∧ ¬Associated (g.1 π) π)) ∧
        (∀ π : MvPolynomial n F, Prime π →
          (∀ g : G, g.1 (apmOrbitProduct G π) = apmOrbitProduct G π) ∧
          (∀ α : MvPolynomial n F, (∀ g : G, g.1 α = α) →
            π ∣ α → apmOrbitProduct G π ∣ α) ∧
          ∃ hfix : ∀ g : G, g.1 (apmOrbitProduct G π) = apmOrbitProduct G π,
            Prime (⟨apmOrbitProduct G π, hfix⟩ : apmFixedRing G)))) := by
  constructor
  · intro G _ _ hodd H chi h
    have hh : h ^ Fintype.card G = 1 := by
      ext
      exact pow_card_eq_one (x := (h : G))
    have hchi := congrArg chi hh
    apply Units.ext
    apply hodd.pow_injective
    simpa using congrArg Units.val hchi
  · intro F _ n _ G _
    constructor
    · intro g α
      rw [← irreducible_iff_prime, ← irreducible_iff_prime]
      exact MulEquiv.irreducible_iff g.1
    · -- Boundary: searched `MulEquiv.irreducible_iff`, the
      -- `MvPolynomial` unit classification, `Finset.prod_bij`, and prime-product
      -- divisibility APIs.  The remaining implication requires constructing
      -- the stabilizer-of-associate subgroup and its coefficient character
      -- into `Fˣ`, then a substantial orbit-product invariance/divisibility
      -- argument and transfer of primality to the custom fixed subring.
      sorry
