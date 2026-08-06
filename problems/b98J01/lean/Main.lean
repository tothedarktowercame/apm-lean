import Mathlib

/-!
# APM b98J01

## Statement repairs

Part (e) is printed as `Z(N) < G`, which is both immediate from `N ≤ G` and,
contrary to the closing remark, not incompatible with `|Z(N)| = 2`. We state
the intended conclusion `K ≤ Z(N)`: every element of `K` commutes with every
element of `N`. This is the conclusion used by the remark to rule out a center
of order two.

## Encoding questions

The assertion `G/K ≅ A₄` is encoded without installing a local normal-subgroup
instance: it is a surjective homomorphism `G → A₄` whose kernel is exactly `K`.
-/

theorem apm_b98j01 :
    ∀ (G : Type*) [Group G] [Fintype G],
      Fintype.card G = 36 →
      ((¬∃ H : Subgroup G, H.Normal ∧ Nat.card H = 9) →
        ∃ (K : Subgroup G) (φ : G →* alternatingGroup (Fin 4)),
          K.Normal ∧ Nat.card K = 3 ∧ Function.Surjective φ ∧ φ.ker = K) ∧
      (∃ V : Subgroup (alternatingGroup (Fin 4)), V.Normal ∧ Nat.card V = 4) ∧
      (∀ (K : Subgroup G) (φ : G →* alternatingGroup (Fin 4)),
        K.Normal → Nat.card K = 3 → Function.Surjective φ → φ.ker = K →
        ∃ N : Subgroup G,
          N.Normal ∧ Nat.card N = 12 ∧ K ≤ N ∧
          ((∀ x y : N, x * y = y * x) ∨ Nat.card (Subgroup.center N) = 2) ∧
          (∀ k ∈ K, ∀ n ∈ N, k * n = n * k)) := by
  sorry
