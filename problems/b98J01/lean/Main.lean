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

/-- The structural part of pulling the Klein four subgroup back along a
surjection: the preimage is normal and contains the kernel. -/
lemma apm_b98J01_kleinFour_comap_normal_and_ker_le
    {G : Type*} [Group G] (φ : G →* alternatingGroup (Fin 4)) :
    ((alternatingGroup.kleinFour (Fin 4)).comap φ).Normal ∧
      φ.ker ≤ (alternatingGroup.kleinFour (Fin 4)).comap φ := by
  have h4 : Nat.card (Fin 4) = 4 := by simp
  exact ⟨(alternatingGroup.normal_kleinFour h4).comap φ,
    Subgroup.ker_le_comap φ (alternatingGroup.kleinFour (Fin 4))⟩

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
  intro G _ _ hGcard
  have h_klein_four :
      ∃ V : Subgroup (alternatingGroup (Fin 4)), V.Normal ∧ Nat.card V = 4 := by
    have h4 : Nat.card (Fin 4) = 4 := by simp
    exact ⟨alternatingGroup.kleinFour (Fin 4),
      alternatingGroup.normal_kleinFour h4,
      alternatingGroup.kleinFour_card_of_card_eq_four h4⟩
  /-
  Boundary (closer hop 1 Codex, partial): `h_klein_four` above closes the second
  conjunct using the packaged Klein four subgroup; `hGcard` remains available
  for the order-36 argument. Inspection of cited sibling `b93J01` found only
  unrelated elementary examples, not the `A₄` subgroup facts used here.

  The remaining first conjunct needs a conjugation action on the four Sylow
  3-subgroups, conversion of its permutation type to `Fin 4`, kernel-cardinality
  arithmetic, and identification of its order-12 image with `alternatingGroup
  (Fin 4)`. For the last conjunct one must pull back `kleinFour` along an
  arbitrary surjective `φ`, prove the preimage has cardinality 12, classify its
  semidirect action on the order-3 kernel to obtain the center dichotomy, and
  exclude the noncentral action by showing `A₄` has no subgroup of order 6.
  Local Mathlib searches found the general Sylow/action APIs and the packaged
  Klein four facts, but no order-36 or no-order-6 assembly.

  New progress: `apm_b98J01_kleinFour_comap_normal_and_ker_le` packages the
  canonical candidate for the last conjunct,
  `N = (alternatingGroup.kleinFour (Fin 4)).comap φ`, and proves both its
  normality and `φ.ker ≤ N` using `Subgroup.Normal.comap` and
  `Subgroup.ker_le_comap`. Thus, after rewriting `φ.ker = K`, the containment
  `K ≤ N` is immediate. The remaining pullback work is the cardinality formula
  `|N| = |ker φ| * |kleinFour| = 12`; searches of `Coset.Card` found only
  `card_comap_dvd_of_injective`, not the surjective preimage-card equality.
  The center dichotomy and the no-order-six argument also remain open. The
  repaired statement appears mathematically sound.

  Closer hop 2 found the missing cardinality ingredients despite there being
  no named comap-card theorem. `MonoidHom.fiberEquivKerOfSurjective` identifies
  every fiber of `φ` with `φ.ker`, while `Equiv.sigmaFiberEquiv` assembles the
  fibers over the Klein-four subtype; equivalently, the restricted homomorphism
  `φ.subgroupMap N` can use `Subgroup.card_mul_index` and
  `Subgroup.index_ker`. I tested the explicit equivalence
  `N ≃ kleinFour × φ.ker`; its forward and inverse maps elaborate, but the
  dependent-subtype `left_inv`/`right_inv` equalities did not close in this
  hop. Thus the order-12 calculation is now an explicit finite-fiber assembly
  rather than a missing mathematical lemma. The center dichotomy and
  no-order-six arguments remain untouched.
  -/
  sorry
