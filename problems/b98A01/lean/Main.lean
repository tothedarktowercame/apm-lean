import Mathlib

/-!
# APM b98A01

## Statement repairs

In part (b)(iv), “a subgroup of order `3`” is repaired to “a subgroup of
order `35`”. An order-`3` subgroup exists unconditionally by Cauchy's theorem
because `3 ∣ 210`; it cannot be the contingent index-six subgroup to which the
hint says to apply part (a). The order-`35` statement is the substantive
equivalence used by that core argument.

## Encoding questions

None. Part (a) uses an actual homomorphism to `Equiv.Perm (Fin n)` and states
the universal property of its kernel. Part (b) uses actual subgroup
normalizers, subgroup cardinalities, and normality.
-/

theorem apm_b98a01 :
    (∀ (G : Type*) [Group G] [Fintype G] (H : Subgroup G) (n : ℕ),
      H.index = n →
      ∃ ψ : G →* Equiv.Perm (Fin n),
        MonoidHom.ker ψ ≤ H ∧
        ∀ N : Subgroup G, N.Normal → N ≤ H → N ≤ MonoidHom.ker ψ) ∧
    (∀ (G : Type*) [Group G] [Fintype G] (B : Subgroup G),
      Fintype.card G = 210 →
      Nat.card B = 5 →
      ¬B.Normal →
      (Nat.card (Subgroup.normalizer (B : Set G)) = 10 ∨
        Nat.card (Subgroup.normalizer (B : Set G)) = 35) ∧
      ((∃ L : Subgroup G, Nat.card L = 10) →
        Nat.card (Subgroup.normalizer (B : Set G)) = 10) ∧
      (((∃ L : Subgroup G, Nat.card L = 10) ∧
          ¬∃ M : Subgroup G, Nat.card M = 35) ∨
        ((∃ M : Subgroup G, Nat.card M = 35) ∧
          ¬∃ L : Subgroup G, Nat.card L = 10)) ∧
      ((∃ M : Subgroup G, Nat.card M = 35) ↔
        ∃ N : Subgroup G, N.Normal ∧ Nat.card N = 7)) := by
  /-
  Boundary (pass-1 Codex, skipped): Mathlib packages the conceptual engine of
  part (a): `Subgroup.normalCore_eq_ker` identifies the kernel of the coset
  action, and `Subgroup.normal_le_normalCore` expresses its universal property
  for normal subgroups. A proof still has to choose an equivalence from
  the quotient `G ⧸ H` to `Fin n` from the index equality and conjugate the
  permutation representation along it.

  For part (b), source search found general Sylow tools including
  `Sylow.card_eq_index_normalizer` and `Sylow.card_sylow_modEq_one`, but no
  order-210 specialization or proved sibling. Closing the frozen conjunction
  requires showing the arbitrary order-5 subgroup `B` is Sylow, enumerating the
  divisors of 42 congruent to 1 modulo 5, converting the resulting normalizer
  indices to the exact cardinal alternatives 10 and 35, and transporting those
  sizes across conjugate Sylow subgroups. The final equivalence additionally
  needs the index-six core action, divisibility of its quotient order into
  `6!`, elimination of kernel sizes 1, 5, and 35, and construction of the
  converse order-35 subgroup from a normal order-7 subgroup. These bridges are
  not available as packaged lemmas. The repaired statement appears sound.
  -/
  sorry
