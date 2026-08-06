import Mathlib

/-!
# APM b94J01

## Statement repairs

None.

## Encoding questions

The Fundamental Theorem is stated in its unique invariant-factor form. A list
`d` represents the ordered cyclic factors, including the empty list for the
trivial group. `Multiplicative` converts the additive groups `ZMod n` to the
multiplicative convention used by `IsCyclic`.
-/

/-- `d` is the invariant-factor decomposition of the finite abelian group `G`. -/
def apm_b94J01_invariantFactors (G : Type*) [Group G] (d : List ℕ) : Prop :=
  (∀ n ∈ d, 2 ≤ n) ∧
    d.Pairwise (· ∣ ·) ∧
    Nonempty
      (G ≃* (∀ i : Fin d.length, Multiplicative (ZMod (d.get i))))

theorem apm_b94j01 :
    (∀ (G : Type*) [CommGroup G] [Fintype G],
      ∃! d : List ℕ, apm_b94J01_invariantFactors G d) ∧
    (∀ m n : ℕ, 0 < m → 0 < n →
      (IsCyclic (Multiplicative (ZMod m) × Multiplicative (ZMod n)) ↔
        Nat.Coprime m n)) ∧
    (∀ (K : Type*) [Field K] (G : Subgroup Kˣ) [Finite G], IsCyclic G) := by
  sorry
