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
  refine ⟨?_, ?_, ?_⟩
  · /- PASS-1 boundary: searched the finite-abelian-group structure APIs and
       the classification of finite modules over a PID.  Mathlib provides
       cyclic and primary decomposition machinery, but I could not find a
       theorem whose canonical output is the frozen encoding: a *unique list*
       `d`, with entries at least two, `List.Pairwise (· ∣ ·)`, and a `Fin`
       indexed product of `Multiplicative (ZMod (d.get i))`.  Transporting the
       available decomposition into this normalized list and proving list
       uniqueness remains the pass-1 blocker. -/
    sorry
  · intro m n hm hn
    have hmcard : Nat.card (Multiplicative (ZMod m)) = m := by
      calc
        Nat.card (Multiplicative (ZMod m)) = Nat.card (ZMod m) :=
          Nat.card_congr Multiplicative.toAdd
        _ = m := Nat.card_zmod m
    have hncard : Nat.card (Multiplicative (ZMod n)) = n := by
      calc
        Nat.card (Multiplicative (ZMod n)) = Nat.card (ZMod n) :=
          Nat.card_congr Multiplicative.toAdd
        _ = n := Nat.card_zmod n
    rw [Group.isCyclic_prod_iff]
    constructor
    · rintro ⟨hmcyc, hncyc, hcop⟩
      simpa [hmcard, hncard] using hcop
    · intro hcop
      refine ⟨inferInstance, inferInstance, ?_⟩
      simpa [hmcard, hncard] using hcop
  · intro K _ G _
    infer_instance
