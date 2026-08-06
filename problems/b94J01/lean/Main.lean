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
  · intro G _ _
    obtain ⟨ι, instι, n, hn, hdecomp⟩ :=
      CommGroup.equiv_prod_multiplicative_zmod_of_finite G
    /- PASS-1 boundary: `CommGroup.equiv_prod_multiplicative_zmod_of_finite`
       now supplies an explicit finite index type `ι`, moduli `n : ι → ℕ`
       satisfying `1 < n i`, and the multiplicative product equivalence
       `hdecomp`.  I also inspected `AddCommGroup.equiv_directSum_zmod_of_finite`
       and the PID/Smith-normal-form APIs.

       The remaining gap is not existence of a cyclic-factor decomposition:
       it is converting these unordered factors into the frozen invariant-factor
       encoding, a *unique list* `d` with `List.Pairwise (· ∣ ·)`, and proving
       uniqueness of that normalized list.  Mathlib's finite-abelian-group API
       provides primary factors but no theorem for this normalization or its
       uniqueness. -/
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
