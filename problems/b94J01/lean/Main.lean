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

lemma apm_b94J01_card_eq_prod_of_invariantFactors
    (G : Type*) [Group G] (d : List ℕ)
    (hd : apm_b94J01_invariantFactors G d) : Nat.card G = d.prod := by
  obtain ⟨e⟩ := hd.2.2
  calc
    Nat.card G = Nat.card (∀ i : Fin d.length, Multiplicative (ZMod (d.get i))) :=
      Nat.card_congr e.toEquiv
    _ = ∏ i : Fin d.length, Nat.card (Multiplicative (ZMod (d.get i))) := Nat.card_pi
    _ = ∏ i : Fin d.length, d.get i := by
      apply Finset.prod_congr rfl
      intro i hi
      calc
        Nat.card (Multiplicative (ZMod (d.get i))) = Nat.card (ZMod (d.get i)) :=
          Nat.card_congr Multiplicative.toAdd
        _ = d.get i := Nat.card_zmod _
    _ = d.prod := by rw [← List.prod_ofFn, List.ofFn_get]

/-- The normalized invariant-factor list of a group of cardinality one can
only be the empty list. -/
lemma apm_b94J01_invariantFactors_eq_nil_of_card_eq_one
    (G : Type*) [Group G] (d : List ℕ)
    (hd : apm_b94J01_invariantFactors G d) (hcard : Nat.card G = 1) :
    d = [] := by
  have hprod : d.prod = 1 := by
    rw [← apm_b94J01_card_eq_prod_of_invariantFactors G d hd, hcard]
  cases d with
  | nil => rfl
  | cons a t =>
      have ha2 : 2 ≤ a := hd.1 a (by simp)
      have hadvd : a ∣ (a :: t).prod := by
        simp only [List.prod_cons]
        exact dvd_mul_right a t.prod
      have ha1 : a = 1 := Nat.eq_one_of_dvd_one (hprod ▸ hadvd)
      omega

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
    /- CLOSER HOP 2 boundary: `CommGroup.equiv_prod_multiplicative_zmod_of_finite`
       now supplies an explicit finite index type `ι`, moduli `n : ι → ℕ`
       satisfying `1 < n i`, and the multiplicative product equivalence
       `hdecomp`.  I also inspected `AddCommGroup.equiv_directSum_zmod_of_finite`
       and the PID/Smith-normal-form APIs.

       The remaining gap is not existence of a cyclic-factor decomposition:
       it is converting these unordered factors into the frozen invariant-factor
       encoding, a *unique list* `d` with `List.Pairwise (· ∣ ·)`, and proving
       uniqueness of that normalized list.  Mathlib's finite-abelian-group API
       provides primary factors but no theorem for this normalization or its
       uniqueness.  New progress: `apm_b94J01_card_eq_prod_of_invariantFactors`
       proves every admissible list has product `Nat.card G`, using `Nat.card_pi`
       and `Nat.card_zmod`. This supplies the total-order invariant required by
       uniqueness, but product plus the divisibility chain is not sufficient:
       uniqueness still needs the p-primary ranks (equivalently, the cardinalities
       of p-power torsion subgroups) and a theorem recovering each list entry from
       those ranks. Searches for `invariantFactors`, `elementaryDivisors`, and the
       Smith-normal-form quotient APIs found no bridge from an arbitrary finite
       commutative group to that normalized data.

       New closer-hop progress:
       `apm_b94J01_invariantFactors_eq_nil_of_card_eq_one` proves the normalized
       edge case: any admissible list for a group of cardinality one is empty.
       It combines the compiled product formula with the frozen lower bound
       `2 ≤ n` on every factor. Thus existence and uniqueness for the trivial
       group are reduced to constructing the evident empty-product equivalence;
       the nontrivial-group normalization and p-primary uniqueness remain. -/
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
