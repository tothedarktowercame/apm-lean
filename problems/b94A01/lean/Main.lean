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

/-- Subgroups of orders five and two in a group of order ten form an internal
semidirect product when the subgroup of order five is normal. -/
lemma apm_b94a01_complement
    (G : Type*) [Group G] [Fintype G]
    (P Q : Subgroup G) [P.Normal]
    (hP : Nat.card P = 5) (hQ : Nat.card Q = 2)
    (hG : Fintype.card G = 10) :
    Disjoint P Q ∧ P ⊔ Q = ⊤ ∧
      ∃ φ : Q →* MulAut P, Nonempty (G ≃* (P ⋊[φ] Q)) := by
  have hmul : Nat.card P * Nat.card Q = Nat.card G := by
    rw [hP, hQ, Nat.card_eq_fintype_card, hG]
  have hc : P.IsComplement' Q :=
    Subgroup.isComplement'_of_coprime hmul
      (by simpa [hP, hQ] using (show Nat.Coprime 5 2 by decide))
  let φ : Q →* MulAut P :=
    P.normalizerMonoidHom.comp
      (Subgroup.inclusion (P.normalizer_eq_top ▸ le_top))
  refine ⟨hc.disjoint, hc.sup_eq_top, φ, ?_⟩
  exact ⟨(SemidirectProduct.mulEquivSubgroup hc).symm⟩

/-- Cardinality four gives an actual exhaustive injective enumeration of the
automorphism group. -/
lemma apm_b94a01_enumerate_mulAut
    (P : Type*) [Group P] [Finite P]
    (hcard : Nat.card (MulAut P) = 4) :
    ∃ Ψ : Fin 4 → MulAut P,
      Function.Injective Ψ ∧ ∀ φ : MulAut P, ∃ n : Fin 4, φ = Ψ n := by
  letI : Fintype (MulAut P) := Fintype.ofFinite (MulAut P)
  have hcard' : Fintype.card (MulAut P) = 4 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  let e : MulAut P ≃ Fin 4 := Fintype.equivFinOfCardEq hcard'
  refine ⟨e.symm, e.symm.injective, ?_⟩
  intro φ
  exact ⟨e φ, by simp [e]⟩

/-- The four canonical units modulo five give automorphisms with the exact
power action required by the chosen generator. -/
lemma apm_b94a01_power_mulAut
    (P : Type*) [Group P] [Finite P]
    (x : P) (hx : Subgroup.zpowers x = ⊤)
    (hcard : Nat.card P = 5) :
    ∃ Ψ : Fin 4 → MulAut P,
      ∀ (n : Fin 4) (i : ℕ), Ψ n (x ^ i) = x ^ (((n : ℕ) + 1) * i) := by
  let e : Multiplicative (ZMod 5) ≃* P :=
    zmodMulEquivOfGenerator (g := x) (n := 5) (fun z => by simp [hx]) hcard
  let u (n : Fin 4) : (ZMod 5)ˣ :=
    ZMod.unitOfCoprime ((n : ℕ) + 1) (by fin_cases n <;> decide)
  let a (n : Fin 4) : MulAut (Multiplicative (ZMod 5)) :=
    (MulAutMultiplicative (ZMod 5)).symm ((ZMod.AddAutEquivUnits 5).symm (u n))
  let Ψ (n : Fin 4) : MulAut P := MulAut.congr e (a n)
  refine ⟨Ψ, ?_⟩
  intro n i
  change e (a n (e.symm (x ^ i))) = _
  have he : e.symm (x ^ i) = Multiplicative.ofAdd (i : ZMod 5) := by
    rw [← zpow_natCast]
    exact zmodMulEquivOfGenerator_symm_apply_zpow _ _ _
  rw [he]
  simp [a, u, Units.smul_def]
  convert
    (zmodMulEquivOfGenerator_apply_ofAdd_intCast
      (g := x) (n := 5) (fun z => by simp [hx]) hcard
      (i := (((n : ℕ) + 1) * i : ℤ))) using 1 <;>
    try simp [e]
  rw [← zpow_natCast]
  congr 1

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
  letI : (P : Subgroup G).Normal := hPnormal
  haveI : IsCyclic P := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, hx⟩
  have hAutCard : Nat.card (MulAut P) = 4 := by
    rw [IsCyclic.card_mulAut, hPcard]
    native_decide
  have hcomplement :=
    apm_b94a01_complement G (P : Subgroup G) (Q : Subgroup G)
      hPcard hQcard hcard
  obtain ⟨Ψ, hΨinj, hΨsurj⟩ := apm_b94a01_enumerate_mulAut P hAutCard
  refine ⟨Ψ, hΨinj, hΨsurj, ?_⟩
  /- PASS-1 boundary: the Sylow sizes and normality of `P` are now proved
     locally (`hPcard`, `hQcard`, `hPnormal`) using the route validated in
     sibling `b93A01`.  I searched the Sylow and cyclic-group APIs, including
     `Sylow.card_eq_multiplicity`, `card_sylow_modEq_one`,
     `Sylow.normal_of_subsingleton`, `IsCyclic.mulAutMulEquiv`, and
     `IsCyclic.card_mulAut`, together with the semidirect-product recognition
     results.

     Closer hop 1 proves the complement and semidirect-product portion in
     `apm_b94a01_complement`.  It uses
     `Subgroup.isComplement'_of_coprime` to obtain disjointness and generation,
     then instantiates `SemidirectProduct.mulEquivSubgroup` with the normalizer
     conjugation action.  The main context also now compiles `IsCyclic P` from
     `hx` and computes `Nat.card (MulAut P) = 4` via
     `IsCyclic.card_mulAut`.

     The remaining route is to turn that cardinality into the specified
     power-action enumeration `Ψ`, classify the two homomorphisms
     `Q →* MulAut P`, and identify the nontrivial conjugation action with
     inversion to prove the final concrete multiplication identities.  No
     closed artifact or Mathlib theorem found by the searches packages those
     generator-level identifications.

     Closer hop 2 closes the first two frozen obligations on `Ψ` in
     `apm_b94a01_enumerate_mulAut`: `Fintype.equivFinOfCardEq` turns the
     already-proved automorphism cardinality four into an explicit injective
     exhaustive enumeration.  The remaining issue is not enumeration but
     choosing/reindexing it so index `n` acts by the specific exponent `n+1`.
     A targeted inspection of `IsCyclic.mulAutMulEquiv` confirms an
     equivalence with units of `ZMod 5`, but transporting its evaluation
     theorem back to the arbitrary generator `x` is not packaged.

     Closer hop 3 constructs that generator-adapted family directly in
     `apm_b94a01_power_mulAut`, conjugating multiplication by the four units
     of `ZMod 5` through `zmodMulEquivOfGenerator`; its exact power-action
     formula compiles.  The remaining assembly is to prove this canonical
     family injective/exhaustive, classify the two maps from `Q`, and derive
     the final conjugation identities. -/
  sorry
