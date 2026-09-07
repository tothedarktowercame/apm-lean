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
    ∃ Ψ : Fin 4 → MulAut P, Function.Injective Ψ ∧
      ∀ (n : Fin 4) (i : ℕ), Ψ n (x ^ i) = x ^ (((n : ℕ) + 1) * i) := by
  let e : Multiplicative (ZMod 5) ≃* P :=
    zmodMulEquivOfGenerator (g := x) (n := 5) (fun z => by simp [hx]) hcard
  let u (n : Fin 4) : (ZMod 5)ˣ :=
    ZMod.unitOfCoprime ((n : ℕ) + 1) (by fin_cases n <;> decide)
  let a (n : Fin 4) : MulAut (Multiplicative (ZMod 5)) :=
    (MulAutMultiplicative (ZMod 5)).symm ((ZMod.AddAutEquivUnits 5).symm (u n))
  let Ψ (n : Fin 4) : MulAut P := MulAut.congr e (a n)
  have hΨinj : Function.Injective Ψ := by
    intro m n hmn
    have h := DFunLike.congr_fun hmn (e (Multiplicative.ofAdd 1))
    have h' : e (a m (Multiplicative.ofAdd 1)) =
        e (a n (Multiplicative.ofAdd 1)) := by simpa [Ψ] using h
    apply_fun e.symm at h'
    simp [a, u] at h'
    fin_cases m <;> fin_cases n <;>
      norm_num [Units.smul_def, ZMod.unitOfCoprime] at h' ⊢ <;>
      revert h' <;> decide
  refine ⟨Ψ, hΨinj, ?_⟩
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

/-- Homomorphisms out of a cyclic group are determined by the chosen
generator. -/
lemma apm_b94a01_hom_ext_generator
    (Q A : Type*) [Group Q] [Group A] (y : Q)
    (hy : Subgroup.zpowers y = ⊤) (f g : Q →* A)
    (hfg : f y = g y) : f = g := by
  ext q
  have hq : q ∈ Subgroup.zpowers y := by rw [hy]; exact Subgroup.mem_top q
  rw [Subgroup.mem_zpowers_iff] at hq
  obtain ⟨k, rfl⟩ := hq
  simp [hfg]

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
    have hv : (Nat.factorization 10) 5 = 1 := by
      rw [show 10 = 2 * 5 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num)]
      norm_num [Nat.factorization]
    rw [hv]
    norm_num
  have hQcard : Nat.card (Q : Subgroup G) = 2 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, hcard]
    have hv : (Nat.factorization 10) 2 = 1 := by
      rw [show 10 = 2 * 5 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num)]
      norm_num [Nat.factorization]
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
    decide
  have hcomplement :=
    apm_b94a01_complement G (P : Subgroup G) (Q : Subgroup G)
      hPcard hQcard hcard
  obtain ⟨Ψ, hΨinj, hΨpow⟩ := apm_b94a01_power_mulAut P x hx hPcard
  have hΨsurj : ∀ φ : MulAut P, ∃ n : Fin 4, φ = Ψ n := by
    letI : Fintype (MulAut P) := Fintype.ofFinite (MulAut P)
    exact fun φ => by
      obtain ⟨n, rfl⟩ := (hΨinj.bijective_of_nat_card_le
        (by simpa using le_of_eq hAutCard)).surjective φ
      exact ⟨n, rfl⟩
  have hxord : orderOf x = 5 := orderOf_eq_card_of_zpowers_eq_top hx |>.trans hPcard
  have hΨzero : Ψ 0 = 1 := by
    apply MulEquiv.toMonoidHom_injective
    apply apm_b94a01_hom_ext_generator P P x hx
    simpa using hΨpow 0 1
  have hΨthree_sq : (Ψ 3) ^ 2 = 1 := by
    apply MulEquiv.toMonoidHom_injective
    apply apm_b94a01_hom_ext_generator P P x hx
    change Ψ 3 (Ψ 3 x) = x
    rw [show x = x ^ 1 by simp, hΨpow, hΨpow]
    rw [show (((3 : Fin 4) : ℕ) + 1) * 1 = 4 by norm_num]
    rw [show (((3 : Fin 4) : ℕ) + 1) * 4 = 16 by norm_num]
    have : x ^ 5 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by simp [hxord])
    rw [show 16 = 15 + 1 by norm_num, pow_add,
      show x ^ 15 = (x ^ 5) ^ 3 by rw [← pow_mul]]
    simp [this]
  have hyord : orderOf y = 2 := orderOf_eq_card_of_zpowers_eq_top hy |>.trans hQcard
  have hygen : ∀ q : Q, q ∈ Subgroup.zpowers y := fun q => by
    rw [hy]
    exact Subgroup.mem_top q
  let φtriv : Q →* MulAut P :=
    monoidHomOfForallMemZpowers hygen (g' := Ψ 0)
      (by rw [hΨzero]; simp [hyord])
  let φinv : Q →* MulAut P :=
    monoidHomOfForallMemZpowers hygen (g' := Ψ 3)
      (orderOf_dvd_iff_pow_eq_one.mpr hΨthree_sq |>.trans (by simp [hyord]))
  have hφtriv : φtriv y = Ψ 0 := monoidHomOfForallMemZpowers_apply_gen _ _
  have hφinv : φinv y = Ψ 3 := monoidHomOfForallMemZpowers_apply_gen _ _
  have hφne : φtriv ≠ φinv := by
    intro h
    have heq : Ψ 0 = Ψ 3 := hφtriv.symm.trans ((DFunLike.congr_fun h y).trans hφinv)
    have := hΨinj heq
    have := congrArg Fin.val this
    norm_num at this
  refine ⟨Ψ, hΨinj, hΨsurj, hΨpow, ?_⟩
  have hclass : ∀ φ : Q →* MulAut P, φ = φtriv ∨ φ = φinv := by
    intro φ
    obtain ⟨n, hn⟩ := hΨsurj (φ y)
    have hy2 : y ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by simp [hyord])
    have hs : (φ y) ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
    have ha : Ψ n (Ψ n x) = x := by
      rw [hn] at hs
      exact DFunLike.congr_fun hs x
    rw [show x = x ^ 1 by simp, hΨpow, hΨpow] at ha
    fin_cases n
    · left
      apply apm_b94a01_hom_ext_generator Q (MulAut P) y hy
      simpa [hφtriv] using hn
    · rw [pow_eq_pow_iff_modEq, hxord] at ha
      norm_num [Nat.ModEq] at ha
    · rw [pow_eq_pow_iff_modEq, hxord] at ha
      norm_num [Nat.ModEq] at ha
    · right
      apply apm_b94a01_hom_ext_generator Q (MulAut P) y hy
      simpa [hφinv] using hn
  refine ⟨⟨φtriv, φinv, hφtriv, hφinv, hφne, hclass⟩, ?_⟩
  refine ⟨⟨hPnormal, hcomplement.1, hcomplement.2.1, hcomplement.2.2⟩, ?_⟩
  intro hnoncomm
  let φconj : Q →* MulAut P :=
    (P : Subgroup G).normalizerMonoidHom.comp
      (Subgroup.inclusion ((P : Subgroup G).normalizer_eq_top ▸ le_top))
  have hφconj : φconj = φtriv ∨ φconj = φinv := hclass φconj
  have hnottriv : φconj ≠ φtriv := by
    intro ht
    have hxy : (y : G) * (x : G) = (x : G) * (y : G) := by
      have hv : φconj y = φtriv y := congrArg (fun f : Q →* MulAut P => f y) ht
      have hvx := DFunLike.congr_fun hv x
      rw [hφtriv, hΨzero] at hvx
      dsimp [φconj, Subgroup.normalizerMonoidHom, MulDistribMulAction.toMulAut] at hvx
      have hvxG := congrArg Subtype.val hvx
      have hc : (y : G) * (x : G) * (y : G)⁻¹ = (x : G) := by
        exact hvxG
      simpa [mul_assoc] using congrArg (fun z : G => z * (y : G)) hc
    have hxG : Subgroup.zpowers (x : G) = (P : Subgroup G) := by
      calc
        _ = Subgroup.map (P : Subgroup G).subtype (Subgroup.zpowers x) :=
          (MonoidHom.map_zpowers (P : Subgroup G).subtype x).symm
        _ = _ := by
          rw [hx]
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hyG : Subgroup.zpowers (y : G) = (Q : Subgroup G) := by
      calc
        _ = Subgroup.map (Q : Subgroup G).subtype (Subgroup.zpowers y) :=
          (MonoidHom.map_zpowers (Q : Subgroup G).subtype y).symm
        _ = _ := by
          rw [hy]
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hcl : Subgroup.closure ({(x : G), (y : G)} : Set G) = ⊤ := by
      change Subgroup.closure ({(x : G)} ∪ {(y : G)}) = ⊤
      rw [Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
        ← Subgroup.zpowers_eq_closure, hxG, hyG, hcomplement.2.1]
    letI : CommGroup (Subgroup.closure ({(x : G), (y : G)} : Set G)) :=
      Subgroup.closureCommGroupOfComm (by
        intro a ha b hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · rfl
        · exact hxy.symm
        · exact hxy
        · rfl)
    obtain ⟨a, b, hab⟩ := hnoncomm
    apply hab
    have hc : (⟨a, hcl.ge (Subgroup.mem_top a)⟩ : Subgroup.closure
        ({(x : G), (y : G)} : Set G)) * ⟨b, hcl.ge (Subgroup.mem_top b)⟩ =
        ⟨b, hcl.ge (Subgroup.mem_top b)⟩ * ⟨a, hcl.ge (Subgroup.mem_top a)⟩ := mul_comm _ _
    exact congrArg Subtype.val hc
  have hci : φconj = φinv := hφconj.resolve_left hnottriv
  have hconj : (y : G) * (x : G) * (y : G)⁻¹ = ((x ^ 4 : P) : G) := by
    have hv : φconj y = φinv y := congrArg (fun f : Q →* MulAut P => f y) hci
    rw [hφinv] at hv
    have hvx := DFunLike.congr_fun hv x
    rw [show x = x ^ 1 by simp, hΨpow] at hvx
    dsimp [φconj, Subgroup.normalizerMonoidHom, MulDistribMulAction.toMulAut] at hvx
    simpa [MulDistribMulAction.toMulEquiv] using congrArg Subtype.val hvx
  have hfirst : (y : G) * (x : G) = ((x ^ 4 : P) : G) * (y : G) := by
    simpa [mul_assoc] using congrArg (fun z : G => z * (y : G)) hconj
  refine ⟨hfirst, ?_⟩
  have hy2 : y ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by simp [hyord])
  have hx5 : x ^ 5 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by simp [hxord])
  have hy2G : (y : G) ^ 2 = 1 := congrArg Subtype.val hy2
  have hx5G : (x : G) ^ 5 = 1 := congrArg Subtype.val hx5
  have hmove3 : (y : G) * (x : G) ^ 3 * (y : G)⁻¹ = (x : G) ^ 12 := by
    calc
      _ = ((y : G) * (x : G) * (y : G)⁻¹) ^ 3 := by
        simpa using ((MulAut.conj (y : G)).map_pow (x : G) 3)
      _ = (((x ^ 4 : P) : G)) ^ 3 := by rw [hconj]
      _ = (x : G) ^ 12 := by simp [← pow_mul]
  change ((x : G) ^ 2 * (y : G)) * ((x : G) ^ 3 * (y : G)) = (x : G) ^ 4
  calc
    _ = (x : G) ^ 2 * ((y : G) * (x : G) ^ 3 * (y : G)⁻¹) * (y : G) ^ 2 := by group
    _ = (x : G) ^ 14 := by rw [hmove3, hy2G]; group
    _ = (x : G) ^ 4 := by
      rw [show 14 = 10 + 4 by norm_num, pow_add,
        show (x : G) ^ 10 = ((x : G) ^ 5) ^ 2 by rw [← pow_mul]]
      simp [hx5G]
