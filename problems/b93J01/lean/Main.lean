import Mathlib

/-!
# APM b93J01 — false group-theory assertions and their corrections

## Statement repairs

In item (c), the conclusion's `subgroup of order n` is corrected to
`subgroup of order m`; as printed, the whole group makes the assertion
trivially true and contradicts the instruction to show it false.

For item (e), the correction adds the standard condition `p ∤ q - 1`.

## Encoding questions

None. An abelian group being a direct sum of cyclic groups is encoded by a
family of cyclic subgroups which is independent and whose supremum is the
whole group.
-/

open scoped BigOperators

noncomputable section

def apm_b93J01_IsDirectSumOfCyclic (G : Type*) [AddCommGroup G] : Prop :=
  ∃ (ι : Type) (A : ι → AddSubgroup G),
    (∀ i, IsAddCyclic (A i)) ∧ iSupIndep A ∧ iSup A = ⊤

lemma apm_b93J01_card_A4 :
    Fintype.card (alternatingGroup (Fin 4)) = 12 := by
  rw [card_alternatingGroup]
  norm_num

def apm_b93J01_A4_kleinFour : Subgroup (alternatingGroup (Fin 4)) where
  carrier := {g | g ^ 2 = 1}
  one_mem' := by simp
  mul_mem' := by decide
  inv_mem' := by decide

lemma apm_b93J01_A4_kleinFour_normal :
    apm_b93J01_A4_kleinFour.Normal := by
  constructor
  intro n hn g
  change (g * n * g⁻¹) ^ 2 = 1
  change n ^ 2 = 1 at hn
  rw [show (g * n * g⁻¹) ^ 2 = g * n ^ 2 * g⁻¹ by
    simp only [pow_two]
    group]
  simp [hn]

lemma apm_b93J01_A4_kleinFour_ne_bot :
    apm_b93J01_A4_kleinFour ≠ ⊥ := by
  let x : alternatingGroup (Fin 4) :=
    ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3, by simp [alternatingGroup]⟩
  intro h
  have hx : x ∈ apm_b93J01_A4_kleinFour := by
    change x ^ 2 = 1
    decide
  have hxbot : x ∈ (⊥ : Subgroup (alternatingGroup (Fin 4))) := h ▸ hx
  have hxone : x = 1 := by simpa using hxbot
  have : x ≠ 1 := by decide
  exact this hxone

lemma apm_b93J01_A4_kleinFour_ne_top :
    apm_b93J01_A4_kleinFour ≠ ⊤ := by
  let x : alternatingGroup (Fin 4) :=
    ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2, by simp [alternatingGroup]⟩
  intro h
  have hxtop : x ∈ (⊤ : Subgroup (alternatingGroup (Fin 4))) := by simp
  have hx : x ∈ apm_b93J01_A4_kleinFour := h ▸ hxtop
  change x ^ 2 = 1 at hx
  have : x ^ 2 ≠ 1 := by decide
  exact this hx

lemma apm_b93J01_A4_not_simple :
    ¬IsSimpleGroup (alternatingGroup (Fin 4)) := by
  intro h
  rcases h.eq_bot_or_eq_top_of_normal apm_b93J01_A4_kleinFour
      apm_b93J01_A4_kleinFour_normal with hbot | htop
  · exact apm_b93J01_A4_kleinFour_ne_bot hbot
  · exact apm_b93J01_A4_kleinFour_ne_top htop

/-- An order-six subgroup of `A₄` would have index two and hence be normal.
Its quotient would be cyclic, forcing the commutator subgroup--the Klein four
subgroup--inside it, contradicting Lagrange. -/
lemma apm_b93J01_A4_no_subgroup_card_six :
    ¬∃ H : Subgroup (alternatingGroup (Fin 4)), Nat.card H = 6 := by
  rintro ⟨H, hH⟩
  have hindex : H.index = 2 := by
    have h := H.card_mul_index
    rw [hH, Nat.card_eq_fintype_card, apm_b93J01_card_A4] at h
    omega
  letI : H.Normal := H.normal_of_index_eq_two hindex
  have hquot : Nat.card (alternatingGroup (Fin 4) ⧸ H) = 2 := by
    rw [← H.index_eq_card, hindex]
  have hcomm : commutator (alternatingGroup (Fin 4)) ≤ H := by
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    exact (isCyclic_of_prime_card hquot).commutative
  have hklein : alternatingGroup.kleinFour (Fin 4) ≤ H := by
    rw [alternatingGroup.kleinFour_eq_commutator (by norm_num)]
    exact hcomm
  have hdvd := Subgroup.card_dvd_of_le hklein
  rw [alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num), hH] at hdvd
  omega

lemma apm_b93J01_lagrange
    (G : Type*) [Group G] [Fintype G] (H : Subgroup G) :
    Nat.card H ∣ Fintype.card G := by
  simpa only [Nat.card_eq_fintype_card] using H.card_subgroup_dvd_card

lemma apm_b93J01_finite_addCommGroup_directSum
    (G : Type*) [AddCommGroup G] [Fintype G] :
    apm_b93J01_IsDirectSumOfCyclic G := by
  classical
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' G
  let f : (i : ι) → ZMod (n i) →+ G := fun i ↦
    e.symm.toAddMonoidHom.comp (DirectSum.of (fun i ↦ ZMod (n i)) i)
  let A : ι → AddSubgroup G := fun i ↦ (f i).range
  refine ⟨ι, A, ?_, ?_, ?_⟩
  · intro i
    exact isAddCyclic_of_surjective (f i).rangeRestrict
      (AddMonoidHom.rangeRestrict_surjective (f i))
  · rw [← iSupIndep_map_orderIso_iff
      (AddSubgroup.toIntSubmodule : AddSubgroup G ≃o Submodule ℤ G)]
    rw [iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero]
    intro s v hv hsum i hi
    have hev : ∑ j ∈ s, e (v j) = 0 := by
      simpa only [map_sum, map_zero] using congrArg e hsum
    have hcoord := congrArg (fun z ↦ z i) hev
    have hoff : ∀ j ∈ s, j ≠ i → (e (v j)) i = 0 := by
      intro j hj hji
      obtain ⟨y, hy⟩ := hv j hj
      change f j y = v j at hy
      rw [← hy]
      change (e (e.symm ((DirectSum.of (fun i ↦ ZMod (n i)) j) y))) i = 0
      rw [e.apply_symm_apply, DirectSum.of_apply]
      simp [hji]
    have hvi : (e (v i)) i = 0 := by
      change (∑ j ∈ s, e (v j)) i = (0 : DirectSum ι fun i ↦ ZMod (n i)) i at hcoord
      have hcoord' : (∑ j ∈ s, (e (v j)) i) = 0 := by
        calc
          _ = (∑ j ∈ s, e (v j)) i :=
            (DFinsupp.finset_sum_apply s (fun j ↦ e (v j)) i).symm
          _ = 0 := by simpa using hcoord
      rw [Finset.sum_eq_single i hoff (fun h ↦ (h hi).elim)] at hcoord'
      exact hcoord'
    obtain ⟨x, hx⟩ := hv i hi
    change f i x = v i at hx
    have hxi : x = 0 := by
      rw [← hx] at hvi
      simpa [f] using hvi
    rw [← hx, hxi, map_zero]
  · apply top_unique
    intro g hg
    let x := e g
    have hx : e.symm x ∈ iSup A := by
      induction x using DirectSum.induction_on with
      | zero => simp
      | add x y hx hy => simpa only [map_add] using AddSubgroup.add_mem _ hx hy
      | of i z =>
          apply (le_iSup A i)
          exact ⟨z, rfl⟩
    simpa [x] using hx

lemma apm_b93J01_rat_disjoint_subgroups
    (H K : AddSubgroup ℚ) (h : Disjoint H K) : H = ⊥ ∨ K = ⊥ := by
  by_contra hbot
  push_neg at hbot
  obtain ⟨x, hxH, hx0⟩ := (AddSubgroup.bot_or_exists_ne_zero H).resolve_left hbot.1
  obtain ⟨y, hyK, hy0⟩ := (AddSubgroup.bot_or_exists_ne_zero K).resolve_left hbot.2
  let z : ℚ := (x.num * y.num : ℤ)
  have hzH : z ∈ H := by
    have hm := H.zsmul_mem hxH ((x.den : ℤ) * y.num)
    convert hm using 1
    dsimp [z]
    rw [zsmul_eq_mul]
    push_cast
    symm
    calc
      (x.den : ℚ) * y.num * x = (y.num : ℚ) * (x * x.den) := by ring
      _ = (x.num : ℚ) * y.num := by rw [Rat.mul_den_eq_num]; ring
  have hzK : z ∈ K := by
    have hm := K.zsmul_mem hyK ((y.den : ℤ) * x.num)
    convert hm using 1
    dsimp [z]
    rw [zsmul_eq_mul]
    push_cast
    symm
    calc
      (y.den : ℚ) * x.num * y = (x.num : ℚ) * (y * y.den) := by ring
      _ = (x.num : ℚ) * y.num := by rw [Rat.mul_den_eq_num]
  have hz0 : z ≠ 0 := by
    dsimp [z]
    exact_mod_cast mul_ne_zero (Rat.num_ne_zero.mpr hx0) (Rat.num_ne_zero.mpr hy0)
  exact hz0 (AddSubgroup.disjoint_def.mp h hzH hzK)

lemma apm_b93J01_rat_not_directSumOfCyclic :
    ¬apm_b93J01_IsDirectSumOfCyclic ℚ := by
  rintro ⟨ι, A, hcyc, hind, hsup⟩
  have hex : ∃ i, A i ≠ ⊥ := by
    by_contra h
    push_neg at h
    have hall : iSup A = ⊥ := iSup_eq_bot.mpr h
    rw [hsup] at hall
    exact top_ne_bot hall
  obtain ⟨i, hi⟩ := hex
  have hjbot : ∀ j, j ≠ i → A j = ⊥ := by
    intro j hji
    rcases apm_b93J01_rat_disjoint_subgroups (A i) (A j)
      (hind.pairwiseDisjoint hji.symm) with hi0 | hj0
    · exact (hi hi0).elim
    · exact hj0
  have hAi : iSup A = A i := by
    apply le_antisymm
    · refine iSup_le fun j ↦ ?_
      by_cases hji : j = i
      · subst j
        exact le_rfl
      · rw [hjbot j hji]
        exact bot_le
    · exact le_iSup A i
  have hitop : A i = ⊤ := by rw [← hAi, hsup]
  have htopcyc : IsAddCyclic (⊤ : AddSubgroup ℚ) := by
    rw [← hitop]
    exact hcyc i
  letI : IsAddCyclic (⊤ : AddSubgroup ℚ) := htopcyc
  have hratcyc : IsAddCyclic ℚ :=
    isAddCyclic_of_surjective AddSubgroup.topEquiv AddSubgroup.topEquiv.surjective
  exact (LinearOrderedAddCommGroup.isAddCyclic_iff_not_denselyOrdered.mp hratcyc)
    (inferInstance : DenselyOrdered ℚ)

lemma apm_b93J01_card_S3 :
    Fintype.card (Equiv.Perm (Fin 3)) = 2 * 3 := by
  rw [Fintype.card_perm]
  norm_num

lemma apm_b93J01_abelian_of_normal_prime_factors
    (G : Type*) [Group G] [Fintype G] (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hcard : Fintype.card G = p * q)
    (P Q : Subgroup G) (hPn : P.Normal) (hQn : Q.Normal)
    (hPcard : Nat.card P = p) (hQcard : Nat.card Q = q) :
    ∀ a b : G, a * b = b * a := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  letI : IsCyclic P := isCyclic_of_prime_card hPcard
  letI : IsCyclic Q := isCyclic_of_prime_card hQcard
  have hcop : (Nat.card P).Coprime (Nat.card Q) := by
    rw [hPcard, hQcard]
    exact (Nat.coprime_primes hp hq).2 (ne_of_lt hpq)
  have hmul : Nat.card P * Nat.card Q = Nat.card G := by
    rw [hPcard, hQcard, Nat.card_eq_fintype_card, hcard]
  have hcomp : P.IsComplement' Q := Subgroup.isComplement'_of_coprime hmul hcop
  intro a b
  obtain ⟨⟨aP, aQ⟩, rfl⟩ := hcomp.2 a
  obtain ⟨⟨bP, bQ⟩, rfl⟩ := hcomp.2 b
  have haQbP : Commute (aQ : G) (bP : G) :=
    Subgroup.commute_of_normal_of_disjoint Q P hQn hPn hcomp.disjoint.symm
      aQ bP aQ.property bP.property
  have haPbP : (aP : G) * bP = bP * aP :=
    congrArg Subtype.val (IsCyclic.commutative.comm aP bP)
  have haQbQ : (aQ : G) * bQ = bQ * aQ :=
    congrArg Subtype.val (IsCyclic.commutative.comm aQ bQ)
  have hbQaP : Commute (bQ : G) (aP : G) :=
    Subgroup.commute_of_normal_of_disjoint Q P hQn hPn hcomp.disjoint.symm
      bQ aP bQ.property aP.property
  calc
    ((aP : G) * aQ) * ((bP : G) * bQ) =
        (aP : G) * ((aQ : G) * bP) * bQ := by simp only [mul_assoc]
    _ = (aP : G) * ((bP : G) * aQ) * bQ := by rw [haQbP.eq]
    _ = ((aP : G) * bP) * ((aQ : G) * bQ) := by simp only [mul_assoc]
    _ = ((bP : G) * aP) * ((bQ : G) * aQ) := by rw [haPbP, haQbQ]
    _ = (bP : G) * ((aP : G) * bQ) * aQ := by simp only [mul_assoc]
    _ = (bP : G) * ((bQ : G) * aP) * aQ := by rw [hbQaP.eq]
    _ = ((bP : G) * bQ) * ((aP : G) * aQ) := by simp only [mul_assoc]

lemma apm_b93J01_isCyclic_of_card_mul_primes
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hnot : ¬p ∣ q - 1) (G : Type*) [Group G] [Fintype G]
    (hG : Fintype.card G = p * q) : IsCyclic G := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  let P : Sylow p G := default
  let Q : Sylow q G := default
  have hPcard : Nat.card P = p := by
    rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, hG]
    rw [Nat.factorization_mul hp.ne_zero hq.ne_zero, hp.factorization, hq.factorization]
    simp [ne_of_lt hpq]
  have hQcard : Nat.card Q = q := by
    rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, hG]
    rw [Nat.factorization_mul hp.ne_zero hq.ne_zero, hp.factorization, hq.factorization]
    simp [ne_of_lt hpq]
  have hPindex : P.index = q := by
    have hm := P.toSubgroup.card_mul_index
    rw [hPcard, Nat.card_eq_fintype_card, hG] at hm
    exact Nat.eq_of_mul_eq_mul_left hp.pos hm
  have hQindex : Q.index = p := by
    have hm := Q.toSubgroup.index_mul_card
    rw [hQcard, Nat.card_eq_fintype_card, hG] at hm
    exact Nat.eq_of_mul_eq_mul_right hq.pos (by simpa [mul_comm] using hm)
  have hPsylow : Nat.card (Sylow p G) = 1 := by
    have hdvd : Nat.card (Sylow p G) ∣ q := hPindex ▸ Sylow.card_dvd_index P
    rcases (Nat.dvd_prime hq).mp hdvd with h1 | hqcard
    · exact h1
    · exfalso
      have hmod := card_sylow_modEq_one p G
      rw [hqcard] at hmod
      exact hnot ((Nat.modEq_iff_dvd' hq.one_le).mp hmod.symm)
  have hQsylow : Nat.card (Sylow q G) = 1 := by
    have hdvd : Nat.card (Sylow q G) ∣ p := hQindex ▸ Sylow.card_dvd_index Q
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpcard
    · exact h1
    · exfalso
      have hmod := card_sylow_modEq_one q G
      rw [hpcard] at hmod
      have hpone : p = 1 := by
        have hm : p % q = 1 % q := hmod
        calc
          p = p % q := (Nat.mod_eq_of_lt hpq).symm
          _ = 1 % q := hm
          _ = 1 := Nat.mod_eq_of_lt hq.one_lt
      exact hp.ne_one hpone
  letI : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hPsylow).1
  letI : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp hQsylow).1
  have hcomm := apm_b93J01_abelian_of_normal_prime_factors G p q hp hq hpq hG
      P Q (Sylow.normal_of_subsingleton P) (Sylow.normal_of_subsingleton Q) hPcard hQcard
  letI : CommGroup G := ⟨hcomm⟩
  letI : IsZGroup G := IsZGroup.of_squarefree (by
    rw [Nat.card_eq_fintype_card, hG]
    exact (Nat.squarefree_mul ((Nat.coprime_primes hp hq).2 (ne_of_lt hpq))).mpr
      ⟨hp.squarefree, hq.squarefree⟩)
  exact IsCyclic.of_exponent_eq_card (IsZGroup.exponent_eq_card G)

/-- The two adjacent transpositions in `S₃` do not commute, so `S₃` cannot
be cyclic.  Adapted from the original candidate artifact's finite witness. -/
lemma apm_b93J01_not_isCyclic_S3 :
    ¬IsCyclic (Equiv.Perm (Fin 3)) := by
  have hneq :
      ((Equiv.swap (0 : Fin 3) 1 : Equiv.Perm (Fin 3)) * Equiv.swap 1 2) ≠
        (Equiv.swap 1 2 * (Equiv.swap (0 : Fin 3) 1)) := by
    decide
  intro h
  letI : IsCyclic (Equiv.Perm (Fin 3)) := h
  exact hneq (IsCyclic.commutative.comm _ _)

lemma apm_b93J01_card_Q8 : Fintype.card (QuaternionGroup 2) = 8 := by
  rw [QuaternionGroup.card]

lemma apm_b93J01_center_card_eq_two_of_card_eight_noncommutative
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 8)
    (hncomm : ¬∀ a b : G, a * b = b * a) :
    Nat.card (Subgroup.center G) = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpgroup : IsPGroup 2 G := IsPGroup.of_card (p := 2) (n := 3) (by
    rw [Nat.card_eq_fintype_card, hG]
    norm_num)
  haveI : Nontrivial G := by
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_eq_fintype_card, hG]
    norm_num
  have hcenter_nontrivial : Nontrivial (Subgroup.center G) :=
    hpgroup.center_nontrivial
  have hcenter_gt_one : 1 < Nat.card (Subgroup.center G) :=
    Finite.one_lt_card_iff_nontrivial.mpr hcenter_nontrivial
  have hcenter_dvd : Nat.card (Subgroup.center G) ∣ 8 := by
    simpa [Nat.card_eq_fintype_card, hG] using
      (Subgroup.center G).card_subgroup_dvd_card
  have hmem : Nat.card (Subgroup.center G) ∈ Nat.divisors 8 :=
    Nat.mem_divisors.mpr ⟨hcenter_dvd, by norm_num⟩
  have hdivs : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  rw [hdivs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h2 | h4 | h8
  · omega
  · exact h2
  · exfalso
    have hquot : Nat.card (G ⧸ Subgroup.center G) = 2 := by
      have hm := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
      rw [Nat.card_eq_fintype_card, hG, h4] at hm
      omega
    letI : IsCyclic (G ⧸ Subgroup.center G) := isCyclic_of_prime_card hquot
    apply hncomm
    exact commutative_of_cyclic_center_quotient
      (QuotientGroup.mk' (Subgroup.center G))
      (by rw [QuotientGroup.ker_mk'])
  · exfalso
    have hquot : Nat.card (G ⧸ Subgroup.center G) = 1 := by
      have hm := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
      rw [Nat.card_eq_fintype_card, hG, h8] at hm
      omega
    letI : Subsingleton (G ⧸ Subgroup.center G) :=
      Finite.card_le_one_iff_subsingleton.mp (by omega)
    letI : IsCyclic (G ⧸ Subgroup.center G) := inferInstance
    apply hncomm
    exact commutative_of_cyclic_center_quotient
      (QuotientGroup.mk' (Subgroup.center G))
      (by rw [QuotientGroup.ker_mk'])

lemma apm_b93J01_exists_order_four_of_card_eight_noncommutative
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 8)
    (hncomm : ¬∀ a b : G, a * b = b * a) :
    ∃ x : G, orderOf x = 4 := by
  have hex : ∃ x : G, x ^ 2 ≠ 1 := by
    by_contra h
    push_neg at h
    apply hncomm
    intro a b
    have haa : a * a = 1 := by simpa only [pow_two] using h a
    have hbb : b * b = 1 := by simpa only [pow_two] using h b
    have habab : (a * b) * (a * b) = 1 := by
      simpa only [pow_two] using h (a * b)
    have hainv : a⁻¹ = a := (mul_eq_one_iff_eq_inv.mp haa).symm
    have hbinv : b⁻¹ = b := (mul_eq_one_iff_eq_inv.mp hbb).symm
    have habinv : (a * b)⁻¹ = a * b :=
      (mul_eq_one_iff_eq_inv.mp habab).symm
    calc
      a * b = (a * b)⁻¹ := habinv.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hainv, hbinv]
  obtain ⟨x, hx⟩ := hex
  have hdvd : orderOf x ∣ 8 := by simpa [hG] using (orderOf_dvd_card (x := x))
  have hmem : orderOf x ∈ Nat.divisors 8 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdivs : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  rw [hdivs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h2 | h4 | h8
  · exact (hx (by rw [orderOf_eq_one_iff.mp h1]; simp)).elim
  · exact (hx (orderOf_dvd_iff_pow_eq_one.mp (h2 ▸ dvd_rfl))).elim
  · exact ⟨x, h4⟩
  · exfalso
    apply hncomm
    letI : IsCyclic G := isCyclic_of_orderOf_eq_card x (by
      rw [Nat.card_eq_fintype_card, hG, h8])
    exact IsCyclic.commutative.comm

lemma apm_b93J01_exists_normal_cyclic_index_two_of_card_eight_noncommutative
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 8)
    (hncomm : ¬∀ a b : G, a * b = b * a) :
    ∃ x : G, orderOf x = 4 ∧ (Subgroup.zpowers x).index = 2 ∧
      (Subgroup.zpowers x).Normal := by
  obtain ⟨x, hx⟩ :=
    apm_b93J01_exists_order_four_of_card_eight_noncommutative G hG hncomm
  have hindex : (Subgroup.zpowers x).index = 2 := by
    have hm := (Subgroup.zpowers x).card_mul_index
    rw [Nat.card_zpowers, hx, Nat.card_eq_fintype_card, hG] at hm
    omega
  exact ⟨x, hx, hindex, Subgroup.normal_of_index_eq_two hindex⟩

/-- A noncommutative group of order eight admits the usual two-generator
presentation seam: an element `x` of order four and an element `y` outside
`⟨x⟩`.  They generate the whole group, while `y²` lies in `⟨x⟩`.

This isolates the finite-cardinality argument needed before distinguishing
the dihedral and quaternion relations. -/
lemma apm_b93J01_exists_order_four_generating_pair_of_card_eight_noncommutative
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 8)
    (hncomm : ¬∀ a b : G, a * b = b * a) :
    ∃ x y : G, orderOf x = 4 ∧ y ∉ Subgroup.zpowers x ∧
      y ^ 2 ∈ Subgroup.zpowers x ∧
      Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤ := by
  obtain ⟨x, hx, hindex, -⟩ :=
    apm_b93J01_exists_normal_cyclic_index_two_of_card_eight_noncommutative
      G hG hncomm
  let H : Subgroup G := Subgroup.zpowers x
  have hGnat : Nat.card G = 8 := by rw [Nat.card_eq_fintype_card, hG]
  have hHcard : Nat.card H = 4 := by
    rw [show H = Subgroup.zpowers x from rfl, Nat.card_zpowers, hx]
  have hHne : H ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.card_top, hGnat] at hHcard
    omega
  obtain ⟨y, -, hy⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hHne)
  have hy2 : y ^ 2 ∈ H := H.sq_mem_of_index_two hindex y
  let K : Subgroup G := H ⊔ Subgroup.zpowers y
  have hHK : H ≤ K := le_sup_left
  have hyK : y ∈ K :=
    (le_sup_right : Subgroup.zpowers y ≤ K) (Subgroup.mem_zpowers y)
  have hHKne : H ≠ K := by
    intro heq
    exact hy (heq ▸ hyK)
  have hKcard_ge : 4 ≤ Nat.card K := by
    rw [← hHcard]
    exact Nat.card_le_card_of_injective
      (fun z : H => (⟨z, hHK z.property⟩ : K))
      (fun _ _ h => Subtype.ext (congrArg (fun z : K => (z : G)) h))
  have hKcard_ne : Nat.card K ≠ 4 := by
    intro hKcard
    apply hHKne
    exact Subgroup.eq_of_le_of_card_ge hHK (by omega)
  have hdvd : Nat.card K ∣ 8 := by
    simpa [hG] using K.card_subgroup_dvd_card
  have hmem : Nat.card K ∈ Nat.divisors 8 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdivs : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  rw [hdivs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hKcard : Nat.card K = 8 := by omega
  have hKtop : K = ⊤ := Subgroup.eq_top_of_card_eq K (by
    rw [hKcard, hGnat])
  exact ⟨x, y, hx, hy, hy2, hKtop⟩

/-- The square of the exterior generator in the preceding presentation seam
is either the identity or the unique involution in `⟨x⟩`. -/
lemma apm_b93J01_exterior_generator_square_cases
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 8)
    (hncomm : ¬∀ a b : G, a * b = b * a)
    {x y : G} (hx : orderOf x = 4) (hy2 : y ^ 2 ∈ Subgroup.zpowers x) :
    y ^ 2 = 1 ∨ y ^ 2 = x ^ 2 := by
  classical
  have hydvd : orderOf y ∣ 8 := by
    simpa [hG] using (orderOf_dvd_card (x := y))
  have hymem : orderOf y ∈ Nat.divisors 8 :=
    Nat.mem_divisors.mpr ⟨hydvd, by norm_num⟩
  have hdivs : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  rw [hdivs] at hymem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hymem
  have hyord_ne : orderOf y ≠ 8 := by
    intro hyord
    apply hncomm
    letI : IsCyclic G := isCyclic_of_orderOf_eq_card y (by
      rw [Nat.card_eq_fintype_card, hG, hyord])
    exact IsCyclic.commutative.comm
  have hy4 : y ^ 4 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    rcases hymem with h1 | h2 | h4 | h8
    · rw [h1]; norm_num
    · rw [h2]; norm_num
    · rw [h4]
    · exact (hyord_ne h8).elim
  rw [mem_zpowers_iff_mem_range_orderOf, hx] at hy2
  simp only [Finset.mem_image, Finset.mem_range] at hy2
  obtain ⟨n, hn, hxy⟩ := hy2
  have hxpow : x ^ (n * 2) = 1 := by
    rw [pow_mul, hxy, ← pow_mul, show 2 * 2 = 4 by norm_num, hy4]
  have hxdvd : 4 ∣ n * 2 := by
    rw [← hx]
    exact orderOf_dvd_of_pow_eq_one hxpow
  interval_cases n <;> simp_all

lemma apm_b93J01_exists_order_eight_presentation_data
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 8)
    (hncomm : ¬∀ a b : G, a * b = b * a) :
    ∃ x y : G, orderOf x = 4 ∧ y ∉ Subgroup.zpowers x ∧
      (y ^ 2 = 1 ∨ y ^ 2 = x ^ 2) ∧
      Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤ := by
  obtain ⟨x, y, hx, hy, hy2, hgen⟩ :=
    apm_b93J01_exists_order_four_generating_pair_of_card_eight_noncommutative
      G hG hncomm
  exact ⟨x, y, hx, hy,
    apm_b93J01_exterior_generator_square_cases G hG hncomm hx hy2, hgen⟩

/-- Conjugation acts on any cyclic subgroup of order four in a group of
order eight either trivially or by inversion. -/
lemma apm_b93J01_conjugate_order_four_eq_self_or_inv
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 8)
    {x y : G} (hx : orderOf x = 4) :
    y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x⁻¹ := by
  classical
  let H : Subgroup G := Subgroup.zpowers x
  have hindex : (Subgroup.zpowers x).index = 2 := by
    have hm := (Subgroup.zpowers x).card_mul_index
    rw [Nat.card_zpowers, hx,
      Nat.card_eq_fintype_card, hG] at hm
    omega
  have hc : y * x * y⁻¹ ∈ H :=
    (Subgroup.normal_of_index_eq_two hindex).conj_mem x
      (Subgroup.mem_zpowers x) y
  have hco : orderOf (y * x * y⁻¹) = 4 := by
    rw [← (SemiconjBy.conj_mk y x).orderOf_eq y, hx]
  rw [show H = Subgroup.zpowers x from rfl,
    mem_zpowers_iff_mem_range_orderOf, hx] at hc
  simp only [Finset.mem_image, Finset.mem_range] at hc
  obtain ⟨n, hn, hxn⟩ := hc
  interval_cases n
  · rw [← hxn] at hco
    simp at hco
  · left
    simpa using hxn.symm
  · rw [← hxn] at hco
    simp [orderOf_pow, hx] at hco
  · right
    rw [← hxn]
    rw [← mul_left_cancel_iff (a := x)]
    simpa [← pow_succ'] using (show x ^ 4 = 1 from
      orderOf_dvd_iff_pow_eq_one.mp (by rw [hx]))

/-- If two cyclic subgroups generated by commuting elements generate the
whole group, the ambient group is commutative. -/
lemma apm_b93J01_commutative_of_commuting_cyclic_generators
    (G : Type*) [Group G] {x y : G} (hxy : Commute x y)
    (hgen : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤) :
    ∀ a b : G, a * b = b * a := by
  let s : Set G := {x, y}
  have hscomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    intro a ha b hb
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · simp [ha, hb]
    · simpa [ha, hb] using hxy.eq
    · simpa [ha, hb] using hxy.symm.eq
    · simp [ha, hb]
  have hs : Subgroup.closure s = ⊤ := by
    rw [show s = ({x} : Set G) ∪ {y} by ext z; simp [s, or_comm],
      Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
    exact hgen
  letI : CommGroup (Subgroup.closure s) :=
    Subgroup.closureCommGroupOfComm hscomm
  intro a b
  have ha : a ∈ Subgroup.closure s := by rw [hs]; simp
  have hb : b ∈ Subgroup.closure s := by rw [hs]; simp
  exact congrArg Subtype.val
    (mul_comm (⟨a, ha⟩ : Subgroup.closure s) (⟨b, hb⟩ : Subgroup.closure s))

/-- In the noncommutative case the action on the cyclic subgroup cannot be
trivial, so the exterior generator acts by inversion. -/
lemma apm_b93J01_conjugate_order_four_eq_inv_of_generates_noncommutative
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 8)
    (hncomm : ¬∀ a b : G, a * b = b * a) {x y : G}
    (hx : orderOf x = 4)
    (hgen : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤) :
    y * x * y⁻¹ = x⁻¹ := by
  rcases apm_b93J01_conjugate_order_four_eq_self_or_inv G hG
      (x := x) (y := y) hx with hself | hinv
  · exfalso
    apply hncomm
    apply apm_b93J01_commutative_of_commuting_cyclic_generators G
    · apply Commute.symm
      have hyx : y * x = x * y := calc
        y * x = (y * x * y⁻¹) * y := by group
        _ = x * y := by rw [hself]
      exact hyx
    · exact hgen
  · exact hinv

/-- Complete presentation data needed to map the two concrete order-eight
models into an arbitrary noncommutative group of order eight. -/
lemma apm_b93J01_exists_order_eight_model_relations
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 8)
    (hncomm : ¬∀ a b : G, a * b = b * a) :
    ∃ x y : G, orderOf x = 4 ∧
      (y ^ 2 = 1 ∨ y ^ 2 = x ^ 2) ∧
      y * x * y⁻¹ = x⁻¹ ∧
      Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤ := by
  obtain ⟨x, y, hx, -, hy2, hgen⟩ :=
    apm_b93J01_exists_order_eight_presentation_data G hG hncomm
  exact ⟨x, y, hx, hy2,
    apm_b93J01_conjugate_order_four_eq_inv_of_generates_noncommutative
      G hG hncomm hx hgen,
    hgen⟩

/-- The inversion conjugation relation propagates to every integral power;
this is the rewrite used by both concrete normal-form multiplication proofs. -/
lemma apm_b93J01_exterior_mul_zpow
    (G : Type*) [Group G] {x y : G} (hyx : y * x * y⁻¹ = x⁻¹)
    (n : ℤ) :
    y * x ^ n = x ^ (-n) * y := by
  have hsemi : SemiconjBy y x x⁻¹ := by
    rw [SemiconjBy]
    calc
      y * x = (y * x * y⁻¹) * y := by group
      _ = x⁻¹ * y := by rw [hyx]
  have hn := hsemi.zpow_right n
  rw [SemiconjBy] at hn
  simpa only [inv_zpow, ← zpow_neg] using hn

lemma apm_b93J01_zpow_mul_exterior
    (G : Type*) [Group G] {x y : G} (hyx : y * x * y⁻¹ = x⁻¹)
    (n : ℤ) :
    x ^ n * y = y * x ^ (-n) := by
  simpa only [neg_neg] using
    (apm_b93J01_exterior_mul_zpow G hyx (-n)).symm

lemma apm_b93J01_rotation_mul_rotation
    (G : Type*) [Group G] (x : G) (i j : ℤ) :
    x ^ i * x ^ j = x ^ (i + j) := by
  rw [zpow_add]

lemma apm_b93J01_rotation_mul_exterior
    (G : Type*) [Group G] {x y : G} (hyx : y * x * y⁻¹ = x⁻¹)
    (i j : ℤ) :
    x ^ i * (y * x ^ j) = y * x ^ (j - i) := by
  rw [← mul_assoc, apm_b93J01_zpow_mul_exterior G hyx]
  simp only [sub_eq_add_neg, mul_assoc, ← zpow_add]
  rw [add_comm]

lemma apm_b93J01_exterior_mul_rotation
    (G : Type*) [Group G] (x y : G) (i j : ℤ) :
    (y * x ^ i) * x ^ j = y * x ^ (i + j) := by
  simp only [mul_assoc, zpow_add]

lemma apm_b93J01_exterior_mul_exterior
    (G : Type*) [Group G] {x y z : G} (hyx : y * x * y⁻¹ = x⁻¹)
    (hy2 : y ^ 2 = z) (i j : ℤ) :
    (y * x ^ i) * (y * x ^ j) = z * x ^ (j - i) := by
  rw [show (y * x ^ i) * (y * x ^ j) =
      y * ((x ^ i * y) * x ^ j) by group,
    apm_b93J01_zpow_mul_exterior G hyx]
  calc
    y * (y * x ^ (-i) * x ^ j) = y ^ 2 * (x ^ (-i) * x ^ j) := by
      simp only [pow_two]; group
    _ = z * x ^ (j - i) := by
      rw [hy2, ← zpow_add]
      congr 2
      omega

/-- A chosen order-four element gives a canonical cyclic-coordinate
equivalence, avoiding any dependence on representatives of `ZMod 4`. -/
noncomputable def apm_b93J01_orderFourEquivZPowers
    (G : Type*) [Group G] (x : G) (hx : orderOf x = 4) :
    Multiplicative (ZMod 4) ≃* Subgroup.zpowers x := by
  let g : Subgroup.zpowers x := ⟨x, Subgroup.mem_zpowers x⟩
  have hg : ∀ z : Subgroup.zpowers x, z ∈ Subgroup.zpowers g := by
    intro z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp z.property
    apply Subgroup.mem_zpowers_iff.mpr
    exact ⟨k, Subtype.ext hk⟩
  have hn : Nat.card (Subgroup.zpowers x) = 4 := by
    rw [Nat.card_zpowers, hx]
  exact zmodMulEquivOfGenerator hg hn

@[simp]
lemma apm_b93J01_orderFourEquivZPowers_one
    (G : Type*) [Group G] (x : G) (hx : orderOf x = 4) :
    (apm_b93J01_orderFourEquivZPowers G x hx
      (Multiplicative.ofAdd 1) : G) = x := by
  simp [apm_b93J01_orderFourEquivZPowers,
    zmodMulEquivOfGenerator_apply_ofAdd_one]

noncomputable def apm_b93J01_orderFourHom
    (G : Type*) [Group G] (x : G) (hx : orderOf x = 4) :
    Multiplicative (ZMod 4) →* G :=
  (Subgroup.zpowers x).subtype.comp
    (apm_b93J01_orderFourEquivZPowers G x hx).toMonoidHom

@[simp]
lemma apm_b93J01_orderFourHom_one_generator
    (G : Type*) [Group G] (x : G) (hx : orderOf x = 4) :
    apm_b93J01_orderFourHom G x hx (Multiplicative.ofAdd 1) = x := by
  exact apm_b93J01_orderFourEquivZPowers_one G x hx

lemma apm_b93J01_orderFourHom_surjective_onto_zpowers
    (G : Type*) [Group G] (x : G) (hx : orderOf x = 4)
    {z : G} (hz : z ∈ Subgroup.zpowers x) :
    ∃ i : Multiplicative (ZMod 4), apm_b93J01_orderFourHom G x hx i = z := by
  let e := apm_b93J01_orderFourEquivZPowers G x hx
  exact ⟨e.symm ⟨z, hz⟩, congrArg Subtype.val (e.apply_symm_apply ⟨z, hz⟩)⟩

lemma apm_b93J01_exterior_mul_of_mem_zpowers
    (G : Type*) [Group G] {x y z : G} (hyx : y * x * y⁻¹ = x⁻¹)
    (hz : z ∈ Subgroup.zpowers x) :
    y * z = z⁻¹ * y := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  simpa only [zpow_neg] using apm_b93J01_exterior_mul_zpow G hyx n

lemma apm_b93J01_mem_zpowers_mul_exterior
    (G : Type*) [Group G] {x y z : G} (hyx : y * x * y⁻¹ = x⁻¹)
    (hz : z ∈ Subgroup.zpowers x) :
    z * y = y * z⁻¹ := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  simpa only [zpow_neg] using apm_b93J01_zpow_mul_exterior G hyx n

noncomputable def apm_b93J01_dihedralHom
    (G : Type*) [Group G] (x y : G) (hx : orderOf x = 4)
    (hy2 : y ^ 2 = 1) (hyx : y * x * y⁻¹ = x⁻¹) :
    DihedralGroup 4 →* G := by
  let r := apm_b93J01_orderFourHom G x hx
  have hr (i : Multiplicative (ZMod 4)) :
      r i ∈ Subgroup.zpowers x :=
    (apm_b93J01_orderFourEquivZPowers G x hx i).property
  refine
    { toFun := fun d => match d with
        | DihedralGroup.r i => r (Multiplicative.ofAdd i)
        | DihedralGroup.sr i => y * r (Multiplicative.ofAdd i)
      map_one' := by
        change r (Multiplicative.ofAdd 0) = 1
        exact map_one r
      map_mul' := ?_ }
  rintro (i | i) (j | j)
  · simp only [DihedralGroup.r_mul_r]
    simp
  · simp only [DihedralGroup.r_mul_sr]
    rw [← mul_assoc, apm_b93J01_mem_zpowers_mul_exterior G hyx (hr _)]
    rw [mul_assoc, ← map_inv, ← map_mul]
    congr 2
    change j - i = -i + j
    abel

  · simp only [DihedralGroup.sr_mul_r]
    rw [mul_assoc, ← map_mul]
    rfl
  · simp only [DihedralGroup.sr_mul_sr]
    rw [show (y * r (Multiplicative.ofAdd i)) *
        (y * r (Multiplicative.ofAdd j)) =
      y * (r (Multiplicative.ofAdd i) * y) *
        r (Multiplicative.ofAdd j) by group]
    rw [apm_b93J01_mem_zpowers_mul_exterior G hyx (hr _)]
    rw [show y * (y * (r (Multiplicative.ofAdd i))⁻¹) *
        r (Multiplicative.ofAdd j) =
      y ^ 2 * ((r (Multiplicative.ofAdd i))⁻¹ *
        r (Multiplicative.ofAdd j)) by simp only [pow_two]; group]
    rw [hy2, one_mul, ← map_inv, ← map_mul]
    congr 1
    change j - i = -i + j
    abel

@[simp]
lemma apm_b93J01_dihedralHom_r_one
    (G : Type*) [Group G] (x y : G) (hx : orderOf x = 4)
    (hy2 : y ^ 2 = 1) (hyx : y * x * y⁻¹ = x⁻¹) :
    apm_b93J01_dihedralHom G x y hx hy2 hyx (DihedralGroup.r 1) = x := by
  simp [apm_b93J01_dihedralHom,
    apm_b93J01_orderFourHom_one_generator]

@[simp]
lemma apm_b93J01_dihedralHom_sr_zero
    (G : Type*) [Group G] (x y : G) (hx : orderOf x = 4)
    (hy2 : y ^ 2 = 1) (hyx : y * x * y⁻¹ = x⁻¹) :
    apm_b93J01_dihedralHom G x y hx hy2 hyx (DihedralGroup.sr 0) = y := by
  simp [apm_b93J01_dihedralHom]

lemma apm_b93J01_dihedralHom_surjective_of_generates
    (G : Type*) [Group G] (x y : G) (hx : orderOf x = 4)
    (hy2 : y ^ 2 = 1) (hyx : y * x * y⁻¹ = x⁻¹)
    (hgen : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤) :
    Function.Surjective (apm_b93J01_dihedralHom G x y hx hy2 hyx) := by
  rw [← MonoidHom.range_eq_top]
  apply le_antisymm le_top
  rw [← hgen]
  apply sup_le
  · rw [Subgroup.zpowers_le]
    exact ⟨DihedralGroup.r 1, apm_b93J01_dihedralHom_r_one G x y hx hy2 hyx⟩
  · rw [Subgroup.zpowers_le]
    exact ⟨DihedralGroup.sr 0, apm_b93J01_dihedralHom_sr_zero G x y hx hy2 hyx⟩

noncomputable def apm_b93J01_dihedralEquivOfRelations
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 8)
    (x y : G) (hx : orderOf x = 4) (hy2 : y ^ 2 = 1)
    (hyx : y * x * y⁻¹ = x⁻¹)
    (hgen : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤) :
    DihedralGroup 4 ≃* G := by
  let f := apm_b93J01_dihedralHom G x y hx hy2 hyx
  have hsurj : Function.Surjective f :=
    apm_b93J01_dihedralHom_surjective_of_generates G x y hx hy2 hyx hgen
  apply MulEquiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  exact ⟨hsurj, by rw [DihedralGroup.card, hG]⟩

noncomputable def apm_b93J01_quaternionHom
    (G : Type*) [Group G] (x y : G) (hx : orderOf x = 4)
    (hy2 : y ^ 2 = x ^ 2) (hyx : y * x * y⁻¹ = x⁻¹) :
    QuaternionGroup 2 →* G := by
  let r := apm_b93J01_orderFourHom G x hx
  have hr (i : Multiplicative (ZMod 4)) :
      r i ∈ Subgroup.zpowers x :=
    (apm_b93J01_orderFourEquivZPowers G x hx i).property
  have hr_two : r (Multiplicative.ofAdd 2) = x ^ 2 := by
    rw [show Multiplicative.ofAdd (2 : ZMod 4) =
        (Multiplicative.ofAdd 1) ^ 2 by
          change (2 : ZMod 4) = 1 + 1
          norm_num,
      map_pow, apm_b93J01_orderFourHom_one_generator]
  refine
    { toFun := fun q => match q with
        | QuaternionGroup.a i => r (Multiplicative.ofAdd i)
        | QuaternionGroup.xa i => y * r (Multiplicative.ofAdd i)
      map_one' := by
        change r (Multiplicative.ofAdd 0) = 1
        exact map_one r
      map_mul' := ?_ }
  rintro (i | i) (j | j)
  · simp only [QuaternionGroup.a_mul_a]
    simp
  · simp only [QuaternionGroup.a_mul_xa]
    rw [← mul_assoc, apm_b93J01_mem_zpowers_mul_exterior G hyx (hr _)]
    rw [mul_assoc, ← map_inv, ← map_mul]
    congr 2
    change j - i = -i + j
    abel
  · simp only [QuaternionGroup.xa_mul_a]
    rw [mul_assoc, ← map_mul]
    rfl
  · simp only [QuaternionGroup.xa_mul_xa]
    rw [show (y * r (Multiplicative.ofAdd i)) *
        (y * r (Multiplicative.ofAdd j)) =
      y * (r (Multiplicative.ofAdd i) * y) *
        r (Multiplicative.ofAdd j) by group]
    rw [apm_b93J01_mem_zpowers_mul_exterior G hyx (hr _)]
    rw [show y * (y * (r (Multiplicative.ofAdd i))⁻¹) *
        r (Multiplicative.ofAdd j) =
      y ^ 2 * ((r (Multiplicative.ofAdd i))⁻¹ *
        r (Multiplicative.ofAdd j)) by simp only [pow_two]; group]
    rw [hy2, ← hr_two, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    change (2 : ZMod 4) + j - i = 2 + (-i + j)
    abel

@[simp]
lemma apm_b93J01_quaternionHom_a_one
    (G : Type*) [Group G] (x y : G) (hx : orderOf x = 4)
    (hy2 : y ^ 2 = x ^ 2) (hyx : y * x * y⁻¹ = x⁻¹) :
    apm_b93J01_quaternionHom G x y hx hy2 hyx (QuaternionGroup.a 1) = x := by
  simp [apm_b93J01_quaternionHom,
    apm_b93J01_orderFourHom_one_generator]

@[simp]
lemma apm_b93J01_quaternionHom_xa_zero
    (G : Type*) [Group G] (x y : G) (hx : orderOf x = 4)
    (hy2 : y ^ 2 = x ^ 2) (hyx : y * x * y⁻¹ = x⁻¹) :
    apm_b93J01_quaternionHom G x y hx hy2 hyx (QuaternionGroup.xa 0) = y := by
  simp [apm_b93J01_quaternionHom]

lemma apm_b93J01_quaternionHom_surjective_of_generates
    (G : Type*) [Group G] (x y : G) (hx : orderOf x = 4)
    (hy2 : y ^ 2 = x ^ 2) (hyx : y * x * y⁻¹ = x⁻¹)
    (hgen : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤) :
    Function.Surjective (apm_b93J01_quaternionHom G x y hx hy2 hyx) := by
  rw [← MonoidHom.range_eq_top]
  apply le_antisymm le_top
  rw [← hgen]
  apply sup_le
  · rw [Subgroup.zpowers_le]
    exact ⟨QuaternionGroup.a 1,
      apm_b93J01_quaternionHom_a_one G x y hx hy2 hyx⟩
  · rw [Subgroup.zpowers_le]
    exact ⟨QuaternionGroup.xa 0,
      apm_b93J01_quaternionHom_xa_zero G x y hx hy2 hyx⟩

noncomputable def apm_b93J01_quaternionEquivOfRelations
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 8)
    (x y : G) (hx : orderOf x = 4) (hy2 : y ^ 2 = x ^ 2)
    (hyx : y * x * y⁻¹ = x⁻¹)
    (hgen : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤) :
    QuaternionGroup 2 ≃* G := by
  let f := apm_b93J01_quaternionHom G x y hx hy2 hyx
  have hsurj : Function.Surjective f :=
    apm_b93J01_quaternionHom_surjective_of_generates G x y hx hy2 hyx hgen
  apply MulEquiv.ofBijective f
  rw [Fintype.bijective_iff_surjective_and_card]
  exact ⟨hsurj, by rw [QuaternionGroup.card, hG]⟩

lemma apm_b93J01_noncommutative_card_eight_classification
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 8)
    (hncomm : ¬∀ a b : G, a * b = b * a) :
    Nonempty (G ≃* DihedralGroup 4) ∨
      Nonempty (G ≃* QuaternionGroup 2) := by
  obtain ⟨x, y, hx, hy2, hyx, hgen⟩ :=
    apm_b93J01_exists_order_eight_model_relations G hG hncomm
  rcases hy2 with hy2 | hy2
  · exact Or.inl ⟨(apm_b93J01_dihedralEquivOfRelations
      G hG x y hx hy2 hyx hgen).symm⟩
  · exact Or.inr ⟨(apm_b93J01_quaternionEquivOfRelations
      G hG x y hx hy2 hyx hgen).symm⟩

/-- A product of integers greater than one which equals eight has between one
and three factors.  This is the numerical spine of the abelian order-eight
classification after applying the finite abelian group structure theorem. -/
lemma apm_b93J01_card_index_of_prod_eq_eight
    {ι : Type*} [Fintype ι] (n : ι → ℕ)
    (hn : ∀ i, 1 < n i) (hprod : ∏ i, n i = 8) :
    1 ≤ Fintype.card ι ∧ Fintype.card ι ≤ 3 := by
  have hpow : 2 ^ Fintype.card ι ≤ ∏ i, n i := by
    simpa using Finset.pow_card_le_prod Finset.univ n 2
      (fun i _ => Nat.succ_le_iff.mpr (hn i))
  have hle : 2 ^ Fintype.card ι ≤ 2 ^ 3 := by
    norm_num [hprod] at hpow ⊢
    exact hpow
  have hcard_le : Fintype.card ι ≤ 3 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  have hcard_pos : 1 ≤ Fintype.card ι := by
    by_contra h
    have : Fintype.card ι = 0 := by omega
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp this
    simp at hprod
  exact ⟨hcard_pos, hcard_le⟩

lemma apm_b93J01_two_factors_of_product_eight
    {a b : ℕ} (ha : 1 < a) (hb : 1 < b) (hab : a * b = 8) :
    (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) := by
  have hadvd : a ∣ 8 := ⟨b, hab.symm⟩
  have hbdvd : b ∣ 8 := ⟨a, by simpa [mul_comm] using hab.symm⟩
  have hale : a ≤ 8 := Nat.le_of_dvd (by norm_num) hadvd
  have hble : b ≤ 8 := Nat.le_of_dvd (by norm_num) hbdvd
  interval_cases a <;> interval_cases b <;> all_goals norm_num at *

lemma apm_b93J01_three_factors_of_product_eight
    {a b c : ℕ} (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (habc : a * b * c = 8) :
    a = 2 ∧ b = 2 ∧ c = 2 := by
  have hadvd : a ∣ 8 := ⟨b * c, by simpa [mul_assoc] using habc.symm⟩
  have hbdvd : b ∣ 8 := ⟨a * c, by
    calc
      8 = a * b * c := habc.symm
      _ = b * (a * c) := by ac_rfl⟩
  have hcdvd : c ∣ 8 := ⟨a * b, by
    calc
      8 = a * b * c := habc.symm
      _ = c * (a * b) := by ac_rfl⟩
  have hale : a ≤ 8 := Nat.le_of_dvd (by norm_num) hadvd
  have hble : b ≤ 8 := Nat.le_of_dvd (by norm_num) hbdvd
  have hcle : c ≤ 8 := Nat.le_of_dvd (by norm_num) hcdvd
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    all_goals norm_num at *

def apm_b93J01_piReindexMulEquiv
    {ι κ : Type*} (e : ι ≃ κ) (M : ι → Type*) [∀ i, Mul (M i)] :
    (∀ i, M i) ≃* (∀ k, M (e.symm k)) :=
  { Equiv.piCongrLeft' M e with map_mul' := fun _ _ => rfl }

def apm_b93J01_piFinOneMulEquiv
    (M : Fin 1 → Type*) [∀ i, Mul (M i)] :
    (∀ i, M i) ≃* M 0 := MulEquiv.piUnique M

def apm_b93J01_piFinTwoMulEquiv
    (M : Fin 2 → Type*) [∀ i, Mul (M i)] :
    (∀ i, M i) ≃* M 0 × M 1 :=
  { piFinTwoEquiv M with map_mul' := fun _ _ => rfl }

def apm_b93J01_prodSwapMulEquiv
    (A B : Type*) [Mul A] [Mul B] : A × B ≃* B × A :=
  { Equiv.prodComm A B with map_mul' := fun _ _ => rfl }

def apm_b93J01_piFinThreeMulEquiv
    (M : Type*) [Mul M] :
    (Fin 3 → M) ≃* M × (M × M) where
  toFun f := (f 0, (f 1, f 2))
  invFun p i := ![p.1, p.2.1, p.2.2] i
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a, ⟨b, c⟩⟩; rfl
  map_mul' _ _ := rfl

def apm_b93J01_piFinOneZModEquiv (m : ℕ) :
    (Fin 1 → Multiplicative (ZMod m)) ≃* Multiplicative (ZMod m) :=
  apm_b93J01_piFinOneMulEquiv _

def apm_b93J01_piFinTwoZModEquiv (m n : ℕ) :
    ((i : Fin 2) → Multiplicative (ZMod (![m, n] i))) ≃*
      Multiplicative (ZMod m × ZMod n) :=
  (apm_b93J01_piFinTwoMulEquiv
    (fun i : Fin 2 => Multiplicative (ZMod (![m, n] i)))).trans
      (MulEquiv.prodMultiplicative (ZMod m) (ZMod n)).symm

def apm_b93J01_piFinThreeZModTwoEquiv :
    (Fin 3 → Multiplicative (ZMod 2)) ≃*
      Multiplicative (ZMod 2 × ZMod 2 × ZMod 2) :=
  (apm_b93J01_piFinThreeMulEquiv (Multiplicative (ZMod 2))).trans <|
    ((MulEquiv.refl (Multiplicative (ZMod 2))).prodCongr
      (MulEquiv.prodMultiplicative (ZMod 2) (ZMod 2)).symm).trans
        (MulEquiv.prodMultiplicative (ZMod 2) (ZMod 2 × ZMod 2)).symm

lemma apm_b93J01_pi_zmod_order_eight
    {ι : Type*} [Fintype ι] (n : ι → ℕ)
    (hn : ∀ i, 1 < n i) (hprod : ∏ i, n i = 8) :
    Nonempty (((i : ι) → Multiplicative (ZMod (n i))) ≃*
      Multiplicative (ZMod 8)) ∨
    Nonempty (((i : ι) → Multiplicative (ZMod (n i))) ≃*
      Multiplicative (ZMod 4 × ZMod 2)) ∨
    Nonempty (((i : ι) → Multiplicative (ZMod (n i))) ≃*
      Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)) := by
  rcases apm_b93J01_card_index_of_prod_eq_eight n hn hprod with ⟨hpos, hle⟩
  have hcases : Fintype.card ι = 1 ∨ Fintype.card ι = 2 ∨
      Fintype.card ι = 3 := by omega
  rcases hcases with hcard | hcard | hcard
  · let e : ι ≃ Fin 1 := (Fintype.equivFin ι).trans (finCongr hcard)
    let m : Fin 1 → ℕ := fun j => n (e.symm j)
    have hmprod : ∏ j, m j = 8 := by
      rw [← hprod]
      simpa [m] using (e.prod_comp m).symm
    have hm0 : m 0 = 8 := by simpa using hmprod
    have hm : m = fun _ => 8 := by funext j; fin_cases j; exact hm0
    let ep := apm_b93J01_piReindexMulEquiv e
      (fun i => Multiplicative (ZMod (n i)))
    change Nonempty (((i : ι) → Multiplicative (ZMod (n i))) ≃*
      Multiplicative (ZMod 8)) ∨ _
    left
    change ((i : ι) → Multiplicative (ZMod (n i))) ≃*
      ((k : Fin 1) → Multiplicative (ZMod (m k))) at ep
    rw [hm] at ep
    exact ⟨ep.trans (apm_b93J01_piFinOneZModEquiv 8)⟩
  · let e : ι ≃ Fin 2 := (Fintype.equivFin ι).trans (finCongr hcard)
    let m : Fin 2 → ℕ := fun j => n (e.symm j)
    have hmprod : ∏ j, m j = 8 := by
      rw [← hprod]
      simpa [m] using (e.prod_comp m).symm
    have hmprod' : m 0 * m 1 = 8 := by simpa using hmprod
    rcases apm_b93J01_two_factors_of_product_eight
      (hn (e.symm 0)) (hn (e.symm 1)) hmprod' with hm | hm
    · right; left
      let ep := apm_b93J01_piReindexMulEquiv e
        (fun i => Multiplicative (ZMod (n i)))
      have hmf : m = ![2, 4] := by
        funext j; fin_cases j
        · exact hm.1
        · exact hm.2
      change ((i : ι) → Multiplicative (ZMod (n i))) ≃*
        ((k : Fin 2) → Multiplicative (ZMod (m k))) at ep
      rw [hmf] at ep
      exact ⟨ep.trans <| (apm_b93J01_piFinTwoMulEquiv
        (fun i : Fin 2 => Multiplicative (ZMod (![2, 4] i)))).trans <|
          (apm_b93J01_prodSwapMulEquiv _ _).trans
            (MulEquiv.prodMultiplicative (ZMod 4) (ZMod 2)).symm⟩
    · right; left
      let ep := apm_b93J01_piReindexMulEquiv e
        (fun i => Multiplicative (ZMod (n i)))
      have hmf : m = ![4, 2] := by
        funext j; fin_cases j
        · exact hm.1
        · exact hm.2
      change ((i : ι) → Multiplicative (ZMod (n i))) ≃*
        ((k : Fin 2) → Multiplicative (ZMod (m k))) at ep
      rw [hmf] at ep
      exact ⟨ep.trans (apm_b93J01_piFinTwoZModEquiv 4 2)⟩
  · let e : ι ≃ Fin 3 := (Fintype.equivFin ι).trans (finCongr hcard)
    let m : Fin 3 → ℕ := fun j => n (e.symm j)
    have hmprod : ∏ j, m j = 8 := by
      rw [← hprod]
      simpa [m] using (e.prod_comp m).symm
    have hmprod' : m 0 * m 1 * m 2 = 8 := by
      simpa [Fin.prod_univ_succ, mul_assoc] using hmprod
    have hm := apm_b93J01_three_factors_of_product_eight
      (hn (e.symm 0)) (hn (e.symm 1)) (hn (e.symm 2)) hmprod'
    right; right
    let ep := apm_b93J01_piReindexMulEquiv e
      (fun i => Multiplicative (ZMod (n i)))
    have hmf : m = fun _ => 2 := by
      funext j; fin_cases j
      · exact hm.1
      · exact hm.2.1
      · exact hm.2.2
    change ((i : ι) → Multiplicative (ZMod (n i))) ≃*
      ((k : Fin 3) → Multiplicative (ZMod (m k))) at ep
    rw [hmf] at ep
    exact ⟨ep.trans apm_b93J01_piFinThreeZModTwoEquiv⟩

lemma apm_b93J01_abelian_card_eight_classification
    (G : Type*) [CommGroup G] [Fintype G] (hG : Fintype.card G = 8) :
    Nonempty (G ≃* Multiplicative (ZMod 8)) ∨
    Nonempty (G ≃* Multiplicative (ZMod 4 × ZMod 2)) ∨
    Nonempty (G ≃* Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)) := by
  classical
  obtain ⟨ι, inst, n, hn, ⟨e⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  letI : Fintype ι := inst
  letI (i : ι) : NeZero (n i) := ⟨by have := hn i; omega⟩
  have hprod : ∏ i, n i = 8 := by
    calc
      ∏ i, n i = Fintype.card ((i : ι) → Multiplicative (ZMod (n i))) := by
        simp [Fintype.card_pi]
      _ = Fintype.card G := (Fintype.card_congr e.toEquiv).symm
      _ = 8 := hG
  rcases apm_b93J01_pi_zmod_order_eight n hn hprod with h | h | h
  · exact Or.inl ⟨e.trans h.some⟩
  · exact Or.inr (Or.inl ⟨e.trans h.some⟩)
  · exact Or.inr (Or.inr ⟨e.trans h.some⟩)

lemma apm_b93J01_card_eight_classification
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 8) :
    Nonempty (G ≃* Multiplicative (ZMod 8)) ∨
    Nonempty (G ≃* Multiplicative (ZMod 4 × ZMod 2)) ∨
    Nonempty (G ≃* Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)) ∨
    Nonempty (G ≃* DihedralGroup 4) ∨
    Nonempty (G ≃* QuaternionGroup 2) := by
  by_cases hcomm : ∀ a b : G, a * b = b * a
  · letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
    rcases apm_b93J01_abelian_card_eight_classification G hG with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases apm_b93J01_noncommutative_card_eight_classification G hG hcomm with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- Two standard quaternion generators witness that `Q₈` is
noncommutative. -/
lemma apm_b93J01_Q8_not_commutative :
    (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  decide

/-- In `Q₈`, only `1` and the central element of order two square to one. -/
lemma apm_b93J01_card_Q8_sq_eq_one :
    Fintype.card {x : QuaternionGroup 2 // x ^ 2 = 1} = 2 := by
  decide

/-- In the dihedral group of order eight, the identity, the half-turn, and
all four reflections square to one. -/
lemma apm_b93J01_card_D4_sq_eq_one :
    Fintype.card {x : DihedralGroup 4 // x ^ 2 = 1} = 6 := by
  decide

/-- The number of solutions to `x² = 1` is invariant under a group
equivalence, separating `Q₈` from the dihedral group of order eight. -/
lemma apm_b93J01_Q8_not_equiv_D4 :
    ¬Nonempty (QuaternionGroup 2 ≃* DihedralGroup 4) := by
  rintro ⟨e⟩
  let ei : {x : QuaternionGroup 2 // x ^ 2 = 1} ≃
      {x : DihedralGroup 4 // x ^ 2 = 1} :=
    { toFun := fun x => ⟨e x, by rw [← map_pow, x.2, map_one]⟩
      invFun := fun x => ⟨e.symm x, by rw [← map_pow, x.2, map_one]⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x) }
  have hcard := Fintype.card_congr ei
  rw [apm_b93J01_card_Q8_sq_eq_one, apm_b93J01_card_D4_sq_eq_one] at hcard
  omega

/-- Consequently `Q₈` cannot be isomorphic to any commutative group. -/
lemma apm_b93J01_Q8_not_mulEquiv_commutative
    (A : Type*) [CommGroup A] :
    ¬Nonempty (QuaternionGroup 2 ≃* A) := by
  rintro ⟨e⟩
  apply apm_b93J01_Q8_not_commutative
  apply e.injective
  simp only [map_mul]
  exact mul_comm _ _

lemma apm_b93J01_Q8_not_equiv_ZMod8 :
    ¬Nonempty (QuaternionGroup 2 ≃* Multiplicative (ZMod 8)) :=
  apm_b93J01_Q8_not_mulEquiv_commutative _

lemma apm_b93J01_Q8_not_equiv_ZMod4_prod_ZMod2 :
    ¬Nonempty (QuaternionGroup 2 ≃* Multiplicative (ZMod 4 × ZMod 2)) :=
  apm_b93J01_Q8_not_mulEquiv_commutative _

/-- A normal subgroup of `Aₙ` containing a three-cycle is all of `Aₙ`.
This isolates the already available normal-closure half of the general
simplicity argument from the missing minimal-support argument. -/
lemma apm_b93J01_alternating_eq_top_of_mem_threeCycle
    {n : ℕ} (h5 : 5 ≤ n) (H : Subgroup (alternatingGroup (Fin n)))
    (hH : H.Normal) {g : alternatingGroup (Fin n)} (hg : g ∈ H)
    (h3 : Equiv.Perm.IsThreeCycle (g : Equiv.Perm (Fin n))) :
    H = ⊤ := by
  rw [eq_top_iff, ← h3.alternating_normalClosure (by simpa using h5)]
  apply Subgroup.normalClosure_le_normal
  simpa [Set.singleton_subset_iff] using hg

/-- A nontrivial subgroup of a finite alternating group contains a
nonidentity element whose support is minimal among its nonidentity elements. -/
lemma apm_b93J01_alternating_exists_minimalSupport
    {n : ℕ} (H : Subgroup (alternatingGroup (Fin n))) (hne : H ≠ ⊥) :
    ∃ g : alternatingGroup (Fin n), g ∈ H ∧ g ≠ 1 ∧
      ∀ x : alternatingGroup (Fin n), x ∈ H → x ≠ 1 →
        (g : Equiv.Perm (Fin n)).support.card ≤
          (x : Equiv.Perm (Fin n)).support.card := by
  let S : Set (alternatingGroup (Fin n)) := {g | g ∈ H ∧ g ≠ 1}
  have hS : S.Nonempty := by
    by_contra hs
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    by_contra hg1
    exact hs ⟨g, hg, hg1⟩
  obtain ⟨g, ⟨hg, hg1⟩, hmin⟩ := Set.exists_min_image S
    (fun g : alternatingGroup (Fin n) =>
      (g : Equiv.Perm (Fin n)).support.card) (Set.toFinite S) hS
  exact ⟨g, hg, hg1, fun x hx hx1 => hmin x ⟨hx, hx1⟩⟩

/-- The commutator with an ambient alternating permutation stays in a normal
subgroup.  This is the element to which minimal-support descent is applied. -/
lemma apm_b93J01_alternating_commutator_mem
    {n : ℕ} (H : Subgroup (alternatingGroup (Fin n))) (hH : H.Normal)
    {g : alternatingGroup (Fin n)} (hg : g ∈ H)
    (τ : alternatingGroup (Fin n)) : τ * g * τ⁻¹ * g⁻¹ ∈ H := by
  exact H.mul_mem (hH.conj_mem g hg τ) (H.inv_mem hg)

/-- A concrete three-cycle on three distinct points, regarded as an element
of the alternating group. -/
def apm_b93J01_threeCycle
    {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    alternatingGroup (Fin n) :=
  ⟨Equiv.swap a b * Equiv.swap a c,
    (Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc).mem_alternatingGroup⟩

lemma apm_b93J01_threeCycle_isThreeCycle
    {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Equiv.Perm.IsThreeCycle
      (apm_b93J01_threeCycle a b c hab hac hbc : Equiv.Perm (Fin n)) :=
  Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc

/-- Commuting an arbitrary permutation with a three-cycle moves at most six
points: the support lies in the cycle's support and its conjugate. -/
lemma apm_b93J01_card_support_commutator_threeCycle_le_six
    {α : Type*} [Fintype α] [DecidableEq α]
    (τ g : Equiv.Perm α) (hτ : Equiv.Perm.IsThreeCycle τ) :
    (τ * g * τ⁻¹ * g⁻¹).support.card ≤ 6 := by
  have hs : (τ * g * τ⁻¹ * g⁻¹).support ≤
      τ.support ∪ (g * τ⁻¹ * g⁻¹).support := by
    simpa [mul_assoc] using Equiv.Perm.support_mul_le τ (g * τ⁻¹ * g⁻¹)
  calc
    (τ * g * τ⁻¹ * g⁻¹).support.card ≤
        (τ.support ∪ (g * τ⁻¹ * g⁻¹).support).card := Finset.card_le_card hs
    _ ≤ τ.support.card + (g * τ⁻¹ * g⁻¹).support.card :=
      Finset.card_union_le _ _
    _ = 6 := by rw [Equiv.Perm.card_support_conj, Equiv.Perm.support_inv,
      hτ.card_support]

/-- If a permutation carries two successive points `a ↦ b ↦ c` and a
point `d ↦ e` outside that orbit segment, the three-cycle on `a,b,d` has
a nontrivial commutator supported on at most those five points. -/
lemma apm_b93J01_cross_threeCycle_commutator
    {α : Type*} [Fintype α] [DecidableEq α]
    (g : Equiv.Perm α) (a b c d e : α)
    (hn : List.Nodup [a, b, c, d, e])
    (ha : g a = b) (hb : g b = c) (hd : g d = e) :
    let τ := Equiv.swap a b * Equiv.swap a d
    τ * g * τ⁻¹ * g⁻¹ ≠ 1 ∧
      (τ * g * τ⁻¹ * g⁻¹).support.card ≤ 5 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.nodup_nil] at hn
  push_neg at hn
  rcases hn with ⟨⟨hab, hac, had, hae, _⟩, ⟨hbc, hbd, hbe, _⟩,
    ⟨hcd, hce, _⟩, ⟨hde, _⟩, _, _⟩
  let τ : Equiv.Perm α := Equiv.swap a b * Equiv.swap a d
  have hτ : Equiv.Perm.IsThreeCycle τ :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab had hbd
  have hτa : τ a = d := by
    simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm
  have hτb : τ b = a := by
    simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hab.symm hbd,
      Equiv.swap_apply_right]
  have hτd : τ d = b := by
    simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.swap_apply_right, Equiv.swap_apply_left]
  have hne : τ * g * τ⁻¹ * g⁻¹ ≠ 1 := by
    intro hcomm
    have hc : τ * g = g * τ := by
      calc
        τ * g = (τ * g * τ⁻¹ * g⁻¹) * (g * τ) := by group
        _ = g * τ := by rw [hcomm, one_mul]
    have hp := DFunLike.congr_fun hc a
    simp only [Equiv.Perm.coe_mul, Function.comp_apply] at hp
    rw [ha, hτb, hτa, hd] at hp
    exact hae hp
  have hsa : a ∈ τ.support := by
    rw [Equiv.Perm.mem_support, hτa]
    exact had.symm
  have hsτ : τ.support = {a, d, b} := by
    simpa [hτa, hτd] using hτ.support_eq_iff_mem_support.mpr hsa
  have hs : (τ * g * τ⁻¹ * g⁻¹).support ⊆
      τ.support ∪ (g * τ⁻¹ * g⁻¹).support := by
    simpa [mul_assoc] using Equiv.Perm.support_mul_le τ (g * τ⁻¹ * g⁻¹)
  refine ⟨hne, (Finset.card_le_card hs).trans ?_⟩
  rw [Equiv.Perm.support_conj, Equiv.Perm.support_inv, hsτ]
  simp only [Finset.map_insert, Finset.map_singleton, Equiv.toEmbedding_apply,
    ha, hb, hd]
  have hsub : ({a, d, b} ∪ {b, e, c} : Finset α) ⊆ {a, b, c, d, e} := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    aesop
  exact (Finset.card_le_card hsub).trans (by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
      Finset.card_insert_of_notMem (by simp [hcd, hce]),
      Finset.card_insert_of_notMem (by simp [hde])]
    simp)

/-- A nontrivial commutator with a three-cycle bounds the support of a
minimal-support normal-subgroup element by six. -/
lemma apm_b93J01_minimalSupport_card_le_six_of_commutator_ne_one
    {n : ℕ} (H : Subgroup (alternatingGroup (Fin n))) (hH : H.Normal)
    (g : alternatingGroup (Fin n)) (hg : g ∈ H)
    (hgmin : ∀ x : alternatingGroup (Fin n), x ∈ H → x ≠ 1 →
      (g : Equiv.Perm (Fin n)).support.card ≤
        (x : Equiv.Perm (Fin n)).support.card)
    (τ : alternatingGroup (Fin n))
    (hτ : Equiv.Perm.IsThreeCycle (τ : Equiv.Perm (Fin n)))
    (hc : τ * g * τ⁻¹ * g⁻¹ ≠ 1) :
    (g : Equiv.Perm (Fin n)).support.card ≤ 6 := by
  refine (hgmin (τ * g * τ⁻¹ * g⁻¹)
    (apm_b93J01_alternating_commutator_mem H hH hg τ) hc).trans ?_
  simpa using apm_b93J01_card_support_commutator_threeCycle_le_six
    (τ : Equiv.Perm (Fin n)) (g : Equiv.Perm (Fin n)) hτ

/-- Every nonidentity element of `Aₙ`, for `n ≥ 5`, fails to commute with
some three-cycle.  Otherwise the generating set of three-cycles would put it
in the (trivial) center. -/
lemma apm_b93J01_exists_threeCycle_commutator_ne_one
    {n : ℕ} (h5 : 5 ≤ n) (g : alternatingGroup (Fin n)) (hg1 : g ≠ 1) :
    ∃ τ : alternatingGroup (Fin n),
      Equiv.Perm.IsThreeCycle (τ : Equiv.Perm (Fin n)) ∧
      τ * g * τ⁻¹ * g⁻¹ ≠ 1 := by
  by_contra hex
  push_neg at hex
  have hcomm : ∀ τ : alternatingGroup (Fin n),
      Equiv.Perm.IsThreeCycle (τ : Equiv.Perm (Fin n)) → τ * g = g * τ := by
    intro τ hτ
    rw [← commutatorElement_eq_one_iff_mul_comm]
    simpa [commutatorElement_def] using hex τ hτ
  have hgcenter : g ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro x
    let S : Set (alternatingGroup (Fin n)) :=
      {τ | Equiv.Perm.IsThreeCycle (τ : Equiv.Perm (Fin n))}
    have hx : x ∈ Subgroup.closure S := by
      rw [alternatingGroup.closure_isThreeCycles_eq_top]
      trivial
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({g} : Set _) := by
      rw [Subgroup.closure_le]
      intro τ hτ
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact (hcomm τ hτ).symm
    have hxcentral := Subgroup.mem_centralizer_iff.mp (hle hx) g (Set.mem_singleton g)
    exact hxcentral.symm
  have hgbot : g ∈ (⊥ : Subgroup (alternatingGroup (Fin n))) := by
    rw [← alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega))]
    exact hgcenter
  exact hg1 (by simpa using hgbot)

/-- Consequently every minimal-support nonidentity element of a normal
subgroup of `Aₙ` has support cardinality at most six. -/
lemma apm_b93J01_minimalSupport_card_le_six
    {n : ℕ} (h5 : 5 ≤ n)
    (H : Subgroup (alternatingGroup (Fin n))) (hH : H.Normal)
    (g : alternatingGroup (Fin n)) (hg : g ∈ H) (hg1 : g ≠ 1)
    (hgmin : ∀ x : alternatingGroup (Fin n), x ∈ H → x ≠ 1 →
      (g : Equiv.Perm (Fin n)).support.card ≤
        (x : Equiv.Perm (Fin n)).support.card) :
    (g : Equiv.Perm (Fin n)).support.card ≤ 6 := by
  obtain ⟨τ, hτ, hc⟩ := apm_b93J01_exists_threeCycle_commutator_ne_one h5 g hg1
  exact apm_b93J01_minimalSupport_card_le_six_of_commutator_ne_one
    H hH g hg hgmin τ hτ hc

lemma apm_b93J01_alternating_card_support_ne_two
    {n : ℕ} (g : alternatingGroup (Fin n)) :
    (g : Equiv.Perm (Fin n)).support.card ≠ 2 := by
  intro hcard
  have hswap : Equiv.Perm.IsSwap (g : Equiv.Perm (Fin n)) :=
    Equiv.Perm.card_support_eq_two.mp hcard
  have hone := Equiv.Perm.mem_alternatingGroup.mp g.property
  rw [hswap.sign_eq] at hone
  norm_num at hone

/-- The broad commutator bound reduces the minimal-support theorem to the
four small support cardinalities `3`, `4`, `5`, and `6`. -/
lemma apm_b93J01_minimalSupport_card_cases
    {n : ℕ} (h5 : 5 ≤ n)
    (H : Subgroup (alternatingGroup (Fin n))) (hH : H.Normal)
    (g : alternatingGroup (Fin n)) (hg : g ∈ H) (hg1 : g ≠ 1)
    (hgmin : ∀ x : alternatingGroup (Fin n), x ∈ H → x ≠ 1 →
      (g : Equiv.Perm (Fin n)).support.card ≤
        (x : Equiv.Perm (Fin n)).support.card) :
    (g : Equiv.Perm (Fin n)).support.card = 3 ∨
    (g : Equiv.Perm (Fin n)).support.card = 4 ∨
    (g : Equiv.Perm (Fin n)).support.card = 5 ∨
    (g : Equiv.Perm (Fin n)).support.card = 6 := by
  have hlo : 2 ≤ (g : Equiv.Perm (Fin n)).support.card :=
    Equiv.Perm.two_le_card_support_of_ne_one (by
      simpa only [Ne, Subtype.ext_iff, Subgroup.coe_one] using hg1)
  have hhi := apm_b93J01_minimalSupport_card_le_six h5 H hH g hg hg1 hgmin
  have hne := apm_b93J01_alternating_card_support_ne_two g
  omega

/-- An alternating permutation moving exactly four points is a product of
two disjoint transpositions. -/
lemma apm_b93J01_cycleType_eq_two_two_of_card_support_four
    {n : ℕ} (g : alternatingGroup (Fin n))
    (hcard : (g : Equiv.Perm (Fin n)).support.card = 4) :
    (g : Equiv.Perm (Fin n)).cycleType = {2, 2} := by
  have hall : ∀ k ∈ (g : Equiv.Perm (Fin n)).cycleType, k = 2 := by
    intro k hk
    by_contra hk2
    have hkgt : 2 < k := lt_of_le_of_ne
      (Equiv.Perm.two_le_of_mem_cycleType hk) (Ne.symm hk2)
    obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem hk
    have hsum0 := Equiv.Perm.sum_cycleType (g : Equiv.Perm (Fin n))
    rw [hs, Multiset.sum_cons, hcard] at hsum0
    have hs0 : s = 0 := by
      by_contra hsne
      obtain ⟨m, hm⟩ := Multiset.exists_mem_of_ne_zero hsne
      have hm2 := Equiv.Perm.two_le_of_mem_cycleType (hs ▸ Multiset.mem_cons_of_mem hm)
      have hmle := Multiset.le_sum_of_mem hm
      omega
    have hsingle : (g : Equiv.Perm (Fin n)).cycleType = {k} := by
      rw [hs, hs0]
      rfl
    have hsum := Equiv.Perm.sum_cycleType (g : Equiv.Perm (Fin n))
    rw [hsingle, Multiset.sum_singleton, hcard] at hsum
    have hsign := Equiv.Perm.mem_alternatingGroup.mp g.property
    rw [Equiv.Perm.sign_of_cycleType, hsingle, Multiset.sum_singleton,
      Multiset.card_singleton, hsum] at hsign
    norm_num at hsign
  rw [← Multiset.eq_replicate_card] at hall
  have hc : Multiset.card (g : Equiv.Perm (Fin n)).cycleType = 2 := by
    have heq : Multiset.card (g : Equiv.Perm (Fin n)).cycleType * 2 = 4 := by
      calc
        _ = (Multiset.replicate
            (Multiset.card (g : Equiv.Perm (Fin n)).cycleType) 2).sum := by simp
        _ = (g : Equiv.Perm (Fin n)).cycleType.sum := by rw [← hall]
        _ = (g : Equiv.Perm (Fin n)).support.card :=
          Equiv.Perm.sum_cycleType _
        _ = 4 := hcard
    omega
  rw [hc] at hall
  simpa using hall

lemma apm_b93J01_two_mul_card_le_sum_of_two_le
    (s : Multiset ℕ) (hs : ∀ k ∈ s, 2 ≤ k) : 2 * s.card ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      simp only [Multiset.mem_cons, forall_eq_or_imp] at hs
      simp only [Multiset.card_cons, Multiset.sum_cons]
      have := ih hs.2
      omega

/-- An alternating permutation moving exactly five points is a 5-cycle. -/
lemma apm_b93J01_cycleType_eq_five_of_card_support_five
    {n : ℕ} (g : alternatingGroup (Fin n))
    (hcard : (g : Equiv.Perm (Fin n)).support.card = 5) :
    (g : Equiv.Perm (Fin n)).cycleType = {5} := by
  let σ : Equiv.Perm (Fin n) := g
  have hsum : σ.cycleType.sum = 5 := (Equiv.Perm.sum_cycleType σ).trans hcard
  have hbound : 2 * σ.cycleType.card ≤ σ.cycleType.sum :=
    apm_b93J01_two_mul_card_le_sum_of_two_le σ.cycleType
      (fun _ hk => Equiv.Perm.two_le_of_mem_cycleType hk)
  have hpos : 0 < σ.cycleType.card := Equiv.Perm.card_cycleType_pos.2 (by
    intro hσ
    have : σ.support.card = 0 := Equiv.Perm.card_support_eq_zero.mpr hσ
    change (g : Equiv.Perm (Fin n)).support.card = 0 at this
    omega)
  have hsign := Equiv.Perm.mem_alternatingGroup.mp g.property
  have heven : Even (5 + σ.cycleType.card) := by
    rw [Equiv.Perm.sign_of_cycleType, hsum,
      neg_one_pow_eq_one_iff_even (by decide)] at hsign
    exact hsign
  have hc : σ.cycleType.card = 1 := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hcycle : Equiv.Perm.IsCycle σ := Equiv.Perm.card_cycleType_eq_one.mp hc
  simpa [σ, hcard] using hcycle.cycleType

/-- An alternating permutation moving exactly six points has cycle type
`(2,4)` or `(3,3)` (up to the order of the multiset entries). -/
lemma apm_b93J01_cycleType_of_card_support_six
    {n : ℕ} (g : alternatingGroup (Fin n))
    (hcard : (g : Equiv.Perm (Fin n)).support.card = 6) :
    (g : Equiv.Perm (Fin n)).cycleType = {2, 4} ∨
    (g : Equiv.Perm (Fin n)).cycleType = {3, 3} ∨
    (g : Equiv.Perm (Fin n)).cycleType = {4, 2} := by
  let σ : Equiv.Perm (Fin n) := g
  have hsum : σ.cycleType.sum = 6 := (Equiv.Perm.sum_cycleType σ).trans hcard
  have hbound : 2 * σ.cycleType.card ≤ σ.cycleType.sum :=
    apm_b93J01_two_mul_card_le_sum_of_two_le σ.cycleType
      (fun _ hk => Equiv.Perm.two_le_of_mem_cycleType hk)
  have hpos : 0 < σ.cycleType.card := Equiv.Perm.card_cycleType_pos.2 (by
    intro hσ
    have hz : σ.support.card = 0 := Equiv.Perm.card_support_eq_zero.mpr hσ
    change (g : Equiv.Perm (Fin n)).support.card = 0 at hz
    omega)
  have hsign := Equiv.Perm.mem_alternatingGroup.mp g.property
  have heven : Even (6 + σ.cycleType.card) := by
    rw [Equiv.Perm.sign_of_cycleType, hsum,
      neg_one_pow_eq_one_iff_even (by decide)] at hsign
    exact hsign
  have hc : σ.cycleType.card = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hc
  have ha2 : 2 ≤ a := Equiv.Perm.two_le_of_mem_cycleType (by rw [hab]; simp)
  have hb2 : 2 ≤ b := Equiv.Perm.two_le_of_mem_cycleType (by rw [hab]; simp)
  have habsum : a + b = 6 := by simpa [hab] using hsum
  rcases (show (a = 2 ∧ b = 4) ∨ (a = 3 ∧ b = 3) ∨
      (a = 4 ∧ b = 2) by omega) with h | h | h
  · left; simp [σ, hab, h.1, h.2]
  · right; left; simp [σ, hab, h.1, h.2]
  · right; right; simp [σ, hab, h.1, h.2]

/-- Squaring a permutation of cycle type `(2,4)` leaves the square of its
4-cycle, hence moves exactly four points. -/
lemma apm_b93J01_card_support_sq_of_cycleType_two_four
    {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α)
    (hgtype : g.cycleType = {2, 4}) : (g ^ 2).support.card = 4 := by
  have h2mem : 2 ∈ g.cycleType := by rw [hgtype]; simp
  obtain ⟨c, t, hgt, hdis, hc, hccard⟩ :=
    Equiv.Perm.mem_cycleType_iff.mp h2mem
  have hctype : c.cycleType = {2} := by simpa [hccard] using hc.cycleType
  have httype : t.cycleType = {4} := by
    have heq := congrArg Equiv.Perm.cycleType hgt
    rw [hdis.cycleType_mul, hctype, hgtype] at heq
    simpa using heq.symm
  have ht : Equiv.Perm.IsCycle t := by
    rw [← Equiv.Perm.card_cycleType_eq_one, httype]
    simp
  have htcard : t.support.card = 4 := by
    rw [← Equiv.Perm.sum_cycleType, httype]
    simp
  have hc2 : c ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hc.orderOf, hccard]
  have hcc : c * c = 1 := by simpa [pow_two] using hc2
  have hg2 : g ^ 2 = t ^ 2 := by
    rw [hgt]
    simp only [pow_two]
    calc
      c * t * (c * t) = c * (t * c) * t := by group
      _ = c * (c * t) * t := by rw [hdis.commute.eq.symm]
      _ = (c * c) * (t * t) := by group
      _ = t * t := by rw [hcc, one_mul]
  rw [hg2, ht.support_pow_of_pos_of_lt_orderOf (by decide) (by
    rw [ht.orderOf, htcard]
    decide), htcard]

/-- A minimal-support element moving six points cannot have cycle type
`(2,4)`: its square is a nonidentity element of the same normal subgroup
moving only four points. -/
lemma apm_b93J01_minimalSupport_cycleType_ne_two_four
    {n : ℕ} (H : Subgroup (alternatingGroup (Fin n)))
    (g : alternatingGroup (Fin n)) (hg : g ∈ H)
    (hgmin : ∀ x : alternatingGroup (Fin n), x ∈ H → x ≠ 1 →
      (g : Equiv.Perm (Fin n)).support.card ≤
        (x : Equiv.Perm (Fin n)).support.card)
    (hcard : (g : Equiv.Perm (Fin n)).support.card = 6)
    (hgtype : (g : Equiv.Perm (Fin n)).cycleType = {2, 4}) : False := by
  have hsquare : ((g ^ 2 : alternatingGroup (Fin n)) :
      Equiv.Perm (Fin n)).support.card = 4 :=
    apm_b93J01_card_support_sq_of_cycleType_two_four _ hgtype
  have hg2mem : g ^ 2 ∈ H := H.pow_mem hg 2
  have hg2ne : g ^ 2 ≠ 1 := by
    intro heq
    have hs0 : ((g ^ 2 : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)).support.card = 0 := by
      rw [heq]
      simp
    omega
  have hle := hgmin (g ^ 2) hg2mem hg2ne
  rw [hcard, hsquare] at hle
  omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
/-- The swap calculation behind the 5-cycle descent commutator. -/
lemma apm_b93J01_swap_commutator_identity
    {α : Type*} [DecidableEq α] {a b c d : α}
    (h : List.Nodup [a, b, c, d]) :
    Equiv.swap a b * Equiv.swap a c * Equiv.swap b d * Equiv.swap b c =
      Equiv.swap a d * Equiv.swap a c := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.nodup_nil] at h
  push_neg at h
  rcases h with ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd, _, _⟩
  ext x
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def]
  split_ifs <;> grind

/-- If four successive images of a point are distinct, commuting with the
three-cycle on the first three gives an explicit three-cycle. -/
lemma apm_b93J01_commutator_threeCycle_of_orbit_four
    {α : Type*} [Fintype α] [DecidableEq α]
    (g : Equiv.Perm α) (a b c d : α)
    (habcd : List.Nodup [a, b, c, d])
    (ha : g a = b) (hb : g b = c) (hc : g c = d) :
    Equiv.Perm.IsThreeCycle
      ((Equiv.swap a b * Equiv.swap a c) * g *
        (Equiv.swap a b * Equiv.swap a c)⁻¹ * g⁻¹) := by
  have heq : (Equiv.swap a b * Equiv.swap a c) * g *
        (Equiv.swap a b * Equiv.swap a c)⁻¹ * g⁻¹ =
      Equiv.swap a d * Equiv.swap a c := by
    rw [mul_inv_rev]
    simp only [Equiv.swap_inv]
    rw [show (Equiv.swap a b * Equiv.swap a c) * g *
          (Equiv.swap a c * Equiv.swap a b) * g⁻¹ =
        (Equiv.swap a b * Equiv.swap a c) *
          (g * (Equiv.swap a c * Equiv.swap a b) * g⁻¹) by group]
    rw [show g * (Equiv.swap a c * Equiv.swap a b) * g⁻¹ =
        (g * Equiv.swap a c * g⁻¹) * (g * Equiv.swap a b * g⁻¹) by group]
    rw [← Equiv.swap_apply_apply, ← Equiv.swap_apply_apply, ha, hb, hc]
    exact apm_b93J01_swap_commutator_identity habcd
  rw [heq]
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.nodup_nil] at habcd
  push_neg at habcd
  rcases habcd with ⟨⟨_, hac, had⟩, _, hcd, _, _⟩
  apply Equiv.Perm.isThreeCycle_swap_mul_swap_same
  · exact had.1
  · exact hac
  · exact hcd.1.symm

/-- A 5-cycle admits a three-cycle whose commutator with it is itself a
three-cycle. -/
lemma apm_b93J01_exists_threeCycle_commutator_isThreeCycle_of_cycleType_five
    {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α)
    (hg : g.cycleType = {5}) :
    ∃ τ : Equiv.Perm α, Equiv.Perm.IsThreeCycle τ ∧
      Equiv.Perm.IsThreeCycle (τ * g * τ⁻¹ * g⁻¹) := by
  have hcycle : Equiv.Perm.IsCycle g := by
    rw [← Equiv.Perm.card_cycleType_eq_one, hg]
    simp
  have hcard : g.support.card = 5 := by
    rw [← Equiv.Perm.sum_cycleType, hg]
    simp
  obtain ⟨a, ha⟩ := hcycle.nonempty_support
  have hcycleOn : g.IsCycleOn g.support := by
    convert hcycle.isCycleOn using 1
    ext x
    simp [Equiv.Perm.mem_support]
  have hp {i j : ℕ} (hij : ¬i ≡ j [MOD 5]) : (g ^ i) a ≠ (g ^ j) a := by
    intro heq
    apply hij
    have := hcycleOn.pow_apply_eq_pow_apply ha |>.mp heq
    rwa [hcard] at this
  have h01 := hp (by decide : ¬0 ≡ 1 [MOD 5])
  have h02 := hp (by decide : ¬0 ≡ 2 [MOD 5])
  have h03 := hp (by decide : ¬0 ≡ 3 [MOD 5])
  have h12 := hp (by decide : ¬1 ≡ 2 [MOD 5])
  have h13 := hp (by decide : ¬1 ≡ 3 [MOD 5])
  have h23 := hp (by decide : ¬2 ≡ 3 [MOD 5])
  have h01' : a ≠ g a := by simpa using h01
  have h02' : a ≠ g (g a) := by simpa [pow_succ] using h02
  have h03' : a ≠ g (g (g a)) := by simpa [pow_succ] using h03
  have h12' : g a ≠ g (g a) := by simpa [pow_succ] using h12
  have h13' : g a ≠ g (g (g a)) := by simpa [pow_succ] using h13
  have h23' : g (g a) ≠ g (g (g a)) := by simpa [pow_succ] using h23
  let b := g a
  let c := g b
  let d := g c
  have habcd : List.Nodup [a, b, c, d] := by
    simp [b, c, d, h01', h02', h03', h12', h13', h23']
  have hab : a ≠ b := by
    simpa [b] using h01
  have hac : a ≠ c := by
    simpa [b, c, pow_succ] using h02
  have hbc : b ≠ c := by
    simpa [b, c, pow_succ] using h12
  let τ := Equiv.swap a b * Equiv.swap a c
  refine ⟨τ, Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc, ?_⟩
  exact apm_b93J01_commutator_threeCycle_of_orbit_four g a b c d habcd rfl rfl rfl

/-- From degree six onward, a normal subgroup containing an alternating
permutation of support four is the whole alternating group. -/
lemma apm_b93J01_normal_eq_top_of_card_support_four
    {n : ℕ} (h6 : 6 ≤ n)
    (H : Subgroup (alternatingGroup (Fin n))) (hH : H.Normal)
    {g : alternatingGroup (Fin n)} (hg : g ∈ H)
    (hcard : (g : Equiv.Perm (Fin n)).support.card = 4) :
    H = ⊤ := by
  have hgtype := apm_b93J01_cycleType_eq_two_two_of_card_support_four g hcard
  rw [eq_top_iff, ← alternatingGroup.closure_cycleType_eq_two_two_eq_top
    (by simpa using (show 5 ≤ n by omega)), Subgroup.closure_le]
  intro τ hτ
  have hτcard : (τ : Equiv.Perm (Fin n)).support.card = 4 := by
    rw [← Equiv.Perm.sum_cycleType, hτ]
    norm_num
  have hcperm : IsConj (τ : Equiv.Perm (Fin n))
      (g : Equiv.Perm (Fin n)) :=
    Equiv.Perm.isConj_iff_cycleType_eq.2 (hτ.trans hgtype.symm)
  have hc : IsConj τ g := alternatingGroup.isConj_of hcperm (by
    rw [hτcard]
    simpa using h6)
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have hmem := hH.conj_mem g hg c⁻¹
  convert hmem using 1
  rw [← hc]
  group

lemma apm_b93J01_minimalSupport_card_ne_four
    {n : ℕ} (h6 : 6 ≤ n)
    (H : Subgroup (alternatingGroup (Fin n))) (hH : H.Normal)
    (g : alternatingGroup (Fin n)) (hg : g ∈ H) (hg1 : g ≠ 1)
    (hgmin : ∀ x : alternatingGroup (Fin n), x ∈ H → x ≠ 1 →
      (g : Equiv.Perm (Fin n)).support.card ≤
        (x : Equiv.Perm (Fin n)).support.card) :
    (g : Equiv.Perm (Fin n)).support.card ≠ 4 := by
  intro hcard
  have htop := apm_b93J01_normal_eq_top_of_card_support_four h6 H hH hg hcard
  obtain ⟨τ, hτ, _⟩ := apm_b93J01_exists_threeCycle_commutator_ne_one
    (show 5 ≤ n by omega) g hg1
  have hτH : τ ∈ H := by rw [htop]; trivial
  have hle := hgmin τ hτH (by
    intro hτ1
    apply hτ.isCycle.ne_one
    simpa only [Subtype.ext_iff, Subgroup.coe_one] using hτ1)
  rw [hcard, hτ.card_support] at hle
  omega

lemma apm_b93J01_minimalSupport_card_ne_five
    {n : ℕ} (H : Subgroup (alternatingGroup (Fin n))) (hH : H.Normal)
    (g : alternatingGroup (Fin n)) (hg : g ∈ H)
    (hgmin : ∀ x : alternatingGroup (Fin n), x ∈ H → x ≠ 1 →
      (g : Equiv.Perm (Fin n)).support.card ≤
        (x : Equiv.Perm (Fin n)).support.card) :
    (g : Equiv.Perm (Fin n)).support.card ≠ 5 := by
  intro hcard
  have hgtype := apm_b93J01_cycleType_eq_five_of_card_support_five g hcard
  obtain ⟨τ, hτ, hcomm⟩ :=
    apm_b93J01_exists_threeCycle_commutator_isThreeCycle_of_cycleType_five
      (g : Equiv.Perm (Fin n)) hgtype
  let τA : alternatingGroup (Fin n) := ⟨τ, hτ.mem_alternatingGroup⟩
  let cA : alternatingGroup (Fin n) := τA * g * τA⁻¹ * g⁻¹
  have hcH : cA ∈ H := apm_b93J01_alternating_commutator_mem H hH hg τA
  have hc3 : Equiv.Perm.IsThreeCycle (cA : Equiv.Perm (Fin n)) := by
    simpa [cA, τA] using hcomm
  have hc1 : cA ≠ 1 := by
    intro hc
    apply hc3.isCycle.ne_one
    simpa only [Subtype.ext_iff, Subgroup.coe_one] using hc
  have hle := hgmin cA hcH hc1
  rw [hcard, hc3.card_support] at hle
  omega

/-- After the double-transposition case is removed, a minimal-support
counterexample in degree at least six can only move three, five, or six
points. -/
lemma apm_b93J01_minimalSupport_card_cases_reduced
    {n : ℕ} (h6 : 6 ≤ n)
    (H : Subgroup (alternatingGroup (Fin n))) (hH : H.Normal)
    (g : alternatingGroup (Fin n)) (hg : g ∈ H) (hg1 : g ≠ 1)
    (hgmin : ∀ x : alternatingGroup (Fin n), x ∈ H → x ≠ 1 →
      (g : Equiv.Perm (Fin n)).support.card ≤
        (x : Equiv.Perm (Fin n)).support.card) :
    (g : Equiv.Perm (Fin n)).support.card = 3 ∨
    (g : Equiv.Perm (Fin n)).support.card = 5 ∨
    (g : Equiv.Perm (Fin n)).support.card = 6 := by
  rcases apm_b93J01_minimalSupport_card_cases (show 5 ≤ n by omega)
    H hH g hg hg1 hgmin with h3 | h4 | h5 | h6'
  · exact Or.inl h3
  · exact (apm_b93J01_minimalSupport_card_ne_four h6 H hH g hg hg1 hgmin h4).elim
  · exact Or.inr (Or.inl h5)
  · exact Or.inr (Or.inr h6')

/-- The 5-cycle commutator removes support five, leaving only the desired
support three and the final support-six case. -/
lemma apm_b93J01_minimalSupport_card_three_or_six
    {n : ℕ} (h6 : 6 ≤ n)
    (H : Subgroup (alternatingGroup (Fin n))) (hH : H.Normal)
    (g : alternatingGroup (Fin n)) (hg : g ∈ H) (hg1 : g ≠ 1)
    (hgmin : ∀ x : alternatingGroup (Fin n), x ∈ H → x ≠ 1 →
      (g : Equiv.Perm (Fin n)).support.card ≤
        (x : Equiv.Perm (Fin n)).support.card) :
    (g : Equiv.Perm (Fin n)).support.card = 3 ∨
    (g : Equiv.Perm (Fin n)).support.card = 6 := by
  rcases apm_b93J01_minimalSupport_card_cases_reduced h6 H hH g hg hg1 hgmin with
    h3 | h5 | h6'
  · exact Or.inl h3
  · exact (apm_b93J01_minimalSupport_card_ne_five H hH g hg hgmin h5).elim
  · exact Or.inr h6'

/-- In the remaining support-six branch, squaring excludes the `(2,4)`
cycle type, so the element is a product of two disjoint three-cycles. -/
lemma apm_b93J01_minimalSupport_cycleType_three_three_of_card_six
    {n : ℕ} (H : Subgroup (alternatingGroup (Fin n)))
    (g : alternatingGroup (Fin n)) (hg : g ∈ H)
    (hgmin : ∀ x : alternatingGroup (Fin n), x ∈ H → x ≠ 1 →
      (g : Equiv.Perm (Fin n)).support.card ≤
        (x : Equiv.Perm (Fin n)).support.card)
    (hcard : (g : Equiv.Perm (Fin n)).support.card = 6) :
    (g : Equiv.Perm (Fin n)).cycleType = {3, 3} := by
  rcases apm_b93J01_cycleType_of_card_support_six
      g hcard with h24 | h33 | h42
  · exact (apm_b93J01_minimalSupport_cycleType_ne_two_four
      H g hg hgmin hcard h24).elim
  · exact h33
  · have h24 : (g : Equiv.Perm (Fin n)).cycleType = {2, 4} := by
      rw [show ({4, 2} : Multiset ℕ) = {2, 4} by decide] at h42
      exact h42
    exact (apm_b93J01_minimalSupport_cycleType_ne_two_four
      H g hg hgmin hcard h24).elim

/-- A product of two disjoint three-cycles admits a cross-cycle
three-cycle commutator moving at most five points, contradicting minimality
when the original element moves six. -/
lemma apm_b93J01_minimalSupport_card_ne_six
    {n : ℕ} (H : Subgroup (alternatingGroup (Fin n))) (hH : H.Normal)
    (g : alternatingGroup (Fin n)) (hg : g ∈ H)
    (hgmin : ∀ x : alternatingGroup (Fin n), x ∈ H → x ≠ 1 →
      (g : Equiv.Perm (Fin n)).support.card ≤
        (x : Equiv.Perm (Fin n)).support.card)
    (hcard : (g : Equiv.Perm (Fin n)).support.card = 6) : False := by
  have hgtype := apm_b93J01_minimalSupport_cycleType_three_three_of_card_six
    H g hg hgmin hcard
  have h3mem : 3 ∈ (g : Equiv.Perm (Fin n)).cycleType := by rw [hgtype]; simp
  obtain ⟨c, t, hgt, hdis, hc, hccard⟩ :=
    Equiv.Perm.mem_cycleType_iff.mp h3mem
  have hctype : c.cycleType = {3} := by simpa [hccard] using hc.cycleType
  have httype : t.cycleType = {3} := by
    have heq := congrArg Equiv.Perm.cycleType hgt
    rw [hdis.cycleType_mul, hctype, hgtype] at heq
    simpa using heq.symm
  have hc3 : Equiv.Perm.IsThreeCycle c := by
    rw [← card_support_eq_three_iff, ← Equiv.Perm.sum_cycleType, hctype]
    simp
  have ht3 : Equiv.Perm.IsThreeCycle t := by
    rw [← card_support_eq_three_iff, ← Equiv.Perm.sum_cycleType, httype]
    simp
  obtain ⟨a, ha⟩ := hc.nonempty_support
  obtain ⟨d, hd⟩ := ht3.isCycle.nonempty_support
  let b := c a
  let c' := c b
  let e := t d
  have hcnodup : [a, b, c'].Nodup := by
    simpa [b, c'] using hc3.nodup_iff_mem_support.mpr ha
  have hdne : d ≠ e := by
    have hd' : t d ≠ d := by simpa [Equiv.Perm.mem_support] using hd
    simpa [e] using hd'.symm
  have hdenodup : [d, e].Nodup := by simp [hdne]
  have hn : [a, b, c', d, e].Nodup := by
    rw [show [a, b, c', d, e] = [a, b, c'] ++ [d, e] by rfl,
      List.nodup_append]
    refine ⟨hcnodup, hdenodup, ?_⟩
    intro x hxc y hyt hxy
    subst y
    have hxc' : x ∈ c.support := by
      rw [hc3.support_eq_iff_mem_support.mpr ha]
      simpa [b, c'] using hxc
    have hxt' : x ∈ t.support := by
      simp at hyt
      rcases hyt with rfl | rfl
      · exact hd
      · exact t.apply_mem_support.2 hd
    exact (hdis.mem_imp hxc') hxt'
  have hta : t a = a := Equiv.Perm.notMem_support.mp (hdis.mem_imp ha)
  have htbmem : b ∈ c.support := c.apply_mem_support.2 ha
  have htb : t b = b := Equiv.Perm.notMem_support.mp (hdis.mem_imp htbmem)
  have htd : c d = d := Equiv.Perm.notMem_support.mp
    (hdis.symm.mem_imp hd)
  have hte_mem : e ∈ t.support := by
    exact t.apply_mem_support.2 hd
  have hte : c e = e := Equiv.Perm.notMem_support.mp
    (hdis.symm.mem_imp hte_mem)
  have hga : (g : Equiv.Perm (Fin n)) a = b := by
    rw [hgt]
    simp [b, hta]
  have hgb : (g : Equiv.Perm (Fin n)) b = c' := by
    rw [hgt]
    simp [c', htb]
  have hgd : (g : Equiv.Perm (Fin n)) d = e := by
    rw [hgt]
    simpa [e] using hte
  let τp : Equiv.Perm (Fin n) := Equiv.swap a b * Equiv.swap a d
  have hτp : Equiv.Perm.IsThreeCycle τp := by
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same
      (by grind) (by grind) (by grind)
  let τ : alternatingGroup (Fin n) := ⟨τp, hτp.mem_alternatingGroup⟩
  have hcross := apm_b93J01_cross_threeCycle_commutator
    (g : Equiv.Perm (Fin n)) a b c' d e hn hga hgb hgd
  change τp * (g : Equiv.Perm (Fin n)) * τp⁻¹ *
      (g : Equiv.Perm (Fin n))⁻¹ ≠ 1 ∧
    (τp * (g : Equiv.Perm (Fin n)) * τp⁻¹ *
      (g : Equiv.Perm (Fin n))⁻¹).support.card ≤ 5 at hcross
  have hτne : τ * g * τ⁻¹ * g⁻¹ ≠ 1 := by
    intro heq
    apply hcross.1
    exact Subtype.ext_iff.mp heq
  have hle := hgmin (τ * g * τ⁻¹ * g⁻¹)
    (apm_b93J01_alternating_commutator_mem H hH hg τ) hτne
  have hsle : ((τ * g * τ⁻¹ * g⁻¹ : alternatingGroup (Fin n)) :
      Equiv.Perm (Fin n)).support.card ≤ 5 := hcross.2
  rw [hcard] at hle
  omega

/-- Reduction of general simplicity of `Aₙ` to the classical assertion that
each nontrivial normal subgroup contains a three-cycle. -/
lemma apm_b93J01_alternating_isSimpleGroup_of_threeCycle
    {n : ℕ} (h5 : 5 ≤ n)
    (hthree : ∀ H : Subgroup (alternatingGroup (Fin n)), H.Normal → H ≠ ⊥ →
      ∃ g : alternatingGroup (Fin n), g ∈ H ∧
        Equiv.Perm.IsThreeCycle (g : Equiv.Perm (Fin n))) :
    IsSimpleGroup (alternatingGroup (Fin n)) := by
  haveI : Nontrivial (alternatingGroup (Fin n)) :=
    alternatingGroup.nontrivial_of_three_le_card (by
      simpa using (show 3 ≤ n by omega))
  refine ⟨fun H hH => or_not.imp id fun hne => ?_⟩
  obtain ⟨g, hg, h3⟩ := hthree H hH hne
  exact apm_b93J01_alternating_eq_top_of_mem_threeCycle h5 H hH hg h3

/-- It suffices to prove that a minimal-support nonidentity element of a
nontrivial normal subgroup of `Aₙ` is a three-cycle. -/
lemma apm_b93J01_alternating_isSimpleGroup_of_minimalSupport
    {n : ℕ} (h5 : 5 ≤ n)
    (hminimal : ∀ (H : Subgroup (alternatingGroup (Fin n))) (_hH : H.Normal)
      (g : alternatingGroup (Fin n)), g ∈ H → g ≠ 1 →
      (∀ x : alternatingGroup (Fin n), x ∈ H → x ≠ 1 →
        (g : Equiv.Perm (Fin n)).support.card ≤
          (x : Equiv.Perm (Fin n)).support.card) →
      Equiv.Perm.IsThreeCycle (g : Equiv.Perm (Fin n))) :
    IsSimpleGroup (alternatingGroup (Fin n)) := by
  apply apm_b93J01_alternating_isSimpleGroup_of_threeCycle h5
  intro H hH hne
  obtain ⟨g, hg, hg1, hgmin⟩ :=
    apm_b93J01_alternating_exists_minimalSupport H hne
  exact ⟨g, hg, hminimal H hH g hg hg1 hgmin⟩

/-- The degree-five boundary is already supplied by Mathlib, so proving the
result from degree six onward suffices for the frozen statement. -/
lemma apm_b93J01_alternating_simple_of_six_le
    (h : ∀ n : ℕ, 6 ≤ n → IsSimpleGroup (alternatingGroup (Fin n))) :
    ∀ n : ℕ, 5 ≤ n → IsSimpleGroup (alternatingGroup (Fin n)) := by
  intro n hn
  rcases hn.eq_or_lt with rfl | hn6
  · infer_instance
  · exact h n hn6

theorem apm_b93j01 :
    -- (a): `A₄` is a counterexample; `Aₙ` is simple for `n ≥ 5`.
    ¬IsSimpleGroup (alternatingGroup (Fin 4)) ∧
    (∀ n : ℕ, 5 ≤ n → IsSimpleGroup (alternatingGroup (Fin n))) ∧
    -- (b): `Q₈` is missing from the proposed list; there are five types.
    (Fintype.card (QuaternionGroup 2) = 8 ∧
      ¬Nonempty (QuaternionGroup 2 ≃* Multiplicative (ZMod 8)) ∧
      ¬Nonempty (QuaternionGroup 2 ≃* Multiplicative (ZMod 4 × ZMod 2)) ∧
      ¬Nonempty (QuaternionGroup 2 ≃* DihedralGroup 4)) ∧
    (∀ (G : Type) [Group G] [Fintype G], Fintype.card G = 8 →
      Nonempty (G ≃* Multiplicative (ZMod 8)) ∨
      Nonempty (G ≃* Multiplicative (ZMod 4 × ZMod 2)) ∨
      Nonempty (G ≃* Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)) ∨
      Nonempty (G ≃* DihedralGroup 4) ∨
      Nonempty (G ≃* QuaternionGroup 2)) ∧
    -- (c): `A₄` has no subgroup of order six; Lagrange is the correction.
    (Fintype.card (alternatingGroup (Fin 4)) = 12 ∧
      ¬∃ H : Subgroup (alternatingGroup (Fin 4)), Nat.card H = 6) ∧
    (∀ (G : Type) [Group G] [Fintype G] (H : Subgroup G),
      Nat.card H ∣ Fintype.card G) ∧
    -- (d): `ℚ` is not such a direct sum; finite abelian groups are.
    ¬apm_b93J01_IsDirectSumOfCyclic ℚ ∧
    (∀ (G : Type) [AddCommGroup G] [Fintype G],
      apm_b93J01_IsDirectSumOfCyclic G) ∧
    -- (e): `S₃` has order `2·3` but is not cyclic; add `p ∤ q-1`.
    (Fintype.card (Equiv.Perm (Fin 3)) = 2 * 3 ∧
      ¬IsCyclic (Equiv.Perm (Fin 3))) ∧
    (∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → p < q → (¬p ∣ (q - 1)) →
      ∀ (G : Type) [Group G] [Fintype G], Fintype.card G = p * q →
        IsCyclic G) := by
  /- CLOSER HOP 2 BOUNDARY (2026-08-08).

  The helpers above close the numerical order computations for `A₄`, `S₃`,
  and `Q₈`, the full Lagrange conjunct, and the noncyclicity of `S₃`. They use
  `card_alternatingGroup`, `Fintype.card_perm`, and
  `Subgroup.card_subgroup_dvd_card` directly. Going beyond hop 1, the original
  candidate artifact's explicit adjacent-transposition witness was recovered
  from git history and adapted to the current `IsCyclic.commutative` API;
  `QuaternionGroup.card` closes the first order-eight counterexample clause.

  The remaining frozen conjunction is a broad group-classification package.
  In this Mathlib snapshot `GroupTheory.SpecificGroups.Alternating` proves only
  `alternatingGroup.isSimpleGroup_five`; its module header explicitly lists
  general simplicity of alternating groups as future work.  No theorem
  classifies every group of order eight into the five displayed isomorphism
  types, nor packages the finite-abelian direct-sum decomposition in the
  custom `iSupIndep` encoding. The assertions that `A₄` has no subgroup of
  order six, `ℚ` is not such a direct sum, the three `Q₈` non-isomorphisms,
  and the corrected order-`pq` cyclicity theorem still require substantial
  separate developments.
  Searches of `LEMMA-INDEX.md`, `ConstructionTargets`, solved group-theory
  siblings, Mathlib sources, and git history found no combined or reusable
  closure.  The frozen statement is unchanged.

  CLOSER HOP 3 (2026-08-08): two of the three quaternion
  non-isomorphisms are now compiled. `apm_b93J01_Q8_not_commutative` uses the
  concrete generators `a 1` and `xa 0`; their unequal products normalize by
  ordinary `decide`. `apm_b93J01_Q8_not_mulEquiv_commutative` transports
  commutativity backward through a hypothetical multiplicative equivalence,
  and its two specializations rule out `ZMod 8` and `ZMod 4 × ZMod 2` exactly
  as they occur in the frozen theorem. The dihedral target is itself
  noncommutative, so this invariant cannot settle the third clause; searches
  of exponent, element-order, center, and quaternion/dihedral APIs found no
  packaged separating invariant. The broader alternating-group, order-eight
  classification, direct-sum, and order-`pq` bridges also remain. The frozen
  statement is unchanged.

  HOP 4 closes that specific hole. The finite computations
  `apm_b93J01_card_Q8_sq_eq_one` and `apm_b93J01_card_D4_sq_eq_one` show that
  the respective solution sets of `x ^ 2 = 1` have cardinalities two and six.
  `apm_b93J01_Q8_not_equiv_D4` transports this subtype through a hypothetical
  multiplicative equivalence and contradicts those cardinalities. Ordinary
  kernel reduction is also used in the older noncommutativity helper. Thus
  all three frozen quaternion non-isomorphisms
  are now proved; the unrelated broad classification clauses remain open.
  -/
  have hsimple6 : ∀ n : ℕ, 6 ≤ n →
      IsSimpleGroup (alternatingGroup (Fin n)) := by
    intro n h6
    apply apm_b93J01_alternating_isSimpleGroup_of_minimalSupport (by omega)
    intro H hH g hg hg1 hgmin
    rcases apm_b93J01_minimalSupport_card_three_or_six
        h6 H hH g hg hg1 hgmin with h3 | h6card
    · exact card_support_eq_three_iff.mp h3
    · exact (apm_b93J01_minimalSupport_card_ne_six
        H hH g hg hgmin h6card).elim
  have hsimple : ∀ n : ℕ, 5 ≤ n →
      IsSimpleGroup (alternatingGroup (Fin n)) :=
    apm_b93J01_alternating_simple_of_six_le hsimple6
  refine ⟨apm_b93J01_A4_not_simple, hsimple, ?_,
    apm_b93J01_card_eight_classification, ?_, apm_b93J01_lagrange,
    apm_b93J01_rat_not_directSumOfCyclic,
    apm_b93J01_finite_addCommGroup_directSum, ?_, ?_⟩
  · exact ⟨apm_b93J01_card_Q8, apm_b93J01_Q8_not_equiv_ZMod8,
      apm_b93J01_Q8_not_equiv_ZMod4_prod_ZMod2,
      apm_b93J01_Q8_not_equiv_D4⟩
  · exact ⟨apm_b93J01_card_A4, apm_b93J01_A4_no_subgroup_card_six⟩
  · exact ⟨apm_b93J01_card_S3, apm_b93J01_not_isCyclic_S3⟩
  · intro p q hp hq hpq hnot G _ _ hG
    exact apm_b93J01_isCyclic_of_card_mul_primes
      p q hp hq hpq hnot G hG
