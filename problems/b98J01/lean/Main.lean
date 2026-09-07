import Mathlib

open scoped commutatorElement

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

lemma apm_b98J01_card_comap_of_surjective
    {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) (hφ : Function.Surjective φ) (V : Subgroup Q) :
    Nat.card (V.comap φ) = Nat.card φ.ker * Nat.card V := by
  let N : Subgroup G := V.comap φ
  let ψ := φ.subgroupMap N
  have hψ : Function.Surjective ψ := φ.subgroupMap_surjective N
  have hmap : N.map φ = V := by
    dsimp [N]
    exact Subgroup.map_comap_eq_self_of_surjective hφ V
  have hker : Nat.card ψ.ker = Nat.card φ.ker := by
    rw [Subgroup.ker_subgroupMap]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.ker_le_comap φ V)).toEquiv
  have hrange : Nat.card ψ.range = Nat.card V := by
    rw [MonoidHom.range_eq_top.mpr hψ]
    simpa [hmap]
  have hcard := ψ.ker.card_mul_index
  rw [Subgroup.index_ker, hker, hrange] at hcard
  exact hcard.symm

lemma apm_b98J01_kleinFour_comap_card
    {G : Type*} [Group G] (φ : G →* alternatingGroup (Fin 4))
    (hφ : Function.Surjective φ) (hker : Nat.card φ.ker = 3) :
    Nat.card ((alternatingGroup.kleinFour (Fin 4)).comap φ) = 12 := by
  rw [apm_b98J01_card_comap_of_surjective φ hφ,
    alternatingGroup.kleinFour_card_of_card_eq_four (by simp), hker]

/-- Every homomorphism from `A₄` to an abelian group kills its Klein four
subgroup.  This is the structural replacement for a bespoke enumeration of
index-two subgroups and is the key input for ruling out a nontrivial action on
an order-three kernel. -/
lemma apm_b98J01_kleinFour_le_ker_of_commGroup
    {A : Type*} [CommGroup A]
    (f : alternatingGroup (Fin 4) →* A) :
    alternatingGroup.kleinFour (Fin 4) ≤ f.ker := by
  rw [alternatingGroup.kleinFour_eq_commutator (by simp)]
  exact Abelianization.commutator_subset_ker f

/-- An action of `A₄` on a group of order three is trivial.  Cardinality
forces the automorphism group to have order two, while the preceding
commutator lemma forces the kernel to contain the four-element `V₄`. -/
lemma apm_b98J01_hom_A4_mulAut_card_three_eq_one
    {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 3)
    (f : alternatingGroup (Fin 4) →* MulAut K) : f = 1 := by
  letI : IsCyclic K := isCyclic_of_prime_card hK
  let e := IsCyclic.mulAutMulEquiv K
  let _ := e.toMonoidHom.commGroupOfInjective e.injective
  have hV : alternatingGroup.kleinFour (Fin 4) ≤ f.ker :=
    apm_b98J01_kleinFour_le_ker_of_commGroup f
  have hdvd4 : 4 ∣ Nat.card f.ker := by
    have h := Subgroup.card_dvd_of_le hV
    calc
      4 = Nat.card (alternatingGroup.kleinFour (Fin 4)) := by
        symm
        exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
      _ ∣ Nat.card f.ker := h
  have hA4 : Nat.card (alternatingGroup (Fin 4)) = 12 :=
    alternatingGroup.card_of_card_eq_four (by simp)
  have hker_le : Nat.card f.ker ≤ 12 := by
    rw [← hA4]
    exact Subgroup.card_le_card_group f.ker
  have hmul : Nat.card f.ker * Nat.card f.range = 12 := by
    simpa [Subgroup.index_ker, hA4] using f.ker.card_mul_index
  have hAut : Nat.card (MulAut K) = 2 := by
    rw [IsCyclic.card_mulAut K, hK]
    decide
  have hrange_le_two : Nat.card f.range ≤ 2 := by
    rw [← hAut]
    exact Subgroup.card_le_card_group f.range
  have hker : Nat.card f.ker = 4 ∨ Nat.card f.ker = 8 ∨
      Nat.card f.ker = 12 := by
    obtain ⟨c, hc⟩ := hdvd4
    have hpos : 0 < Nat.card f.ker := Nat.card_pos
    omega
  have hrange : Nat.card f.range = 1 := by
    generalize hr : Nat.card f.range = r at hmul hrange_le_two ⊢
    rcases hker with hker | hker | hker
    all_goals rw [hker] at hmul
    all_goals interval_cases r <;> omega
  exact f.range_eq_bot_iff.mp (f.range.eq_bot_iff_card.mpr hrange)

/-- The order-three kernel of a surjection onto `A₄` is central.  Conjugation
first descends through the quotient because the kernel is cyclic, and the
descended action is trivial by the preceding lemma. -/
lemma apm_b98J01_ker_central_of_surjective_A4
    {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (hKn : K.Normal) (hK : Nat.card K = 3)
    (φ : G →* alternatingGroup (Fin 4)) (hφ : Function.Surjective φ)
    (hker : φ.ker = K) :
    ∀ k ∈ K, ∀ g : G, k * g = g * k := by
  letI : K.Normal := hKn
  letI : IsCyclic K := isCyclic_of_prime_card hK
  let action : G →* MulAut K := MulAut.conjNormal
  have hKaction : K ≤ action.ker := by
    intro k hk
    change action k = 1
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    have hc : k * (x : G) = (x : G) * k := by
      exact congrArg Subtype.val (mul_comm (⟨k, hk⟩ : K) x)
    change k * (x : G) * k⁻¹ = (x : G)
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  let qaction : (G ⧸ K) →* MulAut K := QuotientGroup.lift K action hKaction
  let e : (G ⧸ K) ≃* alternatingGroup (Fin 4) :=
    QuotientGroup.liftEquiv K hφ hker.symm
  let descended : alternatingGroup (Fin 4) →* MulAut K :=
    qaction.comp e.symm.toMonoidHom
  have hdesc : descended = 1 :=
    apm_b98J01_hom_A4_mulAut_card_three_eq_one hK descended
  have hfactor : action = descended.comp φ := by
    ext g x
    change g * (x : G) * g⁻¹ = _
    change g * (x : G) * g⁻¹ =
      ((qaction.comp e.symm.toMonoidHom) (φ g)) x
    have he : e (g : G ⧸ K) = φ g := by
      change QuotientGroup.liftEquiv K hφ hker.symm (g : G ⧸ K) = φ g
      rfl
    rw [← he]
    simp [qaction, action]
  intro k hk g
  have ha : action g = 1 := by rw [hfactor, hdesc]; rfl
  have hx := DFunLike.congr_fun ha ⟨k, hk⟩
  have hxv := congrArg Subtype.val hx
  change g * k * g⁻¹ = k at hxv
  calc
    k * g = (g * k * g⁻¹) * g := congrArg (· * g) hxv.symm
    _ = g * k := by simp [mul_assoc]

/-- All parts of the canonical pullback witness except its abelianness (which
is the remaining coprime central-extension argument). -/
lemma apm_b98J01_pullback_witness_except_abelian
    {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (hKn : K.Normal) (hK : Nat.card K = 3)
    (φ : G →* alternatingGroup (Fin 4)) (hφ : Function.Surjective φ)
    (hker : φ.ker = K) :
    ∃ N : Subgroup G,
      N.Normal ∧ Nat.card N = 12 ∧ K ≤ N ∧
      (∀ k ∈ K, ∀ n ∈ N, k * n = n * k) := by
  let N := (alternatingGroup.kleinFour (Fin 4)).comap φ
  have hb := apm_b98J01_kleinFour_comap_normal_and_ker_le φ
  refine ⟨N, hb.1, apm_b98J01_kleinFour_comap_card φ hφ ?_, ?_, ?_⟩
  · simpa [hker] using hK
  · simpa [hker] using hb.2
  · intro k hk n hn
    exact apm_b98J01_ker_central_of_surjective_A4 K hKn hK φ hφ hker k hk n

/-- The canonical order-twelve pullback is abelian.  Its image is Klein four,
so squares and commutators land in the central kernel.  A central commutator
then has square one, while membership in the order-three kernel gives cube
one, forcing it to be trivial. -/
lemma apm_b98J01_kleinFour_comap_abelian
    {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (hKn : K.Normal) (hK : Nat.card K = 3)
    (φ : G →* alternatingGroup (Fin 4)) (hφ : Function.Surjective φ)
    (hker : φ.ker = K) :
    ∀ x y : (alternatingGroup.kleinFour (Fin 4)).comap φ,
      x * y = y * x := by
  let V := alternatingGroup.kleinFour (Fin 4)
  letI : IsKleinFour V := alternatingGroup.kleinFour_isKleinFour (by simp)
  have hcentral :=
    apm_b98J01_ker_central_of_surjective_A4 K hKn hK φ hφ hker
  intro x y
  let vx : V := ⟨φ x, x.2⟩
  let vy : V := ⟨φ y, y.2⟩
  have himage_comm : φ x * φ y = φ y * φ x := by
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := V)).is_comm.comm vx vy)
  let c : G := ⁅(x : G), (y : G)⁆
  have hcK : c ∈ K := by
    rw [← hker, MonoidHom.mem_ker]
    change φ ⁅(x : G), (y : G)⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr himage_comm
  have hccentral (z : G) : c * z = z * c := hcentral c hcK z
  have hx2K : (x : G) ^ 2 ∈ K := by
    rw [← hker, MonoidHom.mem_ker, map_pow]
    change (φ x) ^ 2 = 1
    exact congrArg Subtype.val (IsKleinFour.mul_self vx)
  have hx2central : (x : G) ^ 2 * (y : G) = (y : G) * (x : G) ^ 2 :=
    hcentral ((x : G) ^ 2) hx2K y
  have hxy : (x : G) * y = c * ((y : G) * x) := by
    dsimp [c]
    rw [commutatorElement_def]
    group
  have hsq_relation : (x : G) ^ 2 * y = c ^ 2 * ((y : G) * (x : G) ^ 2) := by
    calc
      (x : G) ^ 2 * y = x * (x * y) := by simp only [pow_two, mul_assoc]
      _ = x * (c * (y * x)) := by rw [hxy]
      _ = c * (x * (y * x)) := by
        rw [← mul_assoc, ← hccentral x, mul_assoc]
      _ = c * ((c * (y * x)) * x) := by
        rw [← mul_assoc (x : G) y x, hxy]
      _ = c ^ 2 * (y * (x : G) ^ 2) := by
        simp only [pow_two, mul_assoc]
  have hc2 : c ^ 2 = 1 := by
    rw [hx2central] at hsq_relation
    have heq : c ^ 2 * ((y : G) * x ^ 2) = 1 * (y * x ^ 2) := by
      simpa using hsq_relation.symm
    exact mul_right_cancel heq
  let ck : K := ⟨c, hcK⟩
  have hc3sub : ck ^ 3 = 1 := by
    simpa [hK] using (pow_card_eq_one' (x := ck))
  have hc3 : c ^ 3 = 1 := congrArg Subtype.val hc3sub
  have hc1 : c = 1 := by
    have hc3eq : c ^ 3 = c := by
      calc
        c ^ 3 = c ^ 2 * c := by group
        _ = c := by rw [hc2, one_mul]
    calc
      c = c ^ 3 := hc3eq.symm
      _ = 1 := hc3
  apply Subtype.ext
  apply commutatorElement_eq_one_iff_mul_comm.mp
  exact hc1

lemma apm_b98J01_surjective_A4_pullback_conclusion
    {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (hKn : K.Normal) (hK : Nat.card K = 3)
    (φ : G →* alternatingGroup (Fin 4)) (hφ : Function.Surjective φ)
    (hker : φ.ker = K) :
    ∃ N : Subgroup G,
      N.Normal ∧ Nat.card N = 12 ∧ K ≤ N ∧
      ((∀ x y : N, x * y = y * x) ∨ Nat.card (Subgroup.center N) = 2) ∧
      (∀ k ∈ K, ∀ n ∈ N, k * n = n * k) := by
  let N := (alternatingGroup.kleinFour (Fin 4)).comap φ
  have hb := apm_b98J01_kleinFour_comap_normal_and_ker_le φ
  refine ⟨N, hb.1, apm_b98J01_kleinFour_comap_card φ hφ ?_, ?_,
    Or.inl (apm_b98J01_kleinFour_comap_abelian K hKn hK φ hφ hker), ?_⟩
  · simpa [hker] using hK
  · simpa [hker] using hb.2
  · intro k hk n hn
    exact apm_b98J01_ker_central_of_surjective_A4 K hKn hK φ hφ hker k hk n

/-- Under the order-nine nonnormality hypothesis there are exactly four Sylow
`3`-subgroups.  This is the numerical input for the conjugation action on four
letters. -/
lemma apm_b98J01_card_sylow_three_eq_four
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 36)
    (hno9 : ¬ ∃ H : Subgroup G, H.Normal ∧ Nat.card H = 9) :
    Nat.card (Sylow 3 G) = 4 := by
  let P : Sylow 3 G := Sylow.nonempty.some
  have hPcard : Nat.card P = 9 := by
    rw [Sylow.card_eq_multiplicity, hG]
    have h36 : 36 = 3 ^ 2 * 4 := by norm_num
    rw [h36, Nat.factorization_mul_apply_of_coprime (by decide),
      Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      Nat.prime_three.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide)]
    norm_num
  have hPindex : P.index = 4 := by
    have hc := P.card_mul_index
    rw [hPcard, hG] at hc
    omega
  have hdvd : Nat.card (Sylow 3 G) ∣ 4 := by
    rw [← hPindex]
    exact Sylow.card_dvd_index P
  have hmod : Nat.card (Sylow 3 G) % 3 = 1 := by
    simpa [Nat.ModEq] using (card_sylow_modEq_one 3 G)
  obtain hcard | hcard | hcard : Nat.card (Sylow 3 G) = 1 ∨
      Nat.card (Sylow 3 G) = 2 ∨ Nat.card (Sylow 3 G) = 4 := by
    have hle : Nat.card (Sylow 3 G) ≤ 4 := Nat.le_of_dvd (by decide) hdvd
    have hpos : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
    omega
  · haveI : Subsingleton (Sylow 3 G) :=
      Finite.card_le_one_iff_subsingleton.mp (by omega)
    exact False.elim (hno9 ⟨P, Sylow.normal_of_subsingleton P, hPcard⟩)
  · omega
  · exact hcard

/-- The kernel of the conjugation action on the four Sylow `3`-subgroups has
order three. -/
lemma apm_b98J01_sylow_action_ker_card
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 36)
    (hno9 : ¬ ∃ H : Subgroup G, H.Normal ∧ Nat.card H = 9) :
    Nat.card (MulAction.toPermHom G (Sylow 3 G)).ker = 3 := by
  let P : Sylow 3 G := Sylow.nonempty.some
  let action := MulAction.toPermHom G (Sylow 3 G)
  have hsyl : Nat.card (Sylow 3 G) = 4 :=
    apm_b98J01_card_sylow_three_eq_four hG hno9
  have hPcard : Nat.card P = 9 := by
    rw [Sylow.card_eq_multiplicity, hG]
    have h36 : 36 = 3 ^ 2 * 4 := by norm_num
    rw [h36, Nat.factorization_mul_apply_of_coprime (by decide),
      Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      Nat.prime_three.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide)]
    norm_num
  have hnormindex : (Subgroup.normalizer (P : Set G)).index = 4 := by
    rw [← hsyl]
    exact (Sylow.card_eq_index_normalizer P).symm
  have hnormcard : Nat.card (Subgroup.normalizer (P : Set G)) = 9 := by
    have hc := (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [hnormindex, hG] at hc
    omega
  have hnorm : Subgroup.normalizer (P : Set G) = P := by
    have hle : (P : Subgroup G) ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer
    symm
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hnormcard, hPcard])
  have hkerP : action.ker ≤ (P : Subgroup G) := by
    intro g hg
    have hfix : g • P = P := by
      have ha : action g = 1 := MonoidHom.mem_ker.mp hg
      have hp := Equiv.congr_fun ha P
      simpa [action, MulAction.toPermHom_apply] using hp
    rw [← hnorm]
    exact Sylow.smul_eq_iff_mem_normalizer.mp hfix
  have hker_dvd : Nat.card action.ker ∣ 9 := by
    rw [← hPcard]
    exact Subgroup.card_dvd_of_le hkerP
  have hker_cases : Nat.card action.ker = 1 ∨ Nat.card action.ker = 3 ∨
      Nat.card action.ker = 9 := by
    have hp : Nat.card action.ker ∣ 3 ^ 2 := by norm_num at hker_dvd ⊢; exact hker_dvd
    obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hp
    interval_cases k <;> simp_all
  rcases hker_cases with hker1 | hker3 | hker9
  · have hbot : action.ker = ⊥ := action.ker.eq_bot_iff_card.mpr hker1
    have hinj : Function.Injective action := action.ker_eq_bot_iff.mp hbot
    have hle := Nat.card_le_card_of_injective action hinj
    rw [hG, Nat.card_perm, hsyl] at hle
    norm_num at hle
  · exact hker3
  · have hKP : action.ker = (P : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge hkerP
      omega
    have hPn : (P : Subgroup G).Normal := hKP ▸ (inferInstance : action.ker.Normal)
    exact False.elim (hno9 ⟨P, hPn, hPcard⟩)

/-- Transporting the four-point Sylow action to `Fin 4` gives precisely `A₄`
as its image, hence the required quotient map. -/
lemma apm_b98J01_order36_quotient_A4
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 36)
    (hno9 : ¬ ∃ H : Subgroup G, H.Normal ∧ Nat.card H = 9) :
    ∃ (K : Subgroup G) (φ : G →* alternatingGroup (Fin 4)),
      K.Normal ∧ Nat.card K = 3 ∧ Function.Surjective φ ∧ φ.ker = K := by
  let action := MulAction.toPermHom G (Sylow 3 G)
  have hsyl : Nat.card (Sylow 3 G) = 4 :=
    apm_b98J01_card_sylow_three_eq_four hG hno9
  let e : Sylow 3 G ≃ Fin 4 := Finite.equivFinOfCardEq hsyl
  let ψ : G →* Equiv.Perm (Fin 4) := e.permCongrHom.toMonoidHom.comp action
  have hker : ψ.ker = action.ker := by
    ext g
    simp [ψ, action, MonoidHom.mem_ker]
  have hψker : Nat.card ψ.ker = 3 := by
    rw [hker]
    exact apm_b98J01_sylow_action_ker_card hG hno9
  have hrangecard : Nat.card ψ.range = 12 := by
    have hc := ψ.ker.card_mul_index
    rw [Subgroup.index_ker, hψker, hG] at hc
    omega
  have hrangeindex : ψ.range.index = 2 := by
    have hc := ψ.range.card_mul_index
    rw [hrangecard, Nat.card_perm, Nat.card_fin] at hc
    norm_num at hc ⊢
    omega
  have hrange : ψ.range = alternatingGroup (Fin 4) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hrangeindex
  let φ : G →* alternatingGroup (Fin 4) :=
    ψ.codRestrict (alternatingGroup (Fin 4)) fun g ↦ by
      rw [← hrange]
      exact ⟨g, rfl⟩
  have hφ : Function.Surjective φ := by
    intro a
    have ha : (a : Equiv.Perm (Fin 4)) ∈ ψ.range := by rw [hrange]; exact a.2
    obtain ⟨g, hg⟩ := ha
    exact ⟨g, Subtype.ext hg⟩
  have hφker : φ.ker = ψ.ker := by
    ext g
    simp [φ, MonoidHom.mem_ker]
  refine ⟨φ.ker, φ, inferInstance, ?_, hφ, rfl⟩
  rw [hφker, hψker]

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

  Closer hop 3 routes around those dependent equalities completely.
  `apm_b98J01_card_comap_of_surjective` proves the general formula
  `|V.comap φ| = |ker φ| * |V|` via the restricted `subgroupMap`,
  `Subgroup.ker_subgroupMap`, `Subgroup.subgroupOfEquivOfLe`,
  `Subgroup.card_mul_index`, and `Subgroup.index_ker`.
  `apm_b98J01_kleinFour_comap_card` specializes it to close the exact
  order-12 calculation. Thus the pullback candidate now has compiled
  normality, kernel containment, and cardinality. The open parts are the
  first order-36 Sylow-action quotient construction and, for the final
  conjunct, the center dichotomy and centrality/no-order-six argument.

  F92 solver round 1 replaces the prospective no-order-six enumeration with
  a more useful structural interface.  The compiled lemma
  `apm_b98J01_kleinFour_le_ker_of_commGroup` shows that every homomorphism
  from `A₄` to an abelian target kills `V₄`, by the packaged identity
  `V₄ = [A₄,A₄]`.  Applied to the action of `G/K ≃ A₄` on the
  cyclic group `K` of order three, this reduces centrality to showing that an
  endomorphism of `K` fixing the image of `V₄` is trivial.  The precise
  remaining dependencies are therefore: construct the first Sylow-action
  quotient; construct/factor the conjugation action through `φ`; prove the
  elementary order-three automorphism bridge; then assemble the already
  compiled pullback normality/cardinality/containment and take the left side
  of the center dichotomy from centrality.

  F92 solver round 2 compiles the promised action bridge and its integration.
  `apm_b98J01_hom_A4_mulAut_card_three_eq_one` proves every `A₄`-action on
  a group of order three trivial by combining `V₄ ≤ ker`, `|Aut(K)| = 2`,
  and kernel/range cardinal arithmetic.  The conjugation action is explicitly
  descended through `QuotientGroup.liftEquiv` in
  `apm_b98J01_ker_central_of_surjective_A4`, proving `K ≤ Z(G)`.
  `apm_b98J01_pullback_witness_except_abelian` integrates this with the
  canonical preimage and supplies its normality, order 12, containment of K,
  and the final centrality clause.  Thus the final conjunct now has one exact
  residual: prove this central extension of the abelian Klein four group by
  the central order-three kernel is abelian (equivalently, kill its
  commutator pairing by coprime-order arithmetic).  Independently, the first
  conjunct still requires the order-36 Sylow action producing the quotient.

  F92 solver round 3 closes the entire final conjunct.  For two elements of
  the pullback, their images commute and square to one in `V₄`; hence their
  commutator and the first element's square lie in the now-central kernel.
  Elementary class-two commutator algebra gives `c² = 1`, while Lagrange in
  the order-three kernel gives `c³ = 1`, so `c = 1`.  The compiled
  `apm_b98J01_surjective_A4_pullback_conclusion` now supplies every requested
  field, including the left (abelian) branch of the dichotomy.  On the first
  conjunct, `apm_b98J01_card_sylow_three_eq_four` compiles the complete Sylow
  count: every Sylow 3-subgroup has order nine and index four, its count
  divides four and is 1 mod 3, and the count-one case contradicts `hno9`.
  The sole remaining theorem-level obligation is therefore to turn the
  conjugation action on this four-element Sylow type into a surjection onto
  `alternatingGroup (Fin 4)` and prove its kernel has order three.

  F92 solver round 4 closes that last obligation.  The action kernel lies in
  a chosen Sylow subgroup because its normalizer has order nine and therefore
  equals the Sylow subgroup.  Its order divides nine; order nine would make
  the Sylow subgroup normal, while order one would inject the 36-element
  group into `S₄` of order 24.  Thus the kernel has order three.  Transporting
  the action along `Finite.equivFinOfCardEq` gives an image of order twelve,
  hence index two in `S₄`; `Equiv.Perm.eq_alternatingGroup_of_index_eq_two`
  identifies it with `A₄`.  Codomain restriction then supplies the required
  surjection and the closing theorem assembles with no `sorry`.
  -/
  refine ⟨?_, h_klein_four, ?_⟩
  · intro hno9
    apply apm_b98J01_order36_quotient_A4
    · simpa [Nat.card_eq_fintype_card] using hGcard
    · exact hno9
  · intro K φ hKn hK hφ hker
    exact apm_b98J01_surjective_A4_pullback_conclusion K hKn hK φ hφ hker
