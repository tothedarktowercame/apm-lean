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

/-- `A₄` has no subgroup of order six.  The short proof is useful below:
an order-six subgroup would have index two, hence contain the commutator
subgroup, which in `A₄` is the Klein four group. -/
lemma apm_b98J01_no_subgroup_card_six
    (H : Subgroup (alternatingGroup (Fin 4))) : Nat.card H ≠ 6 := by
  intro hH
  have hA : Nat.card (alternatingGroup (Fin 4)) = 12 :=
    alternatingGroup.card_of_card_eq_four (by simp)
  have hi : H.index = 2 := by
    have hc := H.card_mul_index
    rw [hH, hA] at hc
    omega
  letI : H.Normal := H.normal_of_index_eq_two hi
  have hq : Nat.card (alternatingGroup (Fin 4) ⧸ H) = 2 := by
    rw [← H.index_eq_card]
    exact hi
  haveI : IsCyclic (alternatingGroup (Fin 4) ⧸ H) :=
    isCyclic_of_prime_card hq
  have hcomm : commutator (alternatingGroup (Fin 4)) ≤ H :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hV : alternatingGroup.kleinFour (Fin 4) ≤ H := by
    rw [alternatingGroup.kleinFour_eq_commutator (by simp)]
    exact hcomm
  have hd := Subgroup.card_dvd_of_le hV
  rw [alternatingGroup.kleinFour_card_of_card_eq_four (by simp), hH] at hd
  omega

lemma apm_b98J01_kernel_card_three_central
    {G : Type*} [Group G] [Fintype G]
    (hG : Nat.card G = 36)
    (K : Subgroup G) (φ : G →* alternatingGroup (Fin 4))
    (hKn : K.Normal) (hK : Nat.card K = 3)
    (hφ : Function.Surjective φ) (hker : φ.ker = K) :
    ∀ k ∈ K, ∀ g : G, k * g = g * k := by
  letI : K.Normal := hKn
  haveI : IsCyclic K := isCyclic_of_prime_card hK
  let c : G →* MulAut K := MulAut.conjNormal
  have hcaut : Nat.card (MulAut K) = 2 := by
    rw [IsCyclic.card_mulAut, hK]
    decide
  have hKc : K ≤ c.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp only [c, MulAut.conjNormal_apply]
    have hx : (k : G) * (x : G) = x * k :=
      congr_arg Subtype.val (mul_comm ⟨k, hk⟩ x)
    rw [hx]
    simp
  by_contra hnot
  push_neg at hnot
  obtain ⟨k, hk, g, hkg⟩ := hnot
  have hcg : c g ≠ 1 := by
    intro heq
    have happ := DFunLike.congr_fun heq ⟨k, hk⟩
    have happ' := congr_arg Subtype.val happ
    simp only [c, MulAut.conjNormal_apply] at happ'
    apply hkg
    exact ((mul_inv_eq_iff_eq_mul).mp happ').symm
  have hrange_ne : c.range ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨⟨c g, ⟨g, rfl⟩⟩, fun he ↦ hcg (Subtype.ext_iff.mp he)⟩
  have hrange_card : Nat.card c.range = 2 := by
    have hd := c.range.card_subgroup_dvd_card
    rw [hcaut, Nat.dvd_prime Nat.prime_two] at hd
    rcases hd with hd | hd
    · exfalso
      apply hrange_ne
      exact Subgroup.card_eq_one.mp hd
    · exact hd
  have hcindex : c.ker.index = 2 := by
    rw [Subgroup.index_ker]
    exact hrange_card
  have hccard : Nat.card c.ker = 18 := by
    have hc := c.ker.card_mul_index
    rw [hcindex, hG] at hc
    omega
  let ψ := φ.subgroupMap c.ker
  have hψker : Nat.card ψ.ker = 3 := by
    rw [Subgroup.ker_subgroupMap]
    have heq : φ.ker.subgroupOf c.ker = K.subgroupOf c.ker := by rw [hker]
    rw [heq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKc).toEquiv).trans hK
  have hψrange : Nat.card (c.ker.map φ) = 6 := by
    have hc := ψ.ker.card_mul_index
    rw [Subgroup.index_ker, hψker] at hc
    have hψ : Function.Surjective ψ := φ.subgroupMap_surjective c.ker
    rw [MonoidHom.range_eq_top.mpr hψ] at hc
    rw [Subgroup.card_top] at hc
    have hdom : Nat.card ↥c.ker = 18 := hccard
    rw [hdom] at hc
    omega
  apply apm_b98J01_no_subgroup_card_six (c.ker.map φ)
  exact hψrange

lemma apm_b98J01_kleinFour_pullback_data
    {G : Type*} [Group G] [Fintype G]
    (hG : Nat.card G = 36)
    (K : Subgroup G) (φ : G →* alternatingGroup (Fin 4))
    (hKn : K.Normal) (hK : Nat.card K = 3)
    (hφ : Function.Surjective φ) (hker : φ.ker = K) :
    ∃ N : Subgroup G,
      N.Normal ∧ Nat.card N = 12 ∧ K ≤ N ∧
      (∀ k ∈ K, ∀ n ∈ N, k * n = n * k) := by
  let N := (alternatingGroup.kleinFour (Fin 4)).comap φ
  have hstruct := apm_b98J01_kleinFour_comap_normal_and_ker_le φ
  refine ⟨N, hstruct.1, apm_b98J01_kleinFour_comap_card φ hφ ?_, ?_, ?_⟩
  · simpa [hker] using hK
  · rw [← hker]
    exact hstruct.2
  · intro k hk n hn
    exact apm_b98J01_kernel_card_three_central hG K φ hKn hK hφ hker k hk n

lemma apm_b98J01_commutative_of_central_card_three_index_four
    {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 12) (K : Subgroup G) (hKn : K.Normal)
    (hK : Nat.card K = 3) (hi : K.index = 4)
    (hKz : K ≤ Subgroup.center G) : ∀ x y : G, x * y = y * x := by
  letI : K.Normal := hKn
  obtain ⟨H, hcomp⟩ := K.exists_right_complement'_of_coprime (by
    rw [hK, hi]
    decide)
  have hH : Nat.card H = 4 := by
    have hc := hcomp.card_mul
    rw [hK, hG] at hc
    omega
  letI : CommGroup H := IsPGroup.commGroupOfCardEqPrimeSq (p := 2) (by simpa using hH)
  intro x y
  obtain ⟨⟨kx, hx⟩, rfl⟩ := hcomp.2 x
  obtain ⟨⟨ky, hy⟩, rfl⟩ := hcomp.2 y
  have hkx (g : G) : g * (kx : G) = kx * g :=
    Subgroup.mem_center_iff.mp (hKz kx.2) g
  have hky (g : G) : g * (ky : G) = ky * g :=
    Subgroup.mem_center_iff.mp (hKz ky.2) g
  have hHcomm : (hx : G) * hy = hy * hx :=
    by simpa using congr_arg Subtype.val (mul_comm hx hy)
  calc
    (kx : G) * hx * ((ky : G) * hy) = kx * (ky * (hx * hy)) := by
      rw [mul_assoc, ← mul_assoc (hx : G) ky hy, hky hx, mul_assoc]
    _ = ky * (kx * (hx * hy)) := by
      rw [← mul_assoc (kx : G) ky, hky kx, mul_assoc]
    _ = ky * (kx * (hy * hx)) := by rw [hHcomm]
    _ = (ky : G) * hy * (kx * hx) := by
      rw [← mul_assoc (kx : G) hy, (hkx hy).symm, mul_assoc, ← mul_assoc]

lemma apm_b98J01_kleinFour_pullback_commutative
    {G : Type*} [Group G] [Fintype G]
    (hG : Nat.card G = 36)
    (K : Subgroup G) (φ : G →* alternatingGroup (Fin 4))
    (hKn : K.Normal) (hK : Nat.card K = 3)
    (hφ : Function.Surjective φ) (hker : φ.ker = K) :
    let N := (alternatingGroup.kleinFour (Fin 4)).comap φ
    ∀ x y : N, x * y = y * x := by
  dsimp
  let N := (alternatingGroup.kleinFour (Fin 4)).comap φ
  have hKN : K ≤ N := by
    rw [← hker]
    exact Subgroup.ker_le_comap φ _
  let K' := K.subgroupOf N
  have hK' : Nat.card K' = 3 := by
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv).trans hK
  have hN : Nat.card N = 12 := by
    exact apm_b98J01_kleinFour_comap_card φ hφ (by simpa [hker] using hK)
  have hi : K'.index = 4 := by
    have hc := K'.card_mul_index
    rw [hK', hN] at hc
    omega
  have hK'n : K'.Normal := hKn.subgroupOf N
  have hK'z : K' ≤ Subgroup.center N := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro n
    apply Subtype.ext
    exact (apm_b98J01_kernel_card_three_central hG K φ hKn hK hφ hker
      k.1 hk n.1).symm
  exact apm_b98J01_commutative_of_central_card_three_index_four
    hN K' hK'n hK' hi hK'z

lemma apm_b98J01_final_conjunct
    {G : Type*} [Group G] [Fintype G] (hG : Nat.card G = 36) :
    ∀ (K : Subgroup G) (φ : G →* alternatingGroup (Fin 4)),
      K.Normal → Nat.card K = 3 → Function.Surjective φ → φ.ker = K →
      ∃ N : Subgroup G,
        N.Normal ∧ Nat.card N = 12 ∧ K ≤ N ∧
        ((∀ x y : N, x * y = y * x) ∨ Nat.card (Subgroup.center N) = 2) ∧
        (∀ k ∈ K, ∀ n ∈ N, k * n = n * k) := by
  intro K φ hKn hK hφ hker
  let N := (alternatingGroup.kleinFour (Fin 4)).comap φ
  have hstruct := apm_b98J01_kleinFour_comap_normal_and_ker_le φ
  refine ⟨N, hstruct.1, apm_b98J01_kleinFour_comap_card φ hφ ?_, ?_, ?_, ?_⟩
  · simpa [hker] using hK
  · rw [← hker]
    exact hstruct.2
  · left
    exact apm_b98J01_kleinFour_pullback_commutative hG K φ hKn hK hφ hker
  · intro k hk n hn
    exact apm_b98J01_kernel_card_three_central hG K φ hKn hK hφ hker k hk n

lemma apm_b98J01_card_sylow_three
    {G : Type*} [Group G] [Fintype G] (hG : Nat.card G = 36)
    (hnormal : ¬∃ H : Subgroup G, H.Normal ∧ Nat.card H = 9) :
    Nat.card (Sylow 3 G) = 4 := by
  let P : Sylow 3 G := default
  have hPcard : Nat.card P = 9 := by
    rw [Sylow.card_eq_multiplicity, hG,
      Nat.factorization_eq_card_pow_dvd 36 Nat.prime_three]
    decide
  have hPindex : P.index = 4 := by
    have hc := P.card_mul_index
    rw [hPcard, hG] at hc
    omega
  have hd : Nat.card (Sylow 3 G) ∣ 4 := by
    simpa [hPindex] using P.card_dvd_index
  have hm : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
  have hn1 : Nat.card (Sylow 3 G) ≠ 1 := by
    intro hone
    letI : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp hone).1
    have hPn : P.Normal := Sylow.normal_of_subsingleton P
    exact hnormal ⟨P, hPn, hPcard⟩
  have hd' : Nat.card (Sylow 3 G) ∣ 2 ^ 2 := by simpa using hd
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp hd' with ⟨k, hk, heq⟩
  interval_cases k <;> simp_all [Nat.ModEq]

lemma apm_b98J01_sylow_action_kernel_card
    {G : Type*} [Group G] [Fintype G] (hG : Nat.card G = 36)
    (hnormal : ¬∃ H : Subgroup G, H.Normal ∧ Nat.card H = 9) :
    let ρ := MulAction.toPermHom G (Sylow 3 G)
    Nat.card ρ.ker = 3 ∧ Nat.card ρ.range = 12 := by
  let ρ := MulAction.toPermHom G (Sylow 3 G)
  change Nat.card ρ.ker = 3 ∧ Nat.card ρ.range = 12
  let P : Sylow 3 G := default
  have hsyl : Nat.card (Sylow 3 G) = 4 :=
    apm_b98J01_card_sylow_three hG hnormal
  have hkerstab : ρ.ker ≤ MulAction.stabilizer G P := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [MulAction.mem_stabilizer_iff]
    have ha := DFunLike.congr_fun hg P
    simpa [ρ] using ha
  have hfour : 4 ∣ Nat.card ρ.range := by
    rw [← Subgroup.index_ker]
    have hd := Subgroup.index_dvd_of_le hkerstab
    rw [Sylow.stabilizer_eq_normalizer,
      ← P.card_eq_index_normalizer, hsyl] at hd
    exact hd
  have hrangeG : Nat.card ρ.range ∣ 36 := by
    rw [← Subgroup.index_ker]
    rw [← hG]
    exact ρ.ker.index_dvd_card
  have hrangePerm : Nat.card ρ.range ∣ 24 := by
    have hd := ρ.range.card_subgroup_dvd_card
    rw [Nat.card_perm, hsyl] at hd
    norm_num at hd ⊢
    exact hd
  have hmul : Nat.card ρ.ker * Nat.card ρ.range = 36 := by
    have hc := ρ.ker.card_mul_index
    rw [Subgroup.index_ker, hG] at hc
    exact hc
  have hknot9 : Nat.card ρ.ker ≠ 9 := by
    intro hk
    exact hnormal ⟨ρ.ker, inferInstance, hk⟩
  have hrle : Nat.card ρ.range ≤ 24 := Nat.le_of_dvd (by omega) hrangePerm
  interval_cases hr : Nat.card ρ.range <;> omega

lemma apm_b98J01_no_normal_card_eighteen
    {G : Type*} [Group G] [Fintype G]
    (hnormal : ¬∃ H : Subgroup G, H.Normal ∧ Nat.card H = 9)
    (L : Subgroup G) (hLn : L.Normal) (hL : Nat.card L = 18) : False := by
  letI : L.Normal := hLn
  let P : Sylow 3 L := default
  have hP : Nat.card P = 9 := by
    rw [Sylow.card_eq_multiplicity, hL,
      Nat.factorization_eq_card_pow_dvd 18 Nat.prime_three]
    decide
  have hi : P.index = 2 := by
    have hc := P.card_mul_index
    rw [hP, hL] at hc
    omega
  have hsyl : Nat.card (Sylow 3 L) = 1 := by
    have hd : Nat.card (Sylow 3 L) ∣ 2 := by simpa [hi] using P.card_dvd_index
    have hm := card_sylow_modEq_one 3 L
    have hle : Nat.card (Sylow 3 L) ≤ 2 := Nat.le_of_dvd (by omega) hd
    interval_cases h : Nat.card (Sylow 3 L) <;> simp_all [Nat.ModEq]
  letI : Subsingleton (Sylow 3 L) := (Nat.card_eq_one_iff_unique.mp hsyl).1
  letI : P.Characteristic := Sylow.characteristic_of_subsingleton P
  have hnormalG : (P.map L.subtype).Normal := inferInstance
  have hcardG : Nat.card (P.map L.subtype) = 9 := by
    rw [Subgroup.card_subtype, hP]
  exact hnormal ⟨P.map L.subtype, hnormalG, hcardG⟩

lemma apm_b98J01_sylow_action_even
    {G : Type*} [Group G] [Fintype G] [DecidableEq (Sylow 3 G)]
    (hG : Nat.card G = 36)
    (hnormal : ¬∃ H : Subgroup G, H.Normal ∧ Nat.card H = 9) :
    let ρ := MulAction.toPermHom G (Sylow 3 G)
    ∀ g, ρ g ∈ alternatingGroup (Sylow 3 G) := by
  classical
  let ρ := MulAction.toPermHom G (Sylow 3 G)
  change ∀ g, ρ g ∈ alternatingGroup (Sylow 3 G)
  let s : G →* ℤˣ := Equiv.Perm.sign.comp ρ
  have hsktop : s.ker = ⊤ := by
    by_contra hne
    have hrne : s.range ≠ ⊥ := by
      intro hr
      apply hne
      rw [MonoidHom.ker_eq_top_iff, ← MonoidHom.range_eq_bot_iff]
      exact hr
    have hrcard : Nat.card s.range = 2 := by
      have hd := s.range.card_subgroup_dvd_card
      have hu : Nat.card ℤˣ = 2 := by
        rw [Nat.card_eq_fintype_card]
        decide
      rw [hu, Nat.dvd_prime Nat.prime_two] at hd
      exact Or.resolve_left hd (fun h ↦ hrne (Subgroup.card_eq_one.mp h))
    have hkcard : Nat.card s.ker = 18 := by
      have hc := s.ker.card_mul_index
      rw [Subgroup.index_ker, hrcard, hG] at hc
      omega
    exact apm_b98J01_no_normal_card_eighteen hnormal s.ker inferInstance hkcard
  intro g
  rw [Equiv.Perm.mem_alternatingGroup]
  have hg : g ∈ s.ker := by rw [hsktop]; trivial
  exact hg

lemma apm_b98J01_first_conjunct
    {G : Type*} [Group G] [Fintype G] (hG : Nat.card G = 36)
    (hnormal : ¬∃ H : Subgroup G, H.Normal ∧ Nat.card H = 9) :
    ∃ (K : Subgroup G) (φ : G →* alternatingGroup (Fin 4)),
      K.Normal ∧ Nat.card K = 3 ∧ Function.Surjective φ ∧ φ.ker = K := by
  classical
  let ρ := MulAction.toPermHom G (Sylow 3 G)
  have heven : ∀ g, ρ g ∈ alternatingGroup (Sylow 3 G) :=
    apm_b98J01_sylow_action_even hG hnormal
  let ψ : G →* alternatingGroup (Sylow 3 G) :=
    ρ.codRestrict (alternatingGroup (Sylow 3 G)) heven
  have hρ := apm_b98J01_sylow_action_kernel_card hG hnormal
  have hψker : ψ.ker = ρ.ker := by
    ext g
    simp [ψ]
  have hψker_card : Nat.card ψ.ker = 3 := by rw [hψker, hρ.1]
  have hψrange_card : Nat.card ψ.range = 12 := by
    have hc := ψ.ker.card_mul_index
    rw [Subgroup.index_ker, hψker_card, hG] at hc
    omega
  have hsyl : Nat.card (Sylow 3 G) = 4 :=
    apm_b98J01_card_sylow_three hG hnormal
  have haltcard : Nat.card (alternatingGroup (Sylow 3 G)) = 12 :=
    alternatingGroup.card_of_card_eq_four hsyl
  have hψsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top]
    exact ψ.range.eq_top_of_card_eq (hψrange_card.trans haltcard.symm)
  let e : Sylow 3 G ≃ Fin 4 := Fintype.equivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hsyl)
  let φ : G →* alternatingGroup (Fin 4) := e.altCongrHom.toMonoidHom.comp ψ
  have hφsurj : Function.Surjective φ := e.altCongrHom.surjective.comp hψsurj
  have hφker : φ.ker = ψ.ker := by
    ext g
    simp [φ]
  refine ⟨φ.ker, φ, inferInstance, ?_, hφsurj, rfl⟩
  rw [hφker]
  exact hψker_card

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
  -/
  refine ⟨?_, h_klein_four, ?_⟩
  · intro hnormal
    exact apm_b98J01_first_conjunct (by simpa using hGcard) hnormal
  · exact apm_b98J01_final_conjunct (by simpa using hGcard)
