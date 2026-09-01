import Mathlib

universe u

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

/-- Peel the last coordinate from a finite dependent product of groups. -/
def apm_b94J01_piFinSuccLastMulEquiv (n : ℕ)
    (A : Fin (n + 1) → Type*) [∀ i, Group (A i)] :
    (∀ i, A i) ≃* ((∀ i : Fin n, A i.castSucc) × A (Fin.last n)) where
  toFun f := (fun i => f i.castSucc, f (Fin.last n))
  invFun x i := Fin.lastCases x.2 (fun j => x.1 j) i
  left_inv f := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  right_inv x := by
    apply Prod.ext
    · funext i
      simp
    · simp
  map_mul' x y := by
    apply Prod.ext
    · funext i
      rfl
    · rfl

/-- Reindex a dependent product of additive cyclic groups along an equivalence. -/
def apm_b94J01_piMultiplicativeZModCongrLeft {α β : Type*}
    (m : β → ℕ) (e : α ≃ β) :
    ((a : α) → Multiplicative (ZMod (m (e a)))) ≃*
      ((b : β) → Multiplicative (ZMod (m b))) :=
  (MulEquiv.piMultiplicative _).symm |>.trans
    (AddEquiv.toMultiplicative (RingEquiv.piCongrLeft (fun b => ZMod (m b)) e).toAddEquiv) |>.trans
      (MulEquiv.piMultiplicative _)

/-- Append a cyclic factor divisible by every existing invariant factor. -/
lemma apm_b94J01_invariantFactors_append
    (G H : Type*) [Group G] [Group H] (d : List ℕ) (n : ℕ)
    (hd : apm_b94J01_invariantFactors H d) (hn : 2 ≤ n)
    (hdn : ∀ m ∈ d, m ∣ n)
    (eG : G ≃* (H × Multiplicative (ZMod n))) :
    apm_b94J01_invariantFactors G (d ++ [n]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    simp only [List.mem_append, List.mem_singleton] at hm
    exact hm.elim (hd.1 m) (fun h => h ▸ hn)
  · rw [List.pairwise_append]
    exact ⟨hd.2.1, by simp, fun m hm x hx => by
      simp only [List.mem_singleton] at hx
      subst x
      exact hdn m hm⟩
  · obtain ⟨eH⟩ := hd.2.2
    let targetM := fun i : Fin (d ++ [n]).length => (d ++ [n]).get i
    have hlen : d.length + 1 = (d ++ [n]).length := by simp
    let reindex := apm_b94J01_piMultiplicativeZModCongrLeft targetM (finCongr hlen)
    let peel0 := apm_b94J01_piFinSuccLastMulEquiv d.length
      (fun i : Fin (d.length + 1) => Multiplicative (ZMod (targetM (finCongr hlen i))))
    let prefixAlign :
        (∀ i : Fin d.length, Multiplicative (ZMod (targetM (finCongr hlen i.castSucc)))) ≃*
        (∀ i : Fin d.length, Multiplicative (ZMod (d.get i))) :=
      MulEquiv.piCongrRight fun i => MulEquiv.cast (M := fun m : ℕ =>
        Multiplicative (ZMod m)) (by
          simp [targetM, finCongr, List.get_eq_getElem])
    let lastAlign : Multiplicative (ZMod (targetM (finCongr hlen (Fin.last d.length)))) ≃*
        Multiplicative (ZMod n) := MulEquiv.cast (M := fun m : ℕ =>
      Multiplicative (ZMod m)) (by
        simp [targetM, finCongr, List.get_eq_getElem])
    let peel :
        (∀ i : Fin (d ++ [n]).length,
          Multiplicative (ZMod ((d ++ [n]).get i))) ≃*
        ((∀ i : Fin d.length, Multiplicative (ZMod (d.get i))) ×
          Multiplicative (ZMod n)) := by
      exact (reindex.symm.trans peel0).trans (prefixAlign.prodCongr lastAlign)
    exact ⟨(eG.trans (eH.prodCongr (MulEquiv.refl _))).trans peel.symm⟩

lemma apm_b94J01_invariantFactors_singleton (n : ℕ) (hn : 2 ≤ n) :
    apm_b94J01_invariantFactors (Multiplicative (ZMod n)) [n] := by
  refine ⟨by simpa, by simp, ?_⟩
  let align0 : (Fin 1 → Multiplicative (ZMod n)) ≃*
      Multiplicative (ZMod n) := MulEquiv.piUnique _
  let align :
      (∀ i : Fin ([n].length), Multiplicative (ZMod ([n].get i))) ≃*
        Multiplicative (ZMod n) := by
    let familyAlign :
        (∀ i : Fin 1, Multiplicative (ZMod ([n].get i))) ≃*
          (Fin 1 → Multiplicative (ZMod n)) :=
      MulEquiv.piCongrRight fun i => MulEquiv.cast (M := fun m : ℕ =>
        Multiplicative (ZMod m)) (by fin_cases i; rfl)
    simpa using familyAlign.trans align0
  exact ⟨align.symm⟩

/-- A retraction of commutative groups splits off its target as a direct
factor. This is the algebraic consumer for the character-extension route. -/
def apm_b94J01_mulEquiv_ker_prod_of_retraction
    (G H : Type*) [CommGroup G] [CommGroup H]
    (f : G →* H) (s : H →* G) (hs : ∀ h, f (s h) = h) :
    G ≃* (f.ker × H) where
  toFun g :=
    (⟨g * (s (f g))⁻¹, by simp [hs]⟩, f g)
  invFun x := x.1.1 * s x.2
  left_inv g := by simp
  right_inv x := by
    have hx : f x.1.1 = 1 := x.1.2
    apply Prod.ext
    · apply Subtype.ext
      simp [hs, hx]
    · simp [hs, hx]
  map_mul' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x * y * (s (f (x * y)))⁻¹ =
        (x * (s (f x))⁻¹) * (y * (s (f y))⁻¹)
      rw [map_mul f, map_mul s, mul_inv_rev]
      ac_rfl
    · simp

/-- A faithful character of a subgroup, once extended to the ambient group
without leaving its image, gives the retraction needed by the splitting
lemma.  This packages the purely algebraic end of the finite-abelian
character-extension argument. -/
noncomputable def apm_b94J01_retractionOfExtendedFaithfulCharacter
    (G H K : Type*) [CommGroup G] [CommGroup H] [Group K]
    (χ : H →* K) (hχ : Function.Injective χ)
    (φ : G →* K)
    (hrange : ∀ g, φ g ∈ χ.range) : G →* H :=
  (MonoidHom.ofInjective hχ).symm.toMonoidHom.comp (φ.codRestrict χ.range hrange)

@[simp]
lemma apm_b94J01_retractionOfExtendedFaithfulCharacter_section
    (G H K : Type*) [CommGroup G] [CommGroup H] [Group K]
    (s : H →* G) (χ : H →* K) (hχ : Function.Injective χ)
    (φ : G →* K) (hext : ∀ h, φ (s h) = χ h)
    (hrange : ∀ g, φ g ∈ χ.range) (h : H) :
    apm_b94J01_retractionOfExtendedFaithfulCharacter
      G H K χ hχ φ hrange (s h) = h := by
  apply hχ
  change χ ((MonoidHom.ofInjective hχ).symm
    ⟨φ (s h), hrange (s h)⟩) = χ h
  rw [MonoidHom.apply_ofInjective_symm]
  exact hext h

/-- Character extension in range-valued form already supplies the direct
factor decomposition used by the invariant-factor induction. -/
noncomputable def apm_b94J01_mulEquiv_ker_prod_of_extendedFaithfulCharacter
    (G H K : Type*) [CommGroup G] [CommGroup H] [Group K]
    (s : H →* G) (χ : H →* K) (hχ : Function.Injective χ)
    (φ : G →* K) (hext : ∀ h, φ (s h) = χ h)
    (hrange : ∀ g, φ g ∈ χ.range) :
    G ≃* ((apm_b94J01_retractionOfExtendedFaithfulCharacter
      G H K χ hχ φ hrange).ker × H) :=
  apm_b94J01_mulEquiv_ker_prod_of_retraction G H
    (apm_b94J01_retractionOfExtendedFaithfulCharacter
      G H K χ hχ φ hrange) s
    (apm_b94J01_retractionOfExtendedFaithfulCharacter_section
      G H K s χ hχ φ hext hrange)

/-- A cyclic subgroup whose cardinality is the ambient exponent admits the
faithful complex character required by the splitting construction. -/
lemma apm_b94J01_exists_extendedFaithfulCharacter_of_cyclic_card_eq_exponent
    (G : Type*) [CommGroup G] [Finite G] (H : Subgroup G) [IsCyclic H]
    (hcard : Nat.card H = Monoid.exponent G) :
    ∃ (χ : H →* ℂˣ) (φ : G →* ℂˣ),
      Function.Injective χ ∧
      (∀ h, φ (H.subtype h) = χ h) ∧
      ∀ g, φ g ∈ χ.range := by
  let n := Nat.card H
  letI : NeZero n := ⟨Nat.card_pos.ne'⟩
  have hn : n = Monoid.exponent G := hcard
  letI : Fintype H := Fintype.ofFinite H
  let e : H ≃* rootsOfUnity n ℂ :=
    mulEquivOfCyclicCardEq (by
      simpa [n] using
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity ℂ n).symm)
  let χ : H →* ℂˣ := (rootsOfUnity n ℂ).subtype.comp e.toMonoidHom
  have hχ : Function.Injective χ := by
    exact (rootsOfUnity n ℂ).subtype_injective.comp e.injective
  obtain ⟨φ, hφ⟩ := MonoidHom.restrict_surjective (M := ℂ) H χ
  refine ⟨χ, φ, hχ, fun h ↦ DFunLike.congr_fun hφ h, ?_⟩
  intro g
  have hpow : φ g ^ n = 1 := by
    rw [hn, ← map_pow, Monoid.pow_exponent_eq_one, map_one]
  let z : rootsOfUnity n ℂ := ⟨φ g, by rwa [mem_rootsOfUnity]⟩
  obtain ⟨h, hh⟩ := e.surjective z
  refine ⟨h, ?_⟩
  change ((e h : rootsOfUnity n ℂ) : ℂˣ) = φ g
  rw [hh]

lemma apm_b94J01_card_ker_lt_of_retraction
    (G H : Type*) [CommGroup G] [CommGroup H] [Finite G] [Finite H]
    (f : G →* H) (s : H →* G) (hs : ∀ h, f (s h) = h)
    (hH : 2 ≤ Nat.card H) : Nat.card f.ker < Nat.card G := by
  have hcard : Nat.card G = Nat.card f.ker * Nat.card H := by
    rw [Nat.card_congr
      (apm_b94J01_mulEquiv_ker_prod_of_retraction G H f s hs).toEquiv,
      Nat.card_prod]
  have hk : 0 < Nat.card f.ker := Nat.card_pos
  nlinarith

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

/-- The invariant-factor existence-and-uniqueness clause is completely
resolved for groups of cardinality one. -/
lemma apm_b94J01_existsUnique_invariantFactors_of_card_eq_one
    (G : Type*) [CommGroup G] (hcard : Nat.card G = 1) :
    ∃! d : List ℕ, apm_b94J01_invariantFactors G d := by
  letI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hcard).1
  letI : Unique G := { default := 1, uniq := fun _ => Subsingleton.elim _ _ }
  letI : Unique (∀ i : Fin ([].length), Multiplicative (ZMod ([].get i))) :=
    { default := fun i => Fin.elim0 i
      uniq := fun f => funext fun i => Fin.elim0 i }
  refine ⟨[], ?_, ?_⟩
  · refine ⟨by simp, by simp, ?_⟩
    exact ⟨MulEquiv.ofUnique
      (M := G) (N := ∀ i : Fin ([].length), Multiplicative (ZMod ([].get i)))⟩
  · intro d hd
    exact apm_b94J01_invariantFactors_eq_nil_of_card_eq_one G d hd hcard

/-- The cardinality of the subgroup killed by the `k`th-power map. These
numbers are the intrinsic p-primary rank data used by uniqueness. -/
noncomputable def apm_b94J01_powKernelCard (G : Type*) [CommGroup G] (k : ℕ) : ℕ :=
  Nat.card (powMonoidHom k : G →* G).ker

/-- Pure arithmetic presentation of the power-kernel profile. -/
def apm_b94J01_gcdProfile (d : List ℕ) (k : ℕ) : ℕ :=
  (d.map fun n => n.gcd k).prod

@[simp] lemma apm_b94J01_gcdProfile_nil (k : ℕ) :
    apm_b94J01_gcdProfile [] k = 1 := rfl

@[simp] lemma apm_b94J01_gcdProfile_append (d e : List ℕ) (k : ℕ) :
    apm_b94J01_gcdProfile (d ++ e) k =
      apm_b94J01_gcdProfile d k * apm_b94J01_gcdProfile e k := by
  simp [apm_b94J01_gcdProfile]

@[simp] lemma apm_b94J01_gcdProfile_singleton (n k : ℕ) :
    apm_b94J01_gcdProfile [n] k = n.gcd k := by
  simp [apm_b94J01_gcdProfile]

lemma apm_b94J01_gcdProfile_dvd_prod (d : List ℕ) (k : ℕ) :
    apm_b94J01_gcdProfile d k ∣ d.prod := by
  induction d with
  | nil => simp
  | cons n d ih =>
      simp only [apm_b94J01_gcdProfile, List.map_cons, List.prod_cons]
      exact Nat.mul_dvd_mul (Nat.gcd_dvd_left n k) ih

lemma apm_b94J01_gcdProfile_eq_prod_of_forall_dvd
    (d : List ℕ) (k : ℕ) (h : ∀ n ∈ d, n ∣ k) :
    apm_b94J01_gcdProfile d k = d.prod := by
  induction d with
  | nil => rfl
  | cons n d ih =>
      rw [show apm_b94J01_gcdProfile (n :: d) k =
        n.gcd k * apm_b94J01_gcdProfile d k by
          simp [apm_b94J01_gcdProfile]]
      rw [Nat.gcd_eq_left_iff_dvd.mpr (h n (by simp)),
        ih (fun m hm => h m (by simp [hm]))]
      rfl

lemma apm_b94J01_gcdProfile_prod (d : List ℕ) :
    apm_b94J01_gcdProfile d d.prod = d.prod := by
  apply apm_b94J01_gcdProfile_eq_prod_of_forall_dvd
  intro n hn
  exact List.dvd_prod hn

lemma apm_b94J01_prod_eq_of_gcdProfile_eq
    (d e : List ℕ) (h : ∀ k, apm_b94J01_gcdProfile d k = apm_b94J01_gcdProfile e k) :
    d.prod = e.prod := by
  apply Nat.dvd_antisymm
  · rw [← apm_b94J01_gcdProfile_prod d, h]
    exact apm_b94J01_gcdProfile_dvd_prod e d.prod
  · rw [← apm_b94J01_gcdProfile_prod e, ← h]
    exact apm_b94J01_gcdProfile_dvd_prod d e.prod

lemma apm_b94J01_gcdProfile_pos (d : List ℕ) (k : ℕ)
    (hpos : ∀ n ∈ d, 0 < n) : 0 < apm_b94J01_gcdProfile d k := by
  induction d with
  | nil => simp
  | cons a d ih =>
      rw [show apm_b94J01_gcdProfile (a :: d) k =
        a.gcd k * apm_b94J01_gcdProfile d k by simp [apm_b94J01_gcdProfile]]
      exact Nat.mul_pos (Nat.gcd_pos_of_pos_left k (hpos a (by simp)))
        (ih (fun n hn => hpos n (by simp [hn])))

lemma apm_b94J01_forall_dvd_of_gcdProfile_eq_prod
    (d : List ℕ) (k : ℕ) (hpos : ∀ n ∈ d, 0 < n)
    (hsat : apm_b94J01_gcdProfile d k = d.prod) :
    ∀ n ∈ d, n ∣ k := by
  induction d with
  | nil => simp
  | cons a d ih =>
      have ha : 0 < a := hpos a (by simp)
      have htailpos : 0 < d.prod := List.prod_pos (fun n hn => hpos n (by simp [hn]))
      have hgpos : 0 < a.gcd k := Nat.gcd_pos_of_pos_left k ha
      have hprofDvd : apm_b94J01_gcdProfile d k ∣ d.prod :=
        apm_b94J01_gcdProfile_dvd_prod d k
      have hprofpos : 0 < apm_b94J01_gcdProfile d k :=
        apm_b94J01_gcdProfile_pos d k (fun n hn => hpos n (by simp [hn]))
      have hg_le : a.gcd k ≤ a := Nat.gcd_le_left k ha
      have hp_le : apm_b94J01_gcdProfile d k ≤ d.prod :=
        Nat.le_of_dvd htailpos hprofDvd
      have heq : a.gcd k * apm_b94J01_gcdProfile d k = a * d.prod := by
        simpa [apm_b94J01_gcdProfile] using hsat
      have hg : a.gcd k = a := by nlinarith
      have hp : apm_b94J01_gcdProfile d k = d.prod := by nlinarith
      intro n hn
      simp only [List.mem_cons] at hn
      rcases hn with rfl | hn
      · exact Nat.gcd_eq_left_iff_dvd.mp hg
      · exact ih (fun m hm => hpos m (by simp [hm])) hp n hn

lemma apm_b94J01_getLast_eq_of_gcdProfile_eq
    (d e : List ℕ) (hd0 : d ≠ []) (he0 : e ≠ [])
    (hd2 : ∀ n ∈ d, 2 ≤ n) (he2 : ∀ n ∈ e, 2 ≤ n)
    (hdvd : d.Pairwise (· ∣ ·)) (hevd : e.Pairwise (· ∣ ·))
    (hprof : ∀ k, apm_b94J01_gcdProfile d k = apm_b94J01_gcdProfile e k) :
    d.getLast hd0 = e.getLast he0 := by
  have hprod : d.prod = e.prod := apm_b94J01_prod_eq_of_gcdProfile_eq d e hprof
  apply Nat.dvd_antisymm
  · have hesat : apm_b94J01_gcdProfile e (e.getLast he0) = e.prod :=
      apm_b94J01_gcdProfile_eq_prod_of_forall_dvd e (e.getLast he0)
        (fun n hn => hevd.rel_getLast hn)
    have hdsat : apm_b94J01_gcdProfile d (e.getLast he0) = d.prod := by
      rw [hprof, hesat, hprod]
    exact apm_b94J01_forall_dvd_of_gcdProfile_eq_prod d (e.getLast he0)
      (fun n hn => lt_of_lt_of_le (by omega) (hd2 n hn)) hdsat
      (d.getLast hd0) (List.getLast_mem hd0)
  · have hdsat : apm_b94J01_gcdProfile d (d.getLast hd0) = d.prod :=
      apm_b94J01_gcdProfile_eq_prod_of_forall_dvd d (d.getLast hd0)
        (fun n hn => hdvd.rel_getLast hn)
    have hesat : apm_b94J01_gcdProfile e (d.getLast hd0) = e.prod := by
      rw [← hprof, hdsat, ← hprod]
    exact apm_b94J01_forall_dvd_of_gcdProfile_eq_prod e (d.getLast hd0)
      (fun n hn => lt_of_lt_of_le (by omega) (he2 n hn)) hesat
      (e.getLast he0) (List.getLast_mem he0)

lemma apm_b94J01_gcdProfile_dropLast_eq
    (d e : List ℕ) (hd0 : d ≠ []) (he0 : e ≠ [])
    (hdlast : d.getLast hd0 = e.getLast he0)
    (hdlastpos : 0 < d.getLast hd0)
    (hprof : ∀ k, apm_b94J01_gcdProfile d k = apm_b94J01_gcdProfile e k) :
    ∀ k, apm_b94J01_gcdProfile d.dropLast k =
      apm_b94J01_gcdProfile e.dropLast k := by
  intro k
  apply Nat.mul_right_cancel (Nat.gcd_pos_of_pos_left k hdlastpos)
  calc
    apm_b94J01_gcdProfile d.dropLast k * (d.getLast hd0).gcd k =
        apm_b94J01_gcdProfile d k := by
      simpa using congrArg (fun l => apm_b94J01_gcdProfile l k)
        (List.dropLast_append_getLast hd0)
    _ = apm_b94J01_gcdProfile e k := hprof k
    _ = apm_b94J01_gcdProfile e.dropLast k * (d.getLast hd0).gcd k := by
      have h := congrArg (fun l => apm_b94J01_gcdProfile l k)
        (List.dropLast_append_getLast he0)
      simpa [hdlast] using h.symm

/-- The full arithmetic uniqueness theorem for normalized invariant-factor
chains. The power-kernel profile determines the list. -/
theorem apm_b94J01_eq_of_gcdProfile_eq
    (d e : List ℕ)
    (hd2 : ∀ n ∈ d, 2 ≤ n) (he2 : ∀ n ∈ e, 2 ≤ n)
    (hdvd : d.Pairwise (· ∣ ·)) (hevd : e.Pairwise (· ∣ ·))
    (hprof : ∀ k, apm_b94J01_gcdProfile d k = apm_b94J01_gcdProfile e k) :
    d = e := by
  by_cases hd0 : d = []
  · subst d
    have hprod : 1 = e.prod := by
      simpa using apm_b94J01_prod_eq_of_gcdProfile_eq [] e hprof
    cases e with
    | nil => rfl
    | cons a t =>
        have ha2 : 2 ≤ a := he2 a (by simp)
        have hadvd : a ∣ (a :: t).prod := by
          simp only [List.prod_cons]
          exact dvd_mul_right a t.prod
        have ha1 : a = 1 := Nat.eq_one_of_dvd_one (hprod ▸ hadvd)
        omega
  · by_cases he0 : e = []
    · subst e
      have hprod : d.prod = 1 := by
        simpa using apm_b94J01_prod_eq_of_gcdProfile_eq d [] hprof
      obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hd0
      have ha2 : 2 ≤ a := hd2 a (by simp)
      have hadvd : a ∣ (a :: t).prod := by
        simp only [List.prod_cons]
        exact dvd_mul_right a t.prod
      have ha1 : a = 1 := Nat.eq_one_of_dvd_one (hprod ▸ hadvd)
      omega
    · have hlast : d.getLast hd0 = e.getLast he0 :=
        apm_b94J01_getLast_eq_of_gcdProfile_eq d e hd0 he0 hd2 he2 hdvd hevd hprof
      have hlastpos : 0 < d.getLast hd0 :=
        lt_of_lt_of_le (by omega) (hd2 _ (List.getLast_mem hd0))
      have hdropProfile :=
        apm_b94J01_gcdProfile_dropLast_eq d e hd0 he0 hlast hlastpos hprof
      have hdrop : d.dropLast = e.dropLast := apm_b94J01_eq_of_gcdProfile_eq
        d.dropLast e.dropLast
        (fun n hn => hd2 n (List.dropLast_subset d hn))
        (fun n hn => he2 n (List.dropLast_subset e hn))
        (List.Pairwise.sublist (List.dropLast_sublist d) hdvd)
        (List.Pairwise.sublist (List.dropLast_sublist e) hevd)
        hdropProfile
      calc
        d = d.dropLast ++ [d.getLast hd0] := (List.dropLast_append_getLast hd0).symm
        _ = e.dropLast ++ [e.getLast he0] := by rw [hdrop, hlast]
        _ = e := List.dropLast_append_getLast he0
termination_by d.length
decreasing_by simpa using List.length_pos_of_ne_nil hd0

lemma apm_b94J01_gcdProfile_eq_fin_prod (d : List ℕ) (k : ℕ) :
    apm_b94J01_gcdProfile d k = ∏ i : Fin d.length, (d.get i).gcd k := by
  unfold apm_b94J01_gcdProfile
  rw [← List.prod_ofFn]
  congr 1
  exact (List.ofFn_getElem_eq_map d fun n => n.gcd k).symm

lemma apm_b94J01_powKernelCard_eq_of_mulEquiv
    {G H : Type*} [CommGroup G] [CommGroup H] (e : G ≃* H) (k : ℕ) :
    apm_b94J01_powKernelCard G k = apm_b94J01_powKernelCard H k := by
  apply Nat.card_congr
  exact e.toEquiv.subtypeEquiv fun x => by
    simp only [MonoidHom.mem_ker, powMonoidHom_apply]
    constructor
    · intro hx
      simpa using congrArg e hx
    · intro hx
      apply e.injective
      simpa using hx

lemma apm_b94J01_powKernelCard_multiplicative_zmod (n k : ℕ) (hn : n ≠ 0) :
    apm_b94J01_powKernelCard (Multiplicative (ZMod n)) k = n.gcd k := by
  letI : NeZero n := ⟨hn⟩
  unfold apm_b94J01_powKernelCard
  rw [IsCyclic.card_powMonoidHom_ker, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

lemma apm_b94J01_powKernelCard_pi
    {ι : Type*} [Fintype ι] (A : ι → Type*) [∀ i, CommGroup (A i)] (k : ℕ) :
    apm_b94J01_powKernelCard (∀ i, A i) k =
      ∏ i, apm_b94J01_powKernelCard (A i) k := by
  unfold apm_b94J01_powKernelCard
  rw [← Nat.card_pi]
  apply Nat.card_congr
  exact (Equiv.subtypeEquivRight fun f => by
    simp only [MonoidHom.mem_ker, powMonoidHom_apply, Pi.pow_apply, Pi.one_apply,
      funext_iff]).trans Equiv.subtypePiEquivPi

lemma apm_b94J01_powKernelCard_eq_prod_gcd_of_invariantFactors
    (G : Type*) [CommGroup G] (d : List ℕ)
    (hd : apm_b94J01_invariantFactors G d) (k : ℕ) :
    apm_b94J01_powKernelCard G k = ∏ i : Fin d.length, (d.get i).gcd k := by
  obtain ⟨e⟩ := hd.2.2
  rw [apm_b94J01_powKernelCard_eq_of_mulEquiv e,
    apm_b94J01_powKernelCard_pi]
  apply Finset.prod_congr rfl
  intro i hi
  exact apm_b94J01_powKernelCard_multiplicative_zmod _ _ (by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by omega) (hd.1 _ (List.get_mem d i))))

lemma apm_b94J01_powKernelCard_eq_gcdProfile_of_invariantFactors
    (G : Type*) [CommGroup G] (d : List ℕ)
    (hd : apm_b94J01_invariantFactors G d) (k : ℕ) :
    apm_b94J01_powKernelCard G k = apm_b94J01_gcdProfile d k := by
  rw [apm_b94J01_powKernelCard_eq_prod_gcd_of_invariantFactors G d hd k,
    apm_b94J01_gcdProfile_eq_fin_prod]

/-- Any two invariant-factor presentations have the same complete arithmetic
profile. Uniqueness is thereby reduced to reconstructing a divisibility chain
from these products of gcds. -/
lemma apm_b94J01_prod_gcd_eq_prod_gcd_of_invariantFactors
    (G : Type*) [CommGroup G] (d e : List ℕ)
    (hd : apm_b94J01_invariantFactors G d)
    (he : apm_b94J01_invariantFactors G e) (k : ℕ) :
    (∏ i : Fin d.length, (d.get i).gcd k) =
      ∏ i : Fin e.length, (e.get i).gcd k := by
  rw [← apm_b94J01_powKernelCard_eq_prod_gcd_of_invariantFactors G d hd k,
    ← apm_b94J01_powKernelCard_eq_prod_gcd_of_invariantFactors G e he k]

lemma apm_b94J01_gcdProfile_eq_of_invariantFactors
    (G : Type*) [CommGroup G] (d e : List ℕ)
    (hd : apm_b94J01_invariantFactors G d)
    (he : apm_b94J01_invariantFactors G e) (k : ℕ) :
    apm_b94J01_gcdProfile d k = apm_b94J01_gcdProfile e k := by
  rw [← apm_b94J01_powKernelCard_eq_gcdProfile_of_invariantFactors G d hd k,
    ← apm_b94J01_powKernelCard_eq_gcdProfile_of_invariantFactors G e he k]

/-- Uniqueness of normalized invariant factors, separated from existence. -/
theorem apm_b94J01_invariantFactors_unique
    (G : Type*) [CommGroup G] (d e : List ℕ)
    (hd : apm_b94J01_invariantFactors G d)
    (he : apm_b94J01_invariantFactors G e) : d = e := by
  exact apm_b94J01_eq_of_gcdProfile_eq d e hd.1 he.1 hd.2.1 he.2.1
    (fun k => apm_b94J01_gcdProfile_eq_of_invariantFactors G d e hd he k)

/-- The last invariant factor is intrinsic: it is the exponent of the group. -/
lemma apm_b94J01_exponent_eq_getLast_of_invariantFactors
    (G : Type*) [Group G] (d : List ℕ) (hd0 : d ≠ [])
    (hd : apm_b94J01_invariantFactors G d) :
    Monoid.exponent G = d.getLast hd0 := by
  obtain ⟨e⟩ := hd.2.2
  calc
    Monoid.exponent G =
        Monoid.exponent (∀ i : Fin d.length, Multiplicative (ZMod (d.get i))) :=
      Monoid.exponent_eq_of_mulEquiv e
    _ = Finset.lcm Finset.univ (fun i : Fin d.length => d.get i) := by
      rw [Monoid.exponent_pi]
      simp only [Monoid.exponent_multiplicative, ZMod.exponent]
    _ = d.getLast hd0 := by
      apply Nat.dvd_antisymm
      · apply Finset.lcm_dvd
        intro i hi
        exact hd.2.1.rel_getLast (List.get_mem d i)
      · let i : Fin d.length :=
          ⟨d.length - 1,
            Nat.sub_lt (List.length_pos_of_ne_nil hd0) zero_lt_one⟩
        have hi : d.get i = d.getLast hd0 := by
          simp [i, List.getLast_eq_getElem]
        rw [← hi]
        exact Finset.dvd_lcm (Finset.mem_univ i)

/-- Consequently, two nonempty invariant-factor presentations have the same
largest factor. This is the first cancellation datum needed for uniqueness. -/
lemma apm_b94J01_getLast_eq_getLast_of_invariantFactors
    (G : Type*) [Group G] (d e : List ℕ) (hd0 : d ≠ []) (he0 : e ≠ [])
    (hd : apm_b94J01_invariantFactors G d)
    (he : apm_b94J01_invariantFactors G e) :
    d.getLast hd0 = e.getLast he0 := by
  rw [← apm_b94J01_exponent_eq_getLast_of_invariantFactors G d hd0 hd,
    ← apm_b94J01_exponent_eq_getLast_of_invariantFactors G e he0 he]

lemma apm_b94J01_factor_dvd_exponent_of_invariantFactors
    (G : Type*) [CommGroup G] (d : List ℕ)
    (hd : apm_b94J01_invariantFactors G d) (m : ℕ) (hm : m ∈ d) :
    m ∣ Monoid.exponent G := by
  have hd0 : d ≠ [] := List.ne_nil_of_mem hm
  rw [apm_b94J01_exponent_eq_getLast_of_invariantFactors G d hd0 hd]
  exact hd.2.1.rel_getLast hm

lemma apm_b94J01_subgroup_factor_dvd_exponent
    (G : Type*) [CommGroup G] (H : Subgroup G) (d : List ℕ)
    (hd : apm_b94J01_invariantFactors H d) (m : ℕ) (hm : m ∈ d) :
    m ∣ Monoid.exponent G := by
  exact (apm_b94J01_factor_dvd_exponent_of_invariantFactors H d hd m hm).trans
    (Monoid.exponent_submonoid_dvd H.toSubmonoid)

/-- The cardinal recursion needs only this interface from the maximal-cyclic
factor construction.  In particular, divisibility of the recursively
constructed factors is not producer data: it follows from `H ≤ G` and the
identification of the new factor with `Monoid.exponent G`. -/
theorem apm_b94J01_invariantFactors_exists_of_splitProducer
    (split : ∀ (G : Type u) [CommGroup G] [Fintype G], Nat.card G ≠ 1 →
      ∃ (H : Subgroup G) (f : G →* H) (n : ℕ),
        (∀ h : H, f h.1 = h) ∧
        2 ≤ n ∧
        Monoid.exponent G = n ∧
        Nonempty (H ≃* Multiplicative (ZMod n))) :
    ∀ (G : Type u) [CommGroup G] [Fintype G],
      ∃ d : List ℕ, apm_b94J01_invariantFactors G d := by
  let P : ℕ → Prop := fun k => ∀ (G : Type u) [CommGroup G] [Fintype G],
    Nat.card G = k → ∃ d : List ℕ, apm_b94J01_invariantFactors G d
  have hall : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro G _ _ hcardG
        by_cases hcard : Nat.card G = 1
        · exact (apm_b94J01_existsUnique_invariantFactors_of_card_eq_one G hcard).exists
        · obtain ⟨H, f, n, hf, hn, hexp, ⟨eH⟩⟩ := split G hcard
          have hcardH : Nat.card H = n := by
            calc
              Nat.card H = Nat.card (Multiplicative (ZMod n)) := Nat.card_congr eH.toEquiv
              _ = Nat.card (ZMod n) := Nat.card_congr Multiplicative.toAdd
              _ = n := Nat.card_zmod n
          have hkerlt : Nat.card f.ker < Nat.card G :=
            apm_b94J01_card_ker_lt_of_retraction G H f H.subtype hf
              (by simpa [hcardH] using hn)
          letI : Fintype f.ker := Fintype.ofFinite f.ker
          obtain ⟨d, hd⟩ := ih (Nat.card f.ker) (hcardG ▸ hkerlt) f.ker rfl
          refine ⟨d ++ [n], apm_b94J01_invariantFactors_append G f.ker d n hd hn ?_ ?_⟩
          · intro m hm
            rw [← hexp]
            exact apm_b94J01_subgroup_factor_dvd_exponent G f.ker d hd m hm
          · exact (apm_b94J01_mulEquiv_ker_prod_of_retraction G H f H.subtype hf).trans
              ((MulEquiv.refl f.ker).prodCongr eH)
  intro G _ _
  exact hall (Nat.card G) G rfl

/-- A maximal-order cyclic subgroup supplies the split producer required by
the cardinal recursion. -/
lemma apm_b94J01_maximalCyclic_splitProducer
    (G : Type u) [CommGroup G] [Fintype G] (hcard : Nat.card G ≠ 1) :
    ∃ (H : Subgroup G) (f : G →* H) (n : ℕ),
      (∀ h : H, f h.1 = h) ∧
      2 ≤ n ∧
      Monoid.exponent G = n ∧
      Nonempty (H ≃* Multiplicative (ZMod n)) := by
  have hcardgt : 1 < Nat.card G :=
    (Nat.one_lt_iff_ne_zero_and_ne_one).2 ⟨Nat.card_pos.ne', hcard⟩
  letI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hcardgt
  obtain ⟨a, ha⟩ := Monoid.exists_orderOf_eq_exponent
    (Monoid.ExponentExists.of_finite (G := G))
  let H : Subgroup G := Subgroup.zpowers a
  have hHcard : Nat.card H = Monoid.exponent G := by
    exact (Nat.card_zpowers a).trans ha
  obtain ⟨χ, φ, hχ, hext, hrange⟩ :=
    apm_b94J01_exists_extendedFaithfulCharacter_of_cyclic_card_eq_exponent
      G H hHcard
  let f : G →* H := apm_b94J01_retractionOfExtendedFaithfulCharacter
    G H ℂˣ χ hχ φ hrange
  refine ⟨H, f, Monoid.exponent G, ?_, ?_, rfl, ?_⟩
  · exact apm_b94J01_retractionOfExtendedFaithfulCharacter_section
      G H ℂˣ H.subtype χ hχ φ hext hrange
  · exact Monoid.one_lt_exponent
  · exact ⟨(hHcard ▸ zmodCyclicMulEquiv (G := H) (inferInstance : IsCyclic H)).symm⟩

/-- Existence of normalized invariant factors, obtained by repeatedly splitting
off a maximal-order cyclic subgroup. -/
theorem apm_b94J01_invariantFactors_exists_of_card_ne_one
    (G : Type*) [CommGroup G] [Fintype G]
    (_hcard : Nat.card G ≠ 1) :
    ∃ d : List ℕ, apm_b94J01_invariantFactors G d := by
  exact apm_b94J01_invariantFactors_exists_of_splitProducer
    (fun G _ _ hG => apm_b94J01_maximalCyclic_splitProducer G hG) G

/-- Why this unblocks `apm_b94j01`: existence is supplied by the remaining
normalization construction, while uniqueness is the compiled intrinsic theorem
`apm_b94J01_invariantFactors_unique`. -/
theorem apm_b94J01_bridge_1
    (G : Type*) [CommGroup G] [Fintype G]
    (hcard : Nat.card G ≠ 1) :
    ∃! d : List ℕ, apm_b94J01_invariantFactors G d := by
  obtain ⟨d, hd⟩ := apm_b94J01_invariantFactors_exists_of_card_ne_one G hcard
  exact ⟨d, hd, fun e he => apm_b94J01_invariantFactors_unique G e d he hd⟩

theorem apm_b94j01 :
    (∀ (G : Type*) [CommGroup G] [Fintype G],
      ∃! d : List ℕ, apm_b94J01_invariantFactors G d) ∧
    (∀ m n : ℕ, 0 < m → 0 < n →
      (IsCyclic (Multiplicative (ZMod m) × Multiplicative (ZMod n)) ↔
        Nat.Coprime m n)) ∧
    (∀ (K : Type*) [Field K] (G : Subgroup Kˣ) [Finite G], IsCyclic G) := by
  refine ⟨?_, ?_, ?_⟩
  · intro G _ _
    by_cases hcard : Nat.card G = 1
    · exact apm_b94J01_existsUnique_invariantFactors_of_card_eq_one G hcard
    · exact apm_b94J01_bridge_1 G hcard
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
