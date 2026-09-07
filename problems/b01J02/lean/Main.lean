import Mathlib

/-!
# APM b01J02: Ideals of `ℤ[x]`

## Statement repairs

None.

## Encoding questions

None. The classification in part (a) is stated as an equivalence for every
ideal of `ℤ[x]`. Reduction modulo `p` is polynomial coefficient mapping
along `Int.castRingHom (ZMod p)`.
-/

open Polynomial

noncomputable section



lemma apm_b01J02_int_isJacobsonRing : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hP0 : P = ⊥
  · subst P
    apply le_antisymm
    · intro x hx
      rw [Ideal.mem_jacobson_bot] at hx
      have hu := hx x
      rw [Int.isUnit_iff] at hu
      simp only [Ideal.mem_bot]
      rcases hu with hu | hu <;> nlinarith
    · exact Ideal.le_jacobson
  · letI : P.IsPrime := hP
    letI : P.IsMaximal := Ideal.IsPrime.isMaximal hP hP0
    exact Ideal.jacobson_eq_self_of_isMaximal

/-- The two-generated ideal `(p, f)` of `ℤ[x]`. -/
def apm_b01J02_twoGeneratedIdeal (p : ℕ) (f : ℤ[X]) : Ideal ℤ[X] :=
  Ideal.span {C (p : ℤ), f}

/-- The ideal `(3, x² + x + 1)` from part (b). -/
def apm_b01J02_nonprimeIdeal : Ideal ℤ[X] :=
  Ideal.span {C 3, X ^ 2 + X + 1}

/-- The ideal `(x)`, used in part (c). -/
def apm_b01J02_xIdeal : Ideal ℤ[X] :=
  Ideal.span {X}

lemma apm_b01J02_xIdeal_eq_ker :
    apm_b01J02_xIdeal = RingHom.ker (Polynomial.evalRingHom (0 : ℤ)) := by
  rw [Polynomial.ker_evalRingHom]
  simp [apm_b01J02_xIdeal]

lemma apm_b01J02_xIdeal_ne_bot : apm_b01J02_xIdeal ≠ ⊥ := by
  intro h
  have hx : X ∈ apm_b01J02_xIdeal := Ideal.subset_span (by simp)
  rw [h] at hx
  simpa using hx

lemma apm_b01J02_xIdeal_isPrime : apm_b01J02_xIdeal.IsPrime := by
  rw [apm_b01J02_xIdeal_eq_ker]
  exact RingHom.ker_isPrime _

lemma apm_b01J02_xIdeal_not_isMaximal : ¬apm_b01J02_xIdeal.IsMaximal := by
  let J : Ideal ℤ[X] := Ideal.span {X, C 2}
  have hle : apm_b01J02_xIdeal ≤ J := by
    rw [apm_b01J02_xIdeal, Ideal.span_le]
    simp only [Set.singleton_subset_iff]
    exact Ideal.subset_span (by simp)
  have hC2J : C (2 : ℤ) ∈ J := Ideal.subset_span (by simp [J])
  have hC2not : C (2 : ℤ) ∉ apm_b01J02_xIdeal := by
    rw [apm_b01J02_xIdeal_eq_ker]
    simp
  have hJne : J ≠ ⊤ := by
    let e : ℤ[X] →+* ZMod 2 := Polynomial.eval₂RingHom (Int.castRingHom (ZMod 2)) 0
    have hJker : J ≤ RingHom.ker e := by
      change Ideal.span {X, C 2} ≤ RingHom.ker e
      rw [Ideal.span_le]
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · simp [e]
      · simpa [e] using (ZMod.natCast_self 2)
    exact ne_top_of_le_ne_top (RingHom.ker_ne_top e) hJker
  intro hmax
  have := hmax.eq_of_le hJne hle
  exact hC2not (this ▸ hC2J)

lemma apm_b01J02_square_mem_nonprimeIdeal :
    (X - 1 : ℤ[X]) * (X - 1) ∈ apm_b01J02_nonprimeIdeal := by
  have hq : X ^ 2 + X + 1 ∈ apm_b01J02_nonprimeIdeal :=
    Ideal.subset_span (by simp [apm_b01J02_nonprimeIdeal])
  have h3 : C (3 : ℤ) ∈ apm_b01J02_nonprimeIdeal :=
    Ideal.subset_span (by simp [apm_b01J02_nonprimeIdeal])
  have hd : X ^ 2 + X + 1 - C 3 * X ∈ apm_b01J02_nonprimeIdeal :=
    sub_mem hq (Ideal.mul_mem_right X _ h3)
  rw [show C (3 : ℤ) = (3 : ℤ[X]) by norm_num] at hd
  convert hd using 1 <;> ring

lemma apm_b01J02_sub_one_not_mem_nonprimeIdeal :
    (X - 1 : ℤ[X]) ∉ apm_b01J02_nonprimeIdeal := by
  let m : ℤ[X] →+* (ZMod 3)[X] := Polynomial.mapRingHom (Int.castRingHom (ZMod 3))
  intro h
  have hm := Ideal.mem_map_of_mem m h
  have hmap3 : m (C (3 : ℤ)) = 0 := by
    dsimp [m]
    rw [Polynomial.map_C]
    rw [← map_zero C]
    apply congrArg C
    exact_mod_cast (ZMod.natCast_self 3)
  have hm' : (X - 1 : (ZMod 3)[X]) ∈ Ideal.span {X ^ 2 + X + 1} := by
    rw [apm_b01J02_nonprimeIdeal, Ideal.map_span] at hm
    simp only [Set.image_insert_eq, Set.image_singleton, hmap3] at hm
    simpa [m] using hm
  have hdvd : (X ^ 2 + X + 1 : (ZMod 3)[X]) ∣ X - 1 :=
    Ideal.mem_span_singleton.mp hm'
  have hne : (X - 1 : (ZMod 3)[X]) ≠ 0 := by
    intro hz
    have hc := congrArg (fun q : (ZMod 3)[X] => q.coeff 1) hz
    simpa [Polynomial.coeff_one] using hc
  have hdeg := Polynomial.natDegree_le_of_dvd hdvd hne
  have hqdeg : (X ^ 2 + X + 1 : (ZMod 3)[X]).natDegree = 2 := by
    norm_num [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  have hldeg : (X - 1 : (ZMod 3)[X]).natDegree = 1 := by
    norm_num [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
  omega

lemma apm_b01J02_maximal_of_prime_irreducible
    (p : ℕ) (f : ℤ[X]) (hp : p.Prime)
    (hf : Irreducible (f.map (Int.castRingHom (ZMod p)))) :
    (apm_b01J02_twoGeneratedIdeal p f).IsMaximal := by
  let c : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let m : ℤ[X] →+* (ZMod p)[X] := Polynomial.mapRingHom c
  have hc : Function.Surjective c := ZMod.ringHom_surjective c
  have hm : Function.Surjective m := Polynomial.map_surjective c hc
  let J : Ideal (ZMod p)[X] := Ideal.span {f.map c}
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (Irreducible (f.map c)) := ⟨by simpa [c] using hf⟩
  have hJ : J.IsMaximal := by
    dsimp [J]
    infer_instance
  have heq : Ideal.comap m J = apm_b01J02_twoGeneratedIdeal p f := by
    rw [show J = Ideal.map m (Ideal.span {f}) by simp [J, m, Ideal.map_span]]
    rw [Ideal.comap_map_of_surjective m hm]
    rw [show Ideal.comap m ⊥ = RingHom.ker m from rfl]
    dsimp only [m]
    rw [Polynomial.ker_mapRingHom]
    dsimp only [c]
    rw [ZMod.ker_intCastRingHom]
    simp [apm_b01J02_twoGeneratedIdeal, Ideal.map_span, Ideal.span_insert, sup_comm]
  rw [← heq]
  exact Ideal.comap_isMaximal_of_surjective m hm

lemma apm_b01J02_exists_prime_irreducible_of_isMaximal
    (I : Ideal ℤ[X]) (hI : I.IsMaximal) :
    ∃ (p : ℕ) (f : ℤ[X]), p.Prime ∧
      Irreducible (f.map (Int.castRingHom (ZMod p))) ∧
      I = apm_b01J02_twoGeneratedIdeal p f := by
  let P : Ideal ℤ := I.comap (C : ℤ →+* ℤ[X])
  have hPmax : P.IsMaximal := by
    letI : I.IsMaximal := hI
    letI : IsJacobsonRing ℤ := apm_b01J02_int_isJacobsonRing
    exact Polynomial.isMaximal_comap_C_of_isJacobsonRing I
  have hPne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hPmax (by
    exact Int.not_isField)
  letI : P.IsPrime := hPmax.isPrime
  letI : NeZero P := ⟨hPne⟩
  let p : ℕ := Ideal.absNorm P
  have hp : p.Prime := Nat.absNorm_under_prime P
  have hP : P = Ideal.span {(p : ℤ)} := by
    simpa [p] using (Int.ideal_span_absNorm_eq_self P).symm
  letI : Fact p.Prime := ⟨hp⟩
  let c : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let m : ℤ[X] →+* (ZMod p)[X] := Polynomial.mapRingHom c
  have hc : Function.Surjective c := ZMod.ringHom_surjective c
  have hm : Function.Surjective m := Polynomial.map_surjective c hc
  have hker : RingHom.ker m ≤ I := by
    dsimp only [m]
    rw [Polynomial.ker_mapRingHom]
    dsimp only [c]
    rw [ZMod.ker_intCastRingHom, ← hP]
    exact Ideal.map_le_iff_le_comap.mpr le_rfl
  let J : Ideal (ZMod p)[X] := Ideal.map m I
  have hJmax : J.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective m hm hI with htop | hmax
    · exfalso
      have hcmap := congrArg (Ideal.comap m) htop
      rw [Ideal.comap_top, Ideal.comap_map_of_surjective m hm,
        show Ideal.comap m ⊥ = RingHom.ker m from rfl, sup_eq_left.mpr hker] at hcmap
      exact hI.ne_top hcmap
    · exact hmax
  let g : (ZMod p)[X] := Submodule.IsPrincipal.generator J
  have hJspan : J = Ideal.span {g} := (Ideal.span_singleton_generator J).symm
  have hJnebot : J ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hJmax
    (Polynomial.not_isField (ZMod p))
  have hg0 : g ≠ 0 := by
    intro hg
    apply hJnebot
    simpa [hJspan, hg]
  have hgirr : Irreducible g := by
    rw [UniqueFactorizationMonoid.irreducible_iff_prime]
    rw [← Ideal.span_singleton_prime hg0]
    rw [← hJspan]
    exact hJmax.isPrime
  obtain ⟨f, hf⟩ := hm g
  refine ⟨p, f, hp, ?_, ?_⟩
  · rw [← hf] at hgirr
    simpa [m, c] using hgirr
  · have hcmap : Ideal.comap m J = I := by
      change Ideal.comap m (Ideal.map m I) = I
      rw [Ideal.comap_map_of_surjective m hm,
        show Ideal.comap m ⊥ = RingHom.ker m from rfl, sup_eq_left.mpr hker]
    have htarget : Ideal.comap m (Ideal.span {m f}) =
        apm_b01J02_twoGeneratedIdeal p f := by
      rw [show Ideal.span {m f} = Ideal.map m (Ideal.span {f}) by
        simp [Ideal.map_span]]
      rw [Ideal.comap_map_of_surjective m hm,
        show Ideal.comap m ⊥ = RingHom.ker m from rfl]
      dsimp only [m]
      rw [Polynomial.ker_mapRingHom]
      dsimp only [c]
      rw [ZMod.ker_intCastRingHom]
      simp [apm_b01J02_twoGeneratedIdeal, Ideal.map_span, Ideal.span_insert, sup_comm]
    rw [← hcmap, hJspan, ← hf, htarget]

lemma apm_b01J02_maximal_classification :
    ∀ I : Ideal ℤ[X],
      I.IsMaximal ↔
        ∃ (p : ℕ) (f : ℤ[X]), p.Prime ∧
          Irreducible (f.map (Int.castRingHom (ZMod p))) ∧
          I = apm_b01J02_twoGeneratedIdeal p f := by
  intro I
  constructor
  · exact apm_b01J02_exists_prime_irreducible_of_isMaximal I
  · rintro ⟨p, f, hp, hf, rfl⟩
    exact apm_b01J02_maximal_of_prime_irreducible p f hp hf

theorem apm_b01j02 :
    (∀ I : Ideal ℤ[X],
      I.IsMaximal ↔
        ∃ (p : ℕ) (f : ℤ[X]), p.Prime ∧
          Irreducible (f.map (Int.castRingHom (ZMod p))) ∧
          I = apm_b01J02_twoGeneratedIdeal p f) ∧
    (let f : ℤ[X] := X - 1
      let g : ℤ[X] := X - 1
      f * g ∈ apm_b01J02_nonprimeIdeal ∧
        f ∉ apm_b01J02_nonprimeIdeal ∧
        g ∉ apm_b01J02_nonprimeIdeal) ∧
    apm_b01J02_xIdeal ≠ ⊥ ∧
    apm_b01J02_xIdeal.IsPrime ∧
    ¬apm_b01J02_xIdeal.IsMaximal := by
  refine ⟨apm_b01J02_maximal_classification, ?_, apm_b01J02_xIdeal_ne_bot,
    apm_b01J02_xIdeal_isPrime, apm_b01J02_xIdeal_not_isMaximal⟩
  dsimp only
  exact ⟨apm_b01J02_square_mem_nonprimeIdeal,
    apm_b01J02_sub_one_not_mem_nonprimeIdeal,
    apm_b01J02_sub_one_not_mem_nonprimeIdeal⟩

#print axioms apm_b01j02
