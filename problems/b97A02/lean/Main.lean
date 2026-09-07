import Mathlib

/-!
# APM b97A02 — affine automorphisms of a finite-field rational function field

## Statement repairs

None.

## Encoding notes

`F` is an arbitrary finite field and `q = Fintype.card F`.  The fixed field is
stated elementwise inside `RatFunc F`; this avoids replacing the actual fixed
field by a cardinality surrogate.  A subfield between `F` and `F(x)` is encoded
as an `IntermediateField F (RatFunc F)`.
-/

open Set

noncomputable def apm_b97a02_affineAutomorphisms
    (F : Type*) [Field F] [Fintype F] :
    Set (RatFunc F ≃ₐ[F] RatFunc F) :=
  {σ | ∃ a b : F, a ≠ 0 ∧
    σ RatFunc.X = algebraMap F (RatFunc F) a * RatFunc.X +
      algebraMap F (RatFunc F) b}

noncomputable def apm_b97a02_invariant
    (F : Type*) [Field F] [Fintype F] : RatFunc F :=
  (RatFunc.X ^ Fintype.card F - RatFunc.X) ^ (Fintype.card F - 1)

/-- The scalar factor introduced by an affine change of variable disappears
after raising to the exponent used in the frozen invariant. -/
lemma apm_b97A02_algebraMap_pow_card_sub_one
    (F : Type*) [Field F] [Fintype F] (a : F) (ha : a ≠ 0) :
    (algebraMap F (RatFunc F) a) ^ (Fintype.card F - 1) = 1 := by
  rw [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha, map_one]

/-- Coefficients are fixed by the cardinal Frobenius, also after embedding in
the rational function field. -/
lemma apm_b97A02_algebraMap_pow_card
    (F : Type*) [Field F] [Fintype F] (a : F) :
    (algebraMap F (RatFunc F) a) ^ Fintype.card F =
      algebraMap F (RatFunc F) a := by
  rw [← map_pow, FiniteField.pow_card]

/-- Lüroth's degree development implies that the rational function field is
finite over every nonconstant intermediate field. -/
lemma apm_b97A02_finite_over_nontrivial_intermediate
    (F : Type*) [Field F]
    (K : IntermediateField F (RatFunc F)) (hK : K ≠ ⊥) :
    Module.Finite K (RatFunc F) := by
  have hX : IsAlgebraic K (RatFunc.X : RatFunc F) :=
    RatFunc.IntermediateField.isAlgebraic_X hK
  letI : FiniteDimensional K
      (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc F))) :=
    IntermediateField.adjoin.finiteDimensional hX.isIntegral
  exact (RatFunc.IntermediateField.adjoinXEquiv K).toLinearEquiv.finiteDimensional

/-- Every nondegenerate affine change of variable is realized by an algebra
automorphism of the rational function field.  Lüroth's
`algEquivOfTranscendental` supplies the map to the simple adjoin; solving the
affine equation for `X` shows that this adjoin is the whole field. -/
lemma apm_b97A02_exists_affineAlgEquiv
    (F : Type*) [Field F] (a b : F) (ha : a ≠ 0) :
    ∃ σ : RatFunc F ≃ₐ[F] RatFunc F,
      σ RatFunc.X = algebraMap F (RatFunc F) a * RatFunc.X +
        algebraMap F (RatFunc F) b := by
  let f : RatFunc F := algebraMap F (RatFunc F) a * RatFunc.X +
    algebraMap F (RatFunc F) b
  have hX : ¬ ∃ c : F, (RatFunc.X : RatFunc F) = RatFunc.C c := by
    rw [RatFunc.eq_C_iff]
    simp
  have hma : algebraMap F (RatFunc F) a ≠ 0 :=
    (map_ne_zero (algebraMap F (RatFunc F))).2 ha
  have hsolve : (RatFunc.X : RatFunc F) =
      algebraMap F (RatFunc F) a⁻¹ *
        (f - algebraMap F (RatFunc F) b) := by
    dsimp [f]
    rw [map_inv₀]
    calc
      RatFunc.X = (algebraMap F (RatFunc F) a)⁻¹ *
          (algebraMap F (RatFunc F) a * RatFunc.X) := by
            rw [← mul_assoc, inv_mul_cancel₀ hma, one_mul]
      _ = (algebraMap F (RatFunc F) a)⁻¹ *
          (algebraMap F (RatFunc F) a * RatFunc.X +
            algebraMap F (RatFunc F) b - algebraMap F (RatFunc F) b) := by ring
  have hf : ¬ ∃ c : F, f = RatFunc.C c := by
    rintro ⟨c, hc⟩
    apply hX
    refine ⟨a⁻¹ * (c - b), ?_⟩
    rw [hsolve, hc, ← RatFunc.algebraMap_eq_C]
    simp only [← map_sub, ← map_mul]
  have hadjoin : IntermediateField.adjoin F ({f} : Set (RatFunc F)) = ⊤ := by
    apply le_antisymm le_top
    rw [← RatFunc.adjoin_X]
    apply IntermediateField.adjoin_le_iff.mpr
    rw [Set.singleton_subset_iff]
    rw [hsolve]
    exact IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.sub_mem _
        (IntermediateField.subset_adjoin F ({f} : Set (RatFunc F))
          (Set.mem_singleton f))
        (IntermediateField.algebraMap_mem _ _))
  let e : RatFunc F ≃ₐ[F] RatFunc F :=
    (RatFunc.algEquivOfTranscendental f (f.transcendental_of_ne_C hf)).trans
      ((IntermediateField.equivOfEq hadjoin).trans IntermediateField.topEquiv)
  refine ⟨e, ?_⟩
  change e RatFunc.X = f
  simp [e, RatFunc.algEquivOfTranscendental_X]

/-- An algebra homomorphism out of a rational-function field is determined by
its value on `X`.  This is the fraction-field extensionality lemma missing
from the public `RatFunc` API: polynomial values follow from `aeval`
functoriality, and
`RatFunc.induction_on'` reduces an arbitrary rational function to a quotient
of two such polynomial values. -/
lemma apm_b97A02_ratFunc_algHom_ext
    (F : Type*) [Field F]
    (φ ψ : RatFunc F →ₐ[F] RatFunc F)
    (hX : φ RatFunc.X = ψ RatFunc.X) : φ = ψ := by
  ext x
  induction x using RatFunc.induction_on' with
  | _ p q hq =>
      rw [RatFunc.mk_eq_div, map_div₀, map_div₀]
      rw [← RatFunc.aeval_X_left_eq_algebraMap p,
        ← RatFunc.aeval_X_left_eq_algebraMap q,
        ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply,
        ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply, hX]

/-- Equality of affine-linear rational functions remembers both coefficients. -/
lemma apm_b97A02_affine_parameters_injective
    (F : Type*) [Field F] (a b c d : F)
    (h : algebraMap F (RatFunc F) a * RatFunc.X + algebraMap F (RatFunc F) b =
      algebraMap F (RatFunc F) c * RatFunc.X + algebraMap F (RatFunc F) d) :
    a = c ∧ b = d := by
  have hp : Polynomial.C a * Polynomial.X + Polynomial.C b =
      Polynomial.C c * Polynomial.X + Polynomial.C d := by
    apply RatFunc.algebraMap_injective F
    simpa [← RatFunc.algebraMap_eq_C] using h
  constructor
  · have hx := congrArg (fun p : Polynomial F => p.coeff 1) hp
    simpa using hx
  · have hc := congrArg (fun p : Polynomial F => p.coeff 0) hp
    simpa using hc

/-- A canonical affine automorphism for each nonzero slope and intercept. -/
noncomputable def apm_b97A02_affineEquiv
    (F : Type*) [Field F] (p : {a : F // a ≠ 0} × F) :
    RatFunc F ≃ₐ[F] RatFunc F :=
  Classical.choose (apm_b97A02_exists_affineAlgEquiv F p.1 p.2 p.1.property)

lemma apm_b97A02_affineEquiv_X
    (F : Type*) [Field F] (p : {a : F // a ≠ 0} × F) :
    apm_b97A02_affineEquiv F p RatFunc.X =
      algebraMap F (RatFunc F) p.1 * RatFunc.X + algebraMap F (RatFunc F) p.2 :=
  Classical.choose_spec (apm_b97A02_exists_affineAlgEquiv F p.1 p.2 p.1.property)

lemma apm_b97A02_affineEquiv_injective
    (F : Type*) [Field F] : Function.Injective (apm_b97A02_affineEquiv F) := by
  intro p q hpq
  have hX := congrArg (fun σ : RatFunc F ≃ₐ[F] RatFunc F => σ RatFunc.X) hpq
  dsimp only at hX
  rw [apm_b97A02_affineEquiv_X, apm_b97A02_affineEquiv_X] at hX
  obtain ⟨ha, hb⟩ := apm_b97A02_affine_parameters_injective F _ _ _ _ hX
  exact Prod.ext (Subtype.ext ha) hb

lemma apm_b97A02_affineAutomorphisms_eq_range
    (F : Type*) [Field F] [Fintype F] :
    apm_b97a02_affineAutomorphisms F = Set.range (apm_b97A02_affineEquiv F) := by
  ext σ
  constructor
  · rintro ⟨a, b, ha, hσ⟩
    refine ⟨(⟨a, ha⟩, b), ?_⟩
    apply AlgEquiv.ext
    intro x
    have hhom := apm_b97A02_ratFunc_algHom_ext F σ.toAlgHom
      (apm_b97A02_affineEquiv F (⟨a, ha⟩, b)).toAlgHom
      (hσ.trans (apm_b97A02_affineEquiv_X F (⟨a, ha⟩, b)).symm)
    exact (congrArg (fun f : RatFunc F →ₐ[F] RatFunc F => f x) hhom).symm
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, p.1.property, apm_b97A02_affineEquiv_X F p⟩

lemma apm_b97A02_natCard_nonzero
    (F : Type*) [Field F] [Fintype F] :
    Nat.card {a : F // a ≠ 0} = Fintype.card F - 1 := by
  classical
  have h := Set.ncard_subtype (fun a : F => a ≠ 0) (Set.univ : Set F)
  simp only [Set.mem_univ, Set.setOf_true, Set.univ_inter] at h
  rw [← Set.ncard_univ {a : F // a ≠ 0}, h]
  rw [show {a : F | a ≠ 0} = ({0} : Set F)ᶜ by ext; simp]
  rw [Set.ncard_compl]
  simp

/-- The additive polynomial `X^q - X` transforms by the affine slope. -/
lemma apm_b97A02_affine_frobenius_sub
    (F : Type*) [Field F] [Fintype F] (a b : F) :
    (algebraMap F (RatFunc F) a * RatFunc.X +
        algebraMap F (RatFunc F) b) ^ Fintype.card F -
      (algebraMap F (RatFunc F) a * RatFunc.X +
        algebraMap F (RatFunc F) b) =
      algebraMap F (RatFunc F) a *
        (RatFunc.X ^ Fintype.card F - RatFunc.X) := by
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  letI : Fact (Nat.Prime (ringChar F)) := ⟨hp⟩
  have hadd (x y : RatFunc F) :
      (x + y) ^ Fintype.card F =
        x ^ Fintype.card F + y ^ Fintype.card F := by
    rw [hcard]
    exact add_pow_char_pow x y (ringChar F) n
  rw [hadd, mul_pow, apm_b97A02_algebraMap_pow_card,
    apm_b97A02_algebraMap_pow_card]
  ring

/-- Every affine automorphism in the frozen set fixes the proposed invariant. -/
lemma apm_b97A02_affine_fixes_invariant
    (F : Type*) [Field F] [Fintype F]
    (σ : RatFunc F ≃ₐ[F] RatFunc F)
    (hσ : σ ∈ apm_b97a02_affineAutomorphisms F) :
    σ (apm_b97a02_invariant F) = apm_b97a02_invariant F := by
  obtain ⟨a, b, ha, hX⟩ := hσ
  simp only [apm_b97a02_invariant, map_pow, map_sub, hX]
  rw [apm_b97A02_affine_frobenius_sub, mul_pow,
    apm_b97A02_algebraMap_pow_card_sub_one F a ha, one_mul]

/-- Consequently the entire intermediate field generated by the invariant is
fixed pointwise by every affine automorphism. -/
lemma apm_b97A02_adjoin_invariant_fixed
    (F : Type*) [Field F] [Fintype F]
    (σ : RatFunc F ≃ₐ[F] RatFunc F)
    (hσ : σ ∈ apm_b97a02_affineAutomorphisms F)
    (r : RatFunc F)
    (hr : r ∈ IntermediateField.adjoin F
      ({apm_b97a02_invariant F} : Set (RatFunc F))) :
    σ r = r := by
  induction hr using IntermediateField.adjoin_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff.mp hx]
      exact apm_b97A02_affine_fixes_invariant F σ hσ
  | algebraMap x => exact σ.commutes x
  | add x y _ _ hx hy => simpa using congrArg₂ (· + ·) hx hy
  | inv x _ hx => simpa using congrArg Inv.inv hx
  | mul x y _ _ hx hy => simpa using congrArg₂ (· * ·) hx hy

lemma apm_b97A02_invariant_finrank
    (F : Type*) [Field F] [Fintype F] :
    Module.finrank
      (IntermediateField.adjoin F ({apm_b97a02_invariant F} : Set (RatFunc F)))
      (RatFunc F) = Fintype.card F * (Fintype.card F - 1) := by
  rw [RatFunc.finrank_eq_max_natDegree]
  rw [show apm_b97a02_invariant F = algebraMap (Polynomial F) (RatFunc F)
      ((Polynomial.X ^ Fintype.card F - Polynomial.X) ^
        (Fintype.card F - 1)) by simp [apm_b97a02_invariant]]
  rw [RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
  exact Nat.mul_comm _ _

noncomputable def apm_b97A02_affineEquivOverInvariant
    (F : Type*) [Field F] [Fintype F]
    (p : {a : F // a ≠ 0} × F) :
    RatFunc F ≃ₐ[IntermediateField.adjoin F
      ({apm_b97a02_invariant F} : Set (RatFunc F))] RatFunc F :=
  AlgEquiv.ofRingEquiv (f := (apm_b97A02_affineEquiv F p).toRingEquiv) (by
    intro x
    exact apm_b97A02_adjoin_invariant_fixed F (apm_b97A02_affineEquiv F p)
      ⟨p.1, p.2, p.1.property, apm_b97A02_affineEquiv_X F p⟩ x x.property)

lemma apm_b97A02_affineEquivOverInvariant_injective
    (F : Type*) [Field F] [Fintype F] :
    Function.Injective (apm_b97A02_affineEquivOverInvariant F) := by
  intro p q h
  apply apm_b97A02_affineEquiv_injective F
  ext x
  simpa [apm_b97A02_affineEquivOverInvariant] using congrArg (fun e => e x) h

lemma apm_b97A02_affineEquivOverInvariant_surjective
    (F : Type*) [Field F] [Fintype F] :
    Function.Surjective (apm_b97A02_affineEquivOverInvariant F) := by
  let K := IntermediateField.adjoin F
    ({apm_b97a02_invariant F} : Set (RatFunc F))
  have hdegree : Module.finrank K (RatFunc F) =
      Fintype.card F * (Fintype.card F - 1) :=
    apm_b97A02_invariant_finrank F
  letI : FiniteDimensional K (RatFunc F) :=
    FiniteDimensional.of_finrank_pos (by
      rw [hdegree]
      exact Nat.mul_pos Fintype.card_pos (Nat.sub_pos_of_lt Fintype.one_lt_card))
  have hbij : Function.Bijective (apm_b97A02_affineEquivOverInvariant F) :=
    (Nat.bijective_iff_injective_and_card
      (apm_b97A02_affineEquivOverInvariant F)).mpr (by
      constructor
      · exact apm_b97A02_affineEquivOverInvariant_injective F
      · apply le_antisymm
        · rw [Nat.card_prod, apm_b97A02_natCard_nonzero]
          have hle := Nat.card_le_card_of_injective
              (apm_b97A02_affineEquivOverInvariant F)
              (apm_b97A02_affineEquivOverInvariant_injective F)
          rw [Nat.card_prod, apm_b97A02_natCard_nonzero] at hle
          simpa [Nat.card_eq_fintype_card] using hle
        · rw [Nat.card_prod, apm_b97A02_natCard_nonzero]
          simpa [hdegree, Nat.mul_comm] using
            AlgEquiv.card_le (F := K) (K := RatFunc F))
  exact hbij.2

theorem apm_b97a02 (F : Type*) [Field F] [Fintype F] :
    (∀ a b : F, a ≠ 0 →
      ∃! σ : RatFunc F ≃ₐ[F] RatFunc F,
        σ RatFunc.X = algebraMap F (RatFunc F) a * RatFunc.X +
          algebraMap F (RatFunc F) b) ∧
    Set.ncard (apm_b97a02_affineAutomorphisms F) =
      Fintype.card F * (Fintype.card F - 1) ∧
    (∀ r : RatFunc F,
      (∀ σ ∈ apm_b97a02_affineAutomorphisms F, σ r = r) ↔
        r ∈ IntermediateField.adjoin F
          ({apm_b97a02_invariant F} : Set (RatFunc F))) ∧
    (∀ K : IntermediateField F (RatFunc F), K ≠ ⊥ →
      Module.Finite K (RatFunc F)) := by
  refine ⟨?_, ?_, ?_, apm_b97A02_finite_over_nontrivial_intermediate F⟩
  /-
  PARTIAL boundary (closer hop 2): the finite-field coefficient arithmetic
  needed by the invariant calculation is now compiled above.
  `apm_b97A02_algebraMap_pow_card` handles Frobenius-fixed coefficients, and
  `apm_b97A02_algebraMap_pow_card_sub_one` proves that the nonzero affine
  scaling factor disappears at exponent `q-1`.

  Closer hop 2 found that `FieldTheory/RatFunc/Luroth.lean` is present in this
  snapshot despite the earlier bounded search missing it. The new compiled
  lemma `apm_b97A02_finite_over_nontrivial_intermediate` uses
  `RatFunc.IntermediateField.isAlgebraic_X`, finite dimensionality of a simple
  algebraic adjoin, and `RatFunc.IntermediateField.adjoinXEquiv` to close the
  theorem's entire last conjunct. The main proof now supplies that conjunct
  outside the remaining goals.

  The same source also provides `RatFunc.algEquivOfTranscendental` and
  `RatFunc.finrank_eq_max_natDegree`, correcting two earlier API-negative
  findings. For affine `aX+b`, closure can use the former after proving
  transcendence and `F⟮aX+b⟯ = ⊤`; the latter supplies the degree calculation
  needed after the automorphism action has been assembled. That construction,
  uniqueness, finite action count, and fixed-field equality remain open.

  Earlier local Mathlib source search found the
  low-level constructors `RatFunc.liftRingHom` and `RatFunc.liftAlgHom`, and
  the general fixed-field API `IntermediateField.fixedField`, but no packaged
  affine-substitution `AlgEquiv` for `RatFunc`, no theorem that such maps are
  determined by `RatFunc.X`, and no rational-function degree formula proving
  `[F(X) : F(t)] = max (degree numerator) (degree denominator)`.

  The available `IntermediateField.finrank_fixedField_eq_card` machinery
  assumes a finite-dimensional ambient extension and therefore does not apply
  directly to `F ⊂ F(X)`. Consequently the fixed-field identification still
  requires connecting the finite affine action to the newly found degree
  theorem. Searches of proved sibling artifacts found no implementation. The
  statement appears mathematically sound; this is an API/formalization blocker.

  CLOSER HOP 3: `apm_b97A02_exists_affineAlgEquiv` now constructs the affine
  substitution automorphism for every `a ≠ 0`. It explicitly solves
  `X = a⁻¹ ((aX+b)-b)`, uses this to prove `F⟮aX+b⟯ = ⊤`, rules out the affine
  expression being constant, and applies `RatFunc.algEquivOfTranscendental`
  followed by `IntermediateField.equivOfEq` and `topEquiv`. Its application
  lemma then gives exactly `σ X = aX+b`. Thus existence in the first frozen
  conjunct is complete; only uniqueness of an `F`-algebra automorphism from
  its value on `X` remains there.

  Searches beyond hop 2 covered the Lüroth equivalence implementation,
  `RatFunc.eq_C_iff`, `RatFunc.adjoin_X`, intermediate-field adjoin induction,
  and low-level `liftAlgHom` extensionality. The first group supplied the
  construction above. No packaged extensionality theorem for `RatFunc`
  algebra homomorphisms was found, so uniqueness, action counting, invariant
  fixedness, and the fixed-field degree comparison remain open.
  -/
  · intro a b ha
    obtain ⟨σ, hσ⟩ := apm_b97A02_exists_affineAlgEquiv F a b ha
    refine ⟨σ, hσ, ?_⟩
    intro τ hτ
    apply AlgEquiv.ext
    have hhom := apm_b97A02_ratFunc_algHom_ext F σ.toAlgHom τ.toAlgHom
      (hσ.trans hτ.symm)
    exact fun x => congrArg (fun f : RatFunc F →ₐ[F] RatFunc F => f x) hhom.symm
  · rw [apm_b97A02_affineAutomorphisms_eq_range,
      Set.ncard_range_of_injective (apm_b97A02_affineEquiv_injective F),
      Nat.card_prod, apm_b97A02_natCard_nonzero]
    simpa using Nat.mul_comm (Fintype.card F - 1) (Fintype.card F)
  · intro r
    constructor
    · intro hfixed
      let K := IntermediateField.adjoin F
        ({apm_b97a02_invariant F} : Set (RatFunc F))
      have hdegree : Module.finrank K (RatFunc F) =
          Fintype.card F * (Fintype.card F - 1) :=
        apm_b97A02_invariant_finrank F
      letI : FiniteDimensional K (RatFunc F) :=
        FiniteDimensional.of_finrank_pos (by
          rw [hdegree]
          exact Nat.mul_pos Fintype.card_pos
            (Nat.sub_pos_of_lt Fintype.one_lt_card))
      have hbij : Function.Bijective
          (apm_b97A02_affineEquivOverInvariant F) :=
        ⟨apm_b97A02_affineEquivOverInvariant_injective F,
          apm_b97A02_affineEquivOverInvariant_surjective F⟩
      have hcard := ((Nat.bijective_iff_injective_and_card
        (apm_b97A02_affineEquivOverInvariant F)).mp hbij).2
      have haut : Nat.card
          (RatFunc F ≃ₐ[K] RatFunc F) = Module.finrank K (RatFunc F) := by
        calc
          Nat.card (RatFunc F ≃ₐ[K] RatFunc F) =
              Nat.card ({a : F // a ≠ 0} × F) := by simpa [K] using hcard.symm
          _ = Fintype.card F * (Fintype.card F - 1) := by
            rw [Nat.card_prod, apm_b97A02_natCard_nonzero]
            simp [Nat.mul_comm]
          _ = Module.finrank K (RatFunc F) := hdegree.symm
      letI : IsGalois K (RatFunc F) :=
        IsGalois.of_card_aut_eq_finrank K (RatFunc F) haut
      have hr : r ∈ IntermediateField.fixedField
          (⊤ : Subgroup (RatFunc F ≃ₐ[K] RatFunc F)) := by
        rw [IntermediateField.mem_fixedField_iff]
        intro τ hτ
        obtain ⟨p, rfl⟩ := apm_b97A02_affineEquivOverInvariant_surjective F τ
        exact hfixed (apm_b97A02_affineEquiv F p)
          ⟨p.1, p.2, p.1.property, apm_b97A02_affineEquiv_X F p⟩
      rw [IsGalois.fixedField_top] at hr
      rw [IntermediateField.mem_bot] at hr
      obtain ⟨k, hk⟩ := hr
      change r ∈ K
      change (k : RatFunc F) = r at hk
      rw [← hk]
      exact k.property
    · intro hr σ hσ
      exact apm_b97A02_adjoin_invariant_fixed F σ hσ r hr

#print axioms apm_b97a02


  /-
  F84 round 1 closes the affine-action cardinality.  The canonical-choice map
  from a nonzero slope and an intercept has precisely the frozen affine set as
  its range.  Injectivity is reduced to equality of two degree-one polynomials
  through `RatFunc.algebraMap_injective`, then read at coefficients zero and
  one.  `Set.ncard_range_of_injective` and a complement count for the nonzero
  subtype yield `q * (q - 1)`.  Thus only the fixed-field equivalence remains.
  -/
  /-
  HOP 4 closes the specifically identified Mathlib gap with the local theorem
  `apm_b97A02_ratFunc_algHom_ext`, proved by `RatFunc.induction_on'`,
  `RatFunc.mk_eq_div`, and polynomial `aeval` functoriality.  It is used above
  to close the complete uniqueness conjunct.  The remaining placeholder is
  not extensionality: it consists of the affine-action cardinality and the
  fixed-field identification (including the degree comparison described in
  the earlier boundary).
  -/
