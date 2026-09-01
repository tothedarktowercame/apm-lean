import Mathlib

/-!
# APM b94J03

## Statement repairs

None.

## Encoding questions

Splitting fields are quantified abstractly through `IsSplittingField`, so the
statement is independent of a chosen construction. They are described by their
base-field degree and Galois group; over `ℝ` the splitting field is additionally
identified with `ℂ`, and over `ZMod 7` its cardinality is identified as `343`.
-/

open Polynomial

/-- The polynomial `X³ - 3` over a field. -/
noncomputable def apm_b94J03_poly (F : Type*) [Field F] : Polynomial F :=
  X ^ 3 - C 3

lemma apm_b94J03_noncube_mod7 : ∀ a : ZMod 7, a ^ 3 ≠ 3 := by decide

lemma apm_b94J03_primitiveRoot_two_mod7 :
    IsPrimitiveRoot (2 : ZMod 7) 3 := by
  have horder : orderOf (2 : ZMod 7) = 3 := by
    apply (orderOf_eq_iff (by norm_num)).2
    constructor
    · decide
    · intro m hm hm0
      interval_cases m <;> decide
  refine ⟨by decide, fun l hl => ?_⟩
  rw [← horder]
  exact orderOf_dvd_of_pow_eq_one hl

/-- A degree-three extension of `ZMod 7` has the expected cardinality. -/
lemma apm_b94J03_card_of_finrank_three
    [Fact (Nat.Prime 7)] (K : Type*) [Field K] [Algebra (ZMod 7) K]
    [Finite K] [FiniteDimensional (ZMod 7) K]
    (hfin : Module.finrank (ZMod 7) K = 3) : Nat.card K = 343 := by
  rw [← FiniteField.pow_finrank_eq_natCard 7 K, hfin]
  norm_num

/-- Over the finite base field, degree three also determines the cardinality
of the Galois automorphism group. -/
lemma apm_b94J03_aut_card_of_finrank_three
    [Fact (Nat.Prime 7)] (K : Type*) [Field K] [Algebra (ZMod 7) K]
    [Finite K] [FiniteDimensional (ZMod 7) K]
    (hfin : Module.finrank (ZMod 7) K = 3) :
    Nat.card (K ≃ₐ[ZMod 7] K) = 3 := by
  rw [IsGalois.card_aut_eq_finrank, hfin]

/-- The finite-field splitting-field conclusion follows from the Kummer
splitting-field theorem because `ZMod 7` contains a primitive cube root. -/
lemma apm_b94J03_finiteField_conclusion
    [Fact (Nat.Prime 7)] (K : Type*) [Field K] [Algebra (ZMod 7) K]
    [IsSplittingField (ZMod 7) K (apm_b94J03_poly (ZMod 7))] :
    Module.finrank (ZMod 7) K = 3 ∧
      Nat.card K = 343 ∧
      Nonempty ((K ≃ₐ[ZMod 7] K) ≃* Multiplicative (ZMod 3)) := by
  letI : IsSplittingField (ZMod 7) K (X ^ 3 - C 3) := by
    simpa [apm_b94J03_poly] using
      (inferInstance : IsSplittingField (ZMod 7) K (apm_b94J03_poly (ZMod 7)))
  have hnoncube := apm_b94J03_noncube_mod7
  have hirr : Irreducible (apm_b94J03_poly (ZMod 7)) := by
    rw [apm_b94J03_poly]
    exact (X_pow_sub_C_irreducible_iff_of_prime (by norm_num : Nat.Prime 3)).2
      hnoncube
  have hζ := apm_b94J03_primitiveRoot_two_mod7
  have hfin : Module.finrank (ZMod 7) K = 3 := by
    apply finrank_of_isSplittingField_X_pow_sub_C
      (hζ := ⟨2, (mem_primitiveRoots (by norm_num : 0 < 3)).2 hζ⟩)
      hirr
  letI : FiniteDimensional (ZMod 7) K :=
    IsSplittingField.finiteDimensional K (X ^ 3 - C 3)
  haveI : Finite K := Module.finite_of_finite (ZMod 7)
  refine ⟨hfin, apm_b94J03_card_of_finrank_three K hfin, ?_⟩
  exact ⟨autEquivZmod hirr K hζ⟩

lemma apm_b94J03_noncube_rat : ∀ a : ℚ, a ^ 3 ≠ 3 := by
  intro a ha
  have hr : aeval a (X ^ 3 - C 3 : ℤ[X]) = 0 := by
    simpa only [map_sub, aeval_X, map_pow, aeval_C, map_ofNat] using sub_eq_zero.mpr ha
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic
    (monic_X_pow_sub_C (3 : ℤ) (by norm_num : 3 ≠ 0)) hr
  rw [hz] at ha
  norm_num at ha
  have ha' : z ^ 3 = (3 : ℤ) := by exact_mod_cast ha
  have hz' : z ≤ 1 ∨ 2 ≤ z := by omega
  rcases hz' with hz' | hz'
  · have hh := (show Odd 3 by decide).strictMono_pow.monotone hz'
    norm_num [ha'] at hh
  · have hh : (2 : ℤ) ^ 3 ≤ z ^ 3 :=
      (show Odd 3 by decide).strictMono_pow.monotone hz'
    rw [ha'] at hh
    norm_num at hh

lemma apm_b94J03_irreducible_rat : Irreducible (apm_b94J03_poly ℚ) := by
  rw [apm_b94J03_poly]
  exact (X_pow_sub_C_irreducible_iff_of_prime (by norm_num : Nat.Prime 3)).2
    apm_b94J03_noncube_rat

lemma apm_b94J03_real_root_card_le_two :
    Fintype.card ((apm_b94J03_poly ℚ).rootSet ℝ) ≤ 2 := by
  have h := Polynomial.card_rootSet_le_derivative (apm_b94J03_poly ℚ)
  have hd : Fintype.card ((derivative (apm_b94J03_poly ℚ)).rootSet ℝ) = 1 := by
    have he : derivative (apm_b94J03_poly ℚ) = C 3 * X ^ 2 := by
      simp [apm_b94J03_poly, derivative_sub, derivative_pow]
    rw [he]
    simp [rootSet_def]
  omega

lemma apm_b94J03_complex_root_card :
    Fintype.card ((apm_b94J03_poly ℚ).rootSet ℂ) = 3 := by
  rw [Polynomial.card_rootSet_eq_natDegree apm_b94J03_irreducible_rat.separable
    (IsAlgClosed.splits _)]
  norm_num [apm_b94J03_poly]

lemma apm_b94J03_separable_real : (apm_b94J03_poly ℝ).Separable := by
  rw [apm_b94J03_poly]
  exact separable_X_pow_sub_C 3 (by norm_num) (by norm_num)

lemma apm_b94J03_real_poly_root_card_le_two :
    Fintype.card ((apm_b94J03_poly ℝ).rootSet ℝ) ≤ 2 := by
  have h := Polynomial.card_rootSet_le_derivative (apm_b94J03_poly ℝ)
  have hd : Fintype.card ((derivative (apm_b94J03_poly ℝ)).rootSet ℝ) = 1 := by
    have he : derivative (apm_b94J03_poly ℝ) = C 3 * X ^ 2 := by
      simp [apm_b94J03_poly, derivative_sub, derivative_pow]
    rw [he]
    simp [rootSet_def]
  omega

/-- Why this unblocks `apm_b94j03`: this is the concrete real splitting-field
model and its conjugation action.  `IsSplittingField.algEquiv` and
`AlgEquiv.autCongr` then transport both conclusions from `ℂ` to every abstract
real splitting field in the main theorem. -/
theorem apm_b94J03_bridge_complex_model :
    IsSplittingField ℝ ℂ (apm_b94J03_poly ℝ) ∧
      Nonempty ((ℂ ≃ₐ[ℝ] ℂ) ≃* Multiplicative (ZMod 2)) := by
  let p := apm_b94J03_poly ℝ
  let S := p.SplittingField
  letI : FiniteDimensional ℝ S := IsSplittingField.finiteDimensional S p
  have halg : Algebra.IsAlgebraic ℝ S := Algebra.IsIntegral.isAlgebraic
  letI : Algebra.IsAlgebraic ℝ S := halg
  have heC : Nonempty (S ≃ₐ[ℝ] ℂ) := by
    rcases Real.nonempty_algEquiv_or S with heR | heC
    · exfalso
      obtain ⟨e⟩ := heR
      letI : IsSplittingField ℝ ℝ p := Polynomial.IsSplittingField.of_algEquiv ℝ p e
      have hs : p.Splits := by simpa using (IsSplittingField.splits ℝ p)
      have hc : Fintype.card (p.rootSet ℝ) = 3 := by
        rw [Polynomial.card_rootSet_eq_natDegree apm_b94J03_separable_real]
        · norm_num [p, apm_b94J03_poly]
        · simpa using hs
      change Fintype.card ((apm_b94J03_poly ℝ).rootSet ℝ) = 3 at hc
      have hl := apm_b94J03_real_poly_root_card_le_two
      omega
    · exact heC
  obtain ⟨eC⟩ := heC
  letI : IsSplittingField ℝ ℂ p := Polynomial.IsSplittingField.of_algEquiv ℂ p eC
  letI : IsGalois ℝ ℂ :=
    IsGalois.of_separable_splitting_field apm_b94J03_separable_real
  have hAut : Nat.card (ℂ ≃ₐ[ℝ] ℂ) = 2 := by
    exact (IsGalois.card_aut_eq_finrank ℝ ℂ).trans Complex.finrank_real_complex
  have hZ : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    simp [Nat.card_eq_fintype_card]
  exact ⟨inferInstance,
    ⟨mulEquivOfPrimeCardEq hAut hZ⟩⟩

/-- Why this unblocks `apm_b94j03`: this is the missing rational cubic
splitting-field theorem.  It combines irreducibility and the nonsquare
discriminant with the faithful action on the three roots to identify both the
degree and the full `S₃` automorphism group. -/
theorem apm_b94J03_bridge_rational_conclusion
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K (apm_b94J03_poly ℚ)] :
    Module.finrank ℚ K = 6 ∧
      Nonempty ((K ≃ₐ[ℚ] K) ≃* Equiv.Perm (Fin 3)) := by
  let p := apm_b94J03_poly ℚ
  letI : Fact ((p.map (algebraMap ℚ ℂ)).Splits) := ⟨IsAlgClosed.splits _⟩
  have hbij : Function.Bijective (Polynomial.Gal.galActionHom p ℂ) := by
    apply Polynomial.Gal.galActionHom_bijective_of_prime_degree'
      apm_b94J03_irreducible_rat
    · norm_num [p, apm_b94J03_poly]
    · rw [apm_b94J03_complex_root_card]
      have := apm_b94J03_real_root_card_le_two
      omega
    · rw [apm_b94J03_complex_root_card]
      omega
  let eroot : p.rootSet ℂ ≃ Fin 3 :=
    Fintype.equivOfCardEq (by simpa [p] using apm_b94J03_complex_root_card)
  let egal : p.Gal ≃* Equiv.Perm (Fin 3) :=
    (MulEquiv.ofBijective (Polynomial.Gal.galActionHom p ℂ) hbij).trans
      (Equiv.permCongrHom eroot)
  let ek : K ≃ₐ[ℚ] p.SplittingField := IsSplittingField.algEquiv K p
  let eaut : (K ≃ₐ[ℚ] K) ≃* Equiv.Perm (Fin 3) := ek.autCongr.trans egal
  letI : FiniteDimensional ℚ K :=
    IsSplittingField.finiteDimensional K (apm_b94J03_poly ℚ)
  letI : IsGalois ℚ K :=
    IsGalois.of_separable_splitting_field apm_b94J03_irreducible_rat.separable
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 6 := by
    rw [Nat.card_congr eaut.toEquiv]
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  refine ⟨?_, ⟨eaut⟩⟩
  rw [← IsGalois.card_aut_eq_finrank]
  exact hcard

theorem apm_b94j03 :
    (∀ (K : Type*) [Field K] [Algebra ℚ K]
      [IsSplittingField ℚ K (apm_b94J03_poly ℚ)],
      Module.finrank ℚ K = 6 ∧
        Nonempty ((K ≃ₐ[ℚ] K) ≃* Equiv.Perm (Fin 3))) ∧
    (∀ (K : Type*) [Field K] [Algebra ℝ K]
      [IsSplittingField ℝ K (apm_b94J03_poly ℝ)],
      Nonempty (K ≃ₐ[ℝ] ℂ) ∧
        Nonempty ((K ≃ₐ[ℝ] K) ≃* Multiplicative (ZMod 2))) ∧
    (∀ [Fact (Nat.Prime 7)] (K : Type*) [Field K] [Algebra (ZMod 7) K]
      [IsSplittingField (ZMod 7) K (apm_b94J03_poly (ZMod 7))],
        Module.finrank (ZMod 7) K = 3 ∧
        Nat.card K = 343 ∧
        Nonempty ((K ≃ₐ[ZMod 7] K) ≃* Multiplicative (ZMod 3))) := by
  -- (Sibling: b03J04)
  /- PASS-1 boundary: `hnoncube7` and `hirr7` now formally prove the key
     finite-field input: `3` is not a cube modulo `7`, hence `X³ - 3` is
     irreducible over `ZMod 7`.  This uses
     `X_pow_sub_C_irreducible_iff_of_prime`.  I searched
     `IsSplittingField.adjoin_rootSet`,
     `IsGalois.of_separable_splitting_field`, the irreducible-cubic and
     Eisenstein APIs, finite-field cardinality/finrank results, and the
     cyclicity of finite-field Galois groups.  The reusable solved artifact
     `b03J04` supplies general root-set/adjoin splitting-field machinery, but
     not the concrete degree or automorphism computations required here.
     I also inspected analogous artifact `b00J01`, but it is skipped rather
     than a solved sibling and is therefore not cited.

     Closer hop 1 compiles the downstream finite-field consequences.
     `apm_b94J03_card_of_finrank_three` derives cardinality `343` from degree
     three via `FiniteField.pow_finrank_eq_natCard`, while
     `apm_b94J03_aut_card_of_finrank_three` derives automorphism-group
     cardinality three via the finite-field `IsGalois` instance and
     `IsGalois.card_aut_eq_finrank`.  Searches of the finite-field
     splitting-field and Kummer APIs found no direct theorem deriving the
     splitting-field degree from `hirr7`: irreducibility controls a root field,
     while splitting still requires the cube-root-of-unity calculation.

     The intended proof must separately
     realize the abstract splitting fields as `ℚ(∛3, ζ₃)`, `ℂ` over `ℝ`, and
     the degree-three extension of `ZMod 7`, including the explicit
     root-of-unity computations.  The remaining bridges are those degree
     computations and the bundled cyclic/permutation `MulEquiv`
     identifications.

     Closer hop 2 finds and applies the previously missed Kummer dependency.
     `finrank_of_isSplittingField_X_pow_sub_C` and `autEquivZmod` apply because
     `2 : ZMod 7` is a primitive cube root of unity.  The compiled helper
     `apm_b94J03_finiteField_conclusion` therefore closes the complete third
     conjunct: degree three, cardinality 343, and the requested bundled cyclic
     Galois-group equivalence.  Only the rational and real splitting-field
     identifications remain.

     Closer hop 3 wires that finite-field helper into the frozen theorem, so
     the sole sorry is now syntactically restricted to the first two
     conjuncts.  Renewed inspection of `IsSplittingField.algEquiv`, real-closed
     field APIs, cubic discriminants, and `AlgEquiv.autCongr` found the
     uniqueness transport once a concrete model is proved, but no theorem
     proving that `ℂ` is the splitting field of this real cubic or constructing
     the rational `S₃` action. -/
  refine ⟨fun K _ _ _ ↦ apm_b94J03_bridge_rational_conclusion K, ?_, ?_⟩
  · intro K _ _ _
    have hmodel := apm_b94J03_bridge_complex_model
    letI : IsSplittingField ℝ ℂ (apm_b94J03_poly ℝ) := hmodel.1
    let e : K ≃ₐ[ℝ] ℂ :=
      (IsSplittingField.algEquiv K (apm_b94J03_poly ℝ)).trans
        (IsSplittingField.algEquiv ℂ (apm_b94J03_poly ℝ)).symm
    exact ⟨⟨e⟩, hmodel.2.map fun ec ↦ e.autCongr.trans ec⟩
  · intro hprime K
    exact apm_b94J03_finiteField_conclusion K

#print axioms apm_b94j03
