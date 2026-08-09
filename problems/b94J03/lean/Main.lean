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

lemma apm_b94J03_noncube_mod7 : ∀ a : ZMod 7, a ^ 3 ≠ 3 := by native_decide

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

/-- Why this unblocks `apm_b94j03`: this is the concrete real splitting-field
model and its conjugation action.  `IsSplittingField.algEquiv` and
`AlgEquiv.autCongr` then transport both conclusions from `ℂ` to every abstract
real splitting field in the main theorem. -/
theorem apm_b94J03_bridge_complex_model :
    IsSplittingField ℝ ℂ (apm_b94J03_poly ℝ) ∧
      Nonempty ((ℂ ≃ₐ[ℝ] ℂ) ≃* Multiplicative (ZMod 2)) := by
  sorry

/-- Why this unblocks `apm_b94j03`: this is the missing rational cubic
splitting-field theorem.  It combines irreducibility and the nonsquare
discriminant with the faithful action on the three roots to identify both the
degree and the full `S₃` automorphism group. -/
theorem apm_b94J03_bridge_rational_conclusion
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K (apm_b94J03_poly ℚ)] :
    Module.finrank ℚ K = 6 ∧
      Nonempty ((K ≃ₐ[ℚ] K) ≃* Equiv.Perm (Fin 3)) := by
  sorry

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
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hnoncube7 : ∀ a : ZMod 7, a ^ 3 ≠ 3 := by native_decide
  have hirr7 : Irreducible (apm_b94J03_poly (ZMod 7)) := by
    rw [apm_b94J03_poly]
    exact (X_pow_sub_C_irreducible_iff_of_prime (by norm_num : Nat.Prime 3)).2 hnoncube7
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
  refine ⟨?_, ?_, ?_⟩
  rotate_left 2
  intro hprime K
  exact apm_b94J03_finiteField_conclusion K
  all_goals sorry
