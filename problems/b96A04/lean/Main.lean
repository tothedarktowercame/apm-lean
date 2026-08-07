import Mathlib

/-!
# APM b96A04: Module-theoretic rigidity of a fraction field

## Statement repairs

Part (a) is false when `y = 0`, since then `d * y ∣ y` for every `d`.
We add the intended hypothesis `y ≠ 0`, which is also used by the supplied
informal solution.

## Encoding questions

None. The equality `R = K` is represented invariantly by surjectivity of
`algebraMap R K`, since `R` and its fraction field may be distinct Lean types.
-/

open scoped Pointwise

noncomputable section

private theorem fraction_surjective_of_free_embedding
    (R K : Type) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (F : Type) [AddCommGroup F] [Module R F] [Module.Free R F]
    (i : K →ₗ[R] F) (hi : Function.Injective i) :
    Function.Surjective (algebraMap R K) := by
  intro z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R z
  have hbK : algebraMap R K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hbu : IsUnit b := by
    let B := Module.Free.chooseBasis R F
    have hi_one : i (1 : K) ≠ 0 := fun h => one_ne_zero (hi (by simpa using h))
    have hrepr : B.repr (i (1 : K)) ≠ 0 := by
      simpa using B.repr.injective.ne hi_one
    obtain ⟨j, hj⟩ : ∃ j, B.repr (i (1 : K)) j ≠ 0 := by
      by_contra h
      push_neg at h
      apply hrepr
      ext k
      exact h k
    rw [isUnit_iff_exists_inv]
    refine ⟨B.repr (i ((algebraMap R K (b * B.repr (i 1) j))⁻¹)) j, ?_⟩
    apply mul_right_cancel₀ hj
    have hjK : algebraMap R K (B.repr (i 1) j) ≠ 0 := by
      intro h
      apply hj
      exact IsFractionRing.injective R K (by simpa using h)
    have hbaK : algebraMap R K (b * B.repr (i 1) j) ≠ 0 := by
      rw [map_mul]
      exact mul_ne_zero hbK hjK
    have hy : (b * B.repr (i 1) j) •
        i ((algebraMap R K (b * B.repr (i 1) j))⁻¹) = i (1 : K) := by
      rw [← i.map_smul]
      congr 1
      rw [Algebra.smul_def]
      exact mul_inv_cancel₀ hbaK
    have hcoord := congrArg (fun q => B.repr q j) hy
    simpa [mul_assoc, mul_comm, mul_left_comm] using hcoord
  rw [isUnit_iff_exists_inv] at hbu
  obtain ⟨c, hc⟩ := hbu
  refine ⟨a * c, ?_⟩
  have hcK : algebraMap R K b * algebraMap R K c = 1 := by
    simpa [map_mul] using congrArg (algebraMap R K) hc
  rw [map_mul, div_eq_mul_inv, (inv_eq_of_mul_eq_one_right hcK).symm]

theorem apm_b96a04
    (R K : Type) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    (∀ y d : R, y ≠ 0 → d * y ∣ y → IsUnit d) ∧
    (∀ (F : Type) [AddCommGroup F] [Module R F] [Module.Free R F],
      (∀ (m : F) (r : R), m ≠ 0 → r • m = 0 → r = 0) ∧
      ∀ (m : F), m ≠ 0 → ∀ d : R, d ≠ 0 → ¬IsUnit d →
        ∃ x : R, x ≠ 0 ∧ ¬∃ y : F, (d * x) • y = m) ∧
    (∀ (F : Type) [AddCommGroup F] [Module R F] [Module.Free R F],
      (∃ i : K →ₗ[R] F, Function.Injective i) →
        Function.Surjective (algebraMap R K)) ∧
    (Module.Projective R K → Function.Surjective (algebraMap R K)) ∧
    (∀ I : Ideal R, I ≠ ⊤ → Module.Projective R (R ⧸ I) → I = ⊥) ∧
    (∀ M : Submodule R K,
      (∀ a : R, algebraMap R K a ∈ M) → M.FG →
        ∃ r : R, r ≠ 0 ∧
          ∀ m ∈ M, r • m ∈ Set.range (algebraMap R K)) ∧
    (Module.Finite R K → Function.Surjective (algebraMap R K)) := by
  constructor
  · intro y d hy hd
    obtain ⟨c, hc⟩ := hd
    rw [isUnit_iff_exists_inv]
    refine ⟨c, ?_⟩
    apply mul_left_cancel₀ hy
    simpa [mul_assoc, mul_left_comm] using hc.symm
  constructor
  · intro F _ _ _
    constructor
    · intro m r hm hr
      exact (smul_eq_zero.mp hr).resolve_right hm
    · intro m hm d hd hdu
      let b := Module.Free.chooseBasis R F
      have hrepr : b.repr m ≠ 0 := by
        simpa using b.repr.injective.ne hm
      obtain ⟨j, hj⟩ : ∃ j, b.repr m j ≠ 0 := by
        by_contra h
        push_neg at h
        apply hrepr
        ext i
        exact h i
      refine ⟨b.repr m j, hj, ?_⟩
      rintro ⟨y, hy⟩
      apply hdu
      rw [isUnit_iff_exists_inv]
      refine ⟨b.repr y j, ?_⟩
      apply mul_left_cancel₀ hj
      have hcoord := congrArg (fun q => b.repr q j) hy
      simpa [mul_assoc, mul_left_comm] using hcoord
  constructor
  · rintro F _ _ _ ⟨i, hi⟩
    exact fraction_surjective_of_free_embedding R K F i hi
  constructor
  · intro hK
    obtain ⟨F, _, _, _, i, s, his⟩ := Module.Projective.iff_split.mp hK
    letI : AddCommGroup F := Module.addCommMonoidToAddCommGroup R
    apply fraction_surjective_of_free_embedding R K F i
    exact LinearMap.injective_of_comp_eq_id i s his
  constructor
  · -- Boundary (closer hop 1): searched `Module.Projective.iff_split_of_projective`, quotient
    -- splitting, and idempotent APIs.  The required result is still the
    -- indecomposability of a domain applied to the split exact sequence
    -- `I → R → R/I`, including conversion of the section to a complementary
    -- ideal/idempotent.  This hop also searched the projective-module and ideal
    -- libraries for a packaged `Projective R (R ⧸ I) → I = ⊥` theorem or an
    -- ideal generated by an idempotent theorem.  Only the semisimple-ring result
    -- `IsSemisimpleRing.ideal_eq_span_idempotent` was found, whose hypotheses do
    -- not apply.  The remaining local route is to extract a section with
    -- `Projective.iff_split`, set `e = s 1`, prove `e² = e` and `I = span {1-e}`,
    -- then use that a domain has only trivial idempotents.
    sorry
  constructor
  · -- Boundary (closer hop 1): searched `Submodule.fg_def`,
    -- `IsLocalization.commonDenomOfFinset`, and
    -- `IsLocalization.finsetIntegerMultiple_image`.  These provide the finite
    -- generating set and common denominator, but the remaining bridge is
    -- transporting the image equality through the span representation to all
    -- `m ∈ M` in the abstract `IsFractionRing R K` presentation.
    -- This hop found the closely related proved theorem
    -- `IsLocalization.smul_mem_finsetIntegerMultiple_span` in
    -- `RingTheory/Localization/Finiteness.lean`; it clears denominators for an
    -- element already known to lie in a finite span.  Applying it uniformly to
    -- the finite generating set of `M` still requires unpacking `M.FG` and
    -- reconciling the `nonZeroDivisors R` scalar with the required `r : R`.
    sorry
  · -- Boundary (closer hop 1): this follows from the preceding common-denominator lemma by
    -- taking `M = ⊤`, then using divisibility of the fraction field; that lemma
    -- remains the blocker.  A search for a packaged theorem that a fraction
    -- field finite as a module forces `IsField R` returned none;
    -- `IsFractionRing.surjective_iff_isField` only converts the final result.
    sorry
