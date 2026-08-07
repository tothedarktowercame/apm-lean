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
  · -- Boundary: the free-module nonsurjectivity witness above is now complete.
    -- Searches found `IsFractionRing.div_surjective`; this clause still needs
    -- to apply that witness to the image of `1 : K`, explicitly construct in
    -- `K` a solution to every nonzero scalar equation, and then turn “every
    -- nonzero denominator is a unit” into surjectivity of `algebraMap R K`.
    sorry
  constructor
  · -- Boundary: `Module.Projective.iff_split` does realize a projective module
    -- as a direct summand of a free module and supplies the required injective
    -- linear inclusion.  This will reduce to the preceding embedding clause
    -- once that fraction-field divisibility bridge is completed.
    sorry
  constructor
  · -- Boundary: searched `Module.Projective.iff_split_of_projective`, quotient
    -- splitting, and idempotent APIs.  The required result is still the
    -- indecomposability of a domain applied to the split exact sequence
    -- `I → R → R/I`, including conversion of the section to a complementary
    -- ideal/idempotent.
    sorry
  constructor
  · -- Boundary: searched `Submodule.fg_def`,
    -- `IsLocalization.commonDenomOfFinset`, and
    -- `IsLocalization.finsetIntegerMultiple_image`.  These provide the finite
    -- generating set and common denominator, but the remaining bridge is
    -- transporting the image equality through the span representation to all
    -- `m ∈ M` in the abstract `IsFractionRing R K` presentation.
    sorry
  · -- Boundary: this follows from the preceding common-denominator lemma by
    -- taking `M = ⊤`, then using divisibility of the fraction field; that lemma
    -- remains the blocker.
    sorry
