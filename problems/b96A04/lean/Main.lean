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
    · -- Boundary: searched `Module.Free.exists_basis`, coordinate maps, and
      -- `smul_eq_zero`.  Completing the quantified witness requires choosing a
      -- nonzero basis coordinate of `m` and transporting unsolvability back
      -- through the basis representation.
      sorry
  constructor
  · -- Boundary: searched `IsFractionRing.div_surjective` and projective/free
    -- embedding APIs.  This clause depends on the preceding missing free-module
    -- nonsurjectivity witness plus denominator division inside `K`.
    sorry
  constructor
  · -- Boundary: searched `Module.Projective` realization-as-a-summand/free
    -- module APIs; no direct embedding theorem into a free module was found.
    sorry
  constructor
  · -- Boundary: searched projective quotient splitting and idempotent-ideal
    -- APIs.  The required result is the indecomposability of a domain applied
    -- to a split exact sequence `I → R → R/I`.
    sorry
  constructor
  · -- Boundary: searched `IsLocalization.commonDenomOfFinset`,
    -- `finsetIntegerMultiple_image`, and `Submodule.FG`.  The missing bridge is
    -- extracting a finite generating set and clearing its denominators in the
    -- abstract `IsFractionRing R K` presentation.
    sorry
  · -- Boundary: this follows from the preceding common-denominator lemma by
    -- taking `M = ⊤`, then using divisibility of the fraction field; that lemma
    -- remains the blocker.
    sorry
