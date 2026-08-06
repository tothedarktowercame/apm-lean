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
  sorry
