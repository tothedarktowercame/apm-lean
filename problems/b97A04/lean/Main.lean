import Mathlib

/-!
# APM b97A04 — a faithful simple module over a finite-dimensional complex algebra

## Statement repairs

None.

## Encoding notes

Faithfulness is written in the elementwise form given in the source.  The
division-algebra conclusion says directly that every nonzero `R`-linear
endomorphism is a unit.  The description of a general module is the direct-sum
form `ι →₀ V`, allowing arbitrary rather than only finite-dimensional modules.
-/

theorem apm_b97a04
    (R V : Type) [Ring R] [AddCommGroup V]
    [Algebra ℂ R] [Module ℂ V] [Module R V]
    [IsScalarTower ℂ R V] [SMulCommClass ℂ R V]
    [FiniteDimensional ℂ R] [IsSimpleModule R V]
    (hfaithful : ∀ r : R, (∀ v : V, r • v = 0) → r = 0) :
    Module.Finite ℂ V ∧
    (∀ φ : Module.End R V, φ ≠ 0 → IsUnit φ) ∧
    Module.Finite ℂ (Module.End R V) ∧
    (∀ φ : Module.End R V,
      ∃ c : ℂ, φ = c • LinearMap.id) ∧
    Nonempty (R ≃ₐ[ℂ] Module.End ℂ V) ∧
    (∀ (W : Type) [AddCommGroup W] [Module R W],
      ∃ (ι : Type), Nonempty (W ≃ₗ[R] (ι →₀ V))) := by
  sorry
