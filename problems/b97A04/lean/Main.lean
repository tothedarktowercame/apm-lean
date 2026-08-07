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

lemma apm_b97a04_module_finite
    (R V : Type) [Ring R] [AddCommGroup V]
    [Algebra ℂ R] [Module ℂ V] [Module R V]
    [IsScalarTower ℂ R V] [FiniteDimensional ℂ R] [IsSimpleModule R V] :
    Module.Finite ℂ V := by
  letI : Nontrivial V := IsSimpleModule.nontrivial R V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact Module.Finite.of_surjective
    ((LinearMap.toSpanSingleton R V v).restrictScalars ℂ)
    (IsSimpleModule.toSpanSingleton_surjective R hv)

lemma apm_b97a04_schur_and_scalars
    (R V : Type) [Ring R] [AddCommGroup V]
    [Algebra ℂ R] [Module ℂ V] [Module R V]
    [IsScalarTower ℂ R V] [SMulCommClass ℂ R V]
    [FiniteDimensional ℂ R] [IsSimpleModule R V] :
    (∀ φ : Module.End R V, φ ≠ 0 → IsUnit φ) ∧
    Module.Finite ℂ (Module.End R V) ∧
    (∀ φ : Module.End R V, ∃ c : ℂ, φ = c • LinearMap.id) := by
  letI : Module.Finite ℂ V := apm_b97a04_module_finite R V
  letI : FiniteDimensional ℂ V := apm_b97a04_module_finite R V
  classical
  constructor
  · intro φ hφ
    exact (isUnit_iff_ne_zero).2 hφ
  constructor
  · exact Module.Finite.of_injective (LinearMap.restrictScalarsₗ ℂ R V V ℂ)
      (LinearMap.restrictScalars_injective ℂ)
  · intro φ
    obtain ⟨c, hc⟩ :=
      (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := R) (V := V) ℂ).2 φ
    exact ⟨c, by simpa using hc.symm⟩

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
  /-
  Boundary (closer hop 1): `apm_b97a04_module_finite` now derives
  `Module.Finite ℂ V` from a nonzero cyclic vector using
  `IsSimpleModule.toSpanSingleton_surjective` and
  `Module.Finite.of_surjective`.  The compiled helper
  `apm_b97a04_schur_and_scalars` also closes all three Schur-theoretic
  conclusions: nonzero `R`-endomorphisms are units, the endomorphism space is
  finite over `ℂ`, and every endomorphism is scalar.  This reuses
  `LinearMap.bijective_of_ne_zero` indirectly through the division-ring
  instance and `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`.

  The remaining bridge starts at Burnside/Jacobson density.  The available
  `Module.Finite.toModuleEnd_moduleEnd_surjective` targets the double
  centralizer `Module.End (Module.End R V) V`; applying it requires packaging
  finite generation over `Module.End R V`, then identifying that scalar
  action and its double centralizer with the exact `ℂ`-linear endomorphism
  algebra.  After constructing `R ≃ₐ[ℂ] Module.End ℂ V`, the final conjunct
  still needs transport of semisimplicity and the unique simple-module type to
  every possibly infinite `W`, before
  `IsIsotypicOfType.linearEquiv_finsupp` applies. Searches of
  `LEMMA-INDEX.md`, Mathlib's simple-module/Wedderburn--Artin sources, all
  solved sibling artifacts, `ConstructionTargets/`, and git history found no
  declaration packaging either transport. The statement appears sound.
  -/
  sorry
