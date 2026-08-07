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
  letI : Nontrivial V := IsSimpleModule.nontrivial R V
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

/-- Burnside's theorem in the required form. This uses Mathlib's
`Module.Finite.toModuleEnd_moduleEnd_surjective` (Jacobson density), with
`apm_b97a04_schur_and_scalars` identifying the commutant with `ℂ`. -/
lemma apm_b97a04_burnside
    (R V : Type) [Ring R] [AddCommGroup V]
    [Algebra ℂ R] [Module ℂ V] [Module R V]
    [IsScalarTower ℂ R V] [SMulCommClass ℂ R V]
    [FiniteDimensional ℂ R] [IsSimpleModule R V]
    (hfaithful : ∀ r : R, (∀ v : V, r • v = 0) → r = 0) :
    Nonempty (R ≃ₐ[ℂ] Module.End ℂ V) := by
  letI : Module.Finite ℂ V := apm_b97a04_module_finite R V
  letI : FiniteDimensional ℂ V := apm_b97a04_module_finite R V
  let D := Module.End R V
  letI : Module.Finite D V := Module.Finite.of_restrictScalars_finite ℂ D V
  let ρ : R →ₐ[ℂ] Module.End ℂ V := Algebra.lsmul ℂ ℂ V
  refine ⟨AlgEquiv.ofBijective ρ ⟨?_, ?_⟩⟩
  · intro r s hrs
    apply sub_eq_zero.mp
    apply hfaithful (r - s)
    intro v
    rw [sub_smul, sub_eq_zero]
    exact congrFun (congrArg DFunLike.coe hrs) v
  · intro f
    let fD : Module.End D V :=
      { f with
        map_smul' := fun d v => by
          obtain ⟨c, hc⟩ :=
            (apm_b97a04_schur_and_scalars R V).2.2 d
          rw [hc]
          change f (c • v) = c • f v
          exact f.map_smul c v }
    obtain ⟨r, hr⟩ :=
      Module.Finite.toModuleEnd_moduleEnd_surjective (R := R) (M := V) fD
    refine ⟨r, LinearMap.ext fun v => ?_⟩
    change r • v = f v
    exact congrFun (congrArg DFunLike.coe hr) v

/-- The matrix-algebra realization makes `R` simple Artinian; Mathlib's
`IsSimpleRing.isIsotypic` and `IsIsotypicOfType.linearEquiv_finsupp` then
decompose an arbitrary module into copies of the unique simple type `V`. -/
lemma apm_b97a04_modules_are_copies
    (R V : Type) [Ring R] [AddCommGroup V]
    [Algebra ℂ R] [Module ℂ V] [Module R V]
    [IsScalarTower ℂ R V] [SMulCommClass ℂ R V]
    [FiniteDimensional ℂ R] [IsSimpleModule R V]
    (e : R ≃ₐ[ℂ] Module.End ℂ V)
    (W : Type) [AddCommGroup W] [Module R W] :
    ∃ (ι : Type), Nonempty (W ≃ₗ[R] (ι →₀ V)) := by
  letI : Module.Finite ℂ V := apm_b97a04_module_finite R V
  letI : FiniteDimensional ℂ V := apm_b97a04_module_finite R V
  letI : Nontrivial V := IsSimpleModule.nontrivial R V
  let n := Module.finrank ℂ V
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  let b := Module.finBasis ℂ V
  let em : Module.End ℂ V ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toMatrixAlgEquiv b
  letI : IsSimpleRing (Module.End ℂ V) :=
    IsSimpleRing.of_ringEquiv em.symm.toRingEquiv inferInstance
  letI : IsSimpleRing R :=
    IsSimpleRing.of_ringEquiv e.symm.toRingEquiv inferInstance
  letI : IsArtinianRing R := IsArtinianRing.of_finite ℂ R
  have hRR : IsIsotypic R R := IsSimpleRing.isIsotypic R R
  have hWV : IsIsotypicOfType R W V := by
    intro m hm
    obtain ⟨I, ⟨emI⟩⟩ :=
      IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R m
    letI : IsSimpleModule R I := IsSimpleModule.congr emI.symm
    obtain ⟨J, ⟨eVJ⟩⟩ :=
      IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R V
    letI : IsSimpleModule R J := IsSimpleModule.congr eVJ.symm
    exact ⟨emI.trans ((hRR I J).some.symm.trans eVJ.symm)⟩
  exact hWV.linearEquiv_finsupp

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
  have hfinite : Module.Finite ℂ V := apm_b97a04_module_finite R V
  have hschur := apm_b97a04_schur_and_scalars R V
  obtain ⟨e⟩ := apm_b97a04_burnside R V hfaithful
  exact ⟨hfinite, hschur.1, hschur.2.1, hschur.2.2, ⟨e⟩,
    fun W _ _ => apm_b97a04_modules_are_copies R V e W⟩
