import Mathlib

/-! # APM b94J04: localization of modules is exact

## Statement repairs

None.
-/

noncomputable section

/-- A short exact pair of module maps. -/
def IsShortExact {A M N Q : Type*} [Semiring A]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid Q]
    [Module A M] [Module A N] [Module A Q]
    (f : M →ₗ[A] N) (g : N →ₗ[A] Q) : Prop :=
  Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g

/-- The source's `S⁻¹M`, using Mathlib's quotient construction of localized
modules. -/
def moduleLocalization {A : Type*} [CommRing A] (S : Submonoid A)
    (M : Type*) [AddCommGroup M] [Module A M] :=
  LocalizedModule S M

/-- Definition of localized modules, exactness of localization, and the
explicit `ℤ/2ℤ` counterexample to the converse. -/
theorem apm_b94j04
    (A : Type*) [CommRing A] (S : Submonoid A) :
    (∀ (M : Type*) [AddCommGroup M] [Module A M],
      Nonempty (moduleLocalization S M)) ∧
    (∀ (M N Q : Type*)
      [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
      [Module A M] [Module A N] [Module A Q]
      (f : M →ₗ[A] N) (g : N →ₗ[A] Q),
      IsShortExact f g →
        IsShortExact (LocalizedModule.map S f) (LocalizedModule.map S g)) ∧
    (let T : Submonoid ℤ := Submonoid.powers (2 : ℤ)
     let f : ZMod 1 →ₗ[ℤ] ZMod 2 := 0
     let g : ZMod 2 →ₗ[ℤ] ZMod 1 := 0
     ¬ IsShortExact f g ∧
       IsShortExact (LocalizedModule.map T f) (LocalizedModule.map T g)) := by
  constructor
  · intro M _ _
    change Nonempty (LocalizedModule S M)
    exact ⟨0⟩
  constructor
  · intro M N Q _ _ _ _ _ _ f g h
    exact ⟨LocalizedModule.map_injective S f h.1,
      LocalizedModule.map_exact S f g h.2.1,
      LocalizedModule.map_surjective S g h.2.2⟩
  dsimp
  constructor
  · intro h
    have hone := (h.2.1 (1 : ZMod 2)).mp (by simp)
    obtain ⟨x, hx⟩ := hone
    simpa using hx
  · have hsub : Subsingleton (LocalizedModule (Submonoid.powers (2 : ℤ)) (ZMod 2)) :=
      LocalizedModule.subsingleton_iff.mpr (by
        intro m
        exact ⟨2, Submonoid.mem_powers 2, by
          fin_cases m <;> rfl⟩)
    letI := hsub
    constructor
    · intro x y _
      exact Subsingleton.elim x y
    constructor
    · intro y
      constructor
      · intro _
        exact ⟨0, Subsingleton.elim _ _⟩
      · intro _
        exact Subsingleton.elim _ _
    · intro y
      exact ⟨0, Subsingleton.elim _ _⟩
