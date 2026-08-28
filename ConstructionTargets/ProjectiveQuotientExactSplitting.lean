import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Splitting a short exact sequence with projective quotient

This file packages the standard categorical argument needed by `t96A03`:
projectivity lifts the identity through the epic quotient map, producing a
section, and exactness then identifies the middle object with the biproduct of
the kernel object and the quotient.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ProjectiveQuotientExactSplitting

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A short exact sequence whose quotient object is projective splits, with the
middle object canonically (up to the chosen projective lift) isomorphic to the
biproduct of the outer objects. -/
def shortExactIsoBiprod {S : ShortComplex C} (hS : S.ShortExact)
    [Projective S.X₃] : S.X₂ ≅ S.X₁ ⊞ S.X₃ :=
  (ShortComplex.ShortExact.splittingOfProjective hS).isoBinaryBiproduct

/-- The same result in the common consumer form where exactness, monicity of
the left map, and epicity of the right map are available separately. -/
def exactIsoBiprod (S : ShortComplex C) (hS : S.Exact) [Mono S.f] [Epi S.g]
    [Projective S.X₃] : S.X₂ ≅ S.X₁ ⊞ S.X₃ :=
  shortExactIsoBiprod
    { exact := hS
      mono_f := inferInstance
      epi_g := inferInstance }

/-- The section used by `shortExactIsoBiprod` is obtained from projectivity,
not supplied as an additional splitting hypothesis. -/
def projectiveSection {S : ShortComplex C} (hS : S.ShortExact)
    [Projective S.X₃] : S.X₃ ⟶ S.X₂ := by
  letI : Epi S.g := hS.epi_g
  exact Projective.factorThru (𝟙 S.X₃) S.g

@[reassoc (attr := simp)]
theorem projectiveSection_comp {S : ShortComplex C} (hS : S.ShortExact)
    [Projective S.X₃] : projectiveSection hS ≫ S.g = 𝟙 S.X₃ := by
  letI : Epi S.g := hS.epi_g
  exact Projective.factorThru_comp (𝟙 S.X₃) S.g

section IntegerFixture

open ModuleCat

abbrev FixtureA := ModuleCat.of ℤ (Fin 2 → ℤ)
abbrev FixtureP := ModuleCat.of ℤ ℤ
abbrev FixtureB := FixtureA ⊞ FixtureP

abbrev fixtureShortComplex : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (biprod.inl : FixtureA ⟶ FixtureB)
    (biprod.snd : FixtureB ⟶ FixtureP) (by simp)

/-- The standard inclusion/projection sequence on `ℤ² ⊞ ℤ` is short exact. -/
theorem fixtureShortExact : fixtureShortComplex.ShortExact :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct FixtureA FixtureP).shortExact

/-- Concrete validation: the quotient `ℤ` is free, hence projective, so the
generic theorem applies to the sequence with kernel `ℤ²`. -/
def fixtureIso : FixtureB ≅ FixtureA ⊞ FixtureP := by
  letI : Projective FixtureP := inferInstance
  exact shortExactIsoBiprod fixtureShortExact

end IntegerFixture

end ProjectiveQuotientExactSplitting
