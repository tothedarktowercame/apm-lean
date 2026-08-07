import Mathlib

/-! # APM t95J05: descent and integration of a three-form on `ℝP³`

## Statement repairs

The hint's `vol B⁴ = π⁴ / 2` is a typographical error; the four-ball has
volume `π² / 2`.  Accordingly the requested integral is `-π²` with the
orientation for which `S³ → ℝP³` is orientation-preserving.

## Encoding question

The sphere is the actual unit sphere in `ℝ⁴`, and `ℝP³` is its antipodal
quotient. A projective three-form is represented by its antipodally invariant
pullback density on `S³`. The given ambient form restricts to the explicit
density obtained by contraction with the outward unit normal. Integration on
the quotient is half the Hausdorff-measure integral over the double cover.
-/

open MeasureTheory

noncomputable section

abbrev t95J05R4 := EuclideanSpace ℝ (Fin 4)
abbrev t95J05SphereThree := Metric.sphere (0 : t95J05R4) 1

def t95J05Antipode (x : t95J05SphereThree) : t95J05SphereThree :=
  ⟨-x.1, by simpa [Metric.mem_sphere] using x.2⟩

inductive T95J05AntipodalRel :
    t95J05SphereThree → t95J05SphereThree → Prop
  | antipodal (x : t95J05SphereThree) :
      T95J05AntipodalRel x (t95J05Antipode x)

def t95J05RealProjectiveThree :=
  Quotient (Relation.EqvGen.setoid T95J05AntipodalRel)

noncomputable instance : TopologicalSpace t95J05RealProjectiveThree :=
  TopologicalSpace.coinduced
    (fun x : t95J05SphereThree ↦
      Quotient.mk (Relation.EqvGen.setoid T95J05AntipodalRel) x)
    inferInstance

/-- A three-form on `ℝP³`, represented by its invariant density upstairs. -/
def T95J05ProjectiveThreeForm :=
  {ρ : t95J05SphereThree → ℝ //
    ∀ x, ρ (t95J05Antipode x) = ρ x}

/-- The coefficient `x₂³ - 4x₁` of the ambient three-form. -/
def t95J05Omega (x : t95J05R4) : ℝ := x 1 ^ 3 - 4 * x 0

/-- Restriction to the oriented sphere, by contraction with its normal. -/
def t95J05InclusionPullback (x : t95J05SphereThree) : ℝ :=
  t95J05Omega x.1 * x.1 0

/-- Pullback along the antipodal quotient projection. -/
def t95J05ProjectionPullback (η : T95J05ProjectiveThreeForm) :
    t95J05SphereThree → ℝ := η.1

def t95J05Integral (η : T95J05ProjectiveThreeForm) : ℝ :=
  (1 / 2 : ℝ) * ∫ x, η.1 x ∂Measure.hausdorffMeasure 3

theorem apm_t95j05 :
    (∃! η : T95J05ProjectiveThreeForm,
      t95J05ProjectionPullback η = t95J05InclusionPullback) ∧
    (∀ η : T95J05ProjectiveThreeForm,
      t95J05ProjectionPullback η = t95J05InclusionPullback →
      t95J05Integral η = -Real.pi ^ 2) := by
  sorry
