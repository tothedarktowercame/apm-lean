import Mathlib

open MeasureTheory
noncomputable section

abbrev t95J05R4 := EuclideanSpace ℝ (Fin 4)
abbrev t95J05SphereThree := Metric.sphere (0 : t95J05R4) 1

def t95J05Antipode (x : t95J05SphereThree) : t95J05SphereThree :=
  ⟨-x.1, by simpa [Metric.mem_sphere] using x.2⟩

inductive T95J05AntipodalRel : t95J05SphereThree → t95J05SphereThree → Prop
  | antipodal (x) : T95J05AntipodalRel x (t95J05Antipode x)

def t95J05RealProjectiveThree :=
  Quotient (Relation.EqvGen.setoid T95J05AntipodalRel)

noncomputable instance : TopologicalSpace t95J05RealProjectiveThree :=
  TopologicalSpace.coinduced
    (fun x : t95J05SphereThree ↦
      Quotient.mk (Relation.EqvGen.setoid T95J05AntipodalRel) x) inferInstance

def T95J05ProjectiveThreeForm :=
  {ρ : t95J05SphereThree → ℝ // ∀ x, ρ (t95J05Antipode x) = ρ x}

def t95J05Omega (x : t95J05R4) : ℝ := x 1 ^ 3 - 4 * x 0
def t95J05InclusionPullback (x : t95J05SphereThree) : ℝ :=
  t95J05Omega x.1 * x.1 0
def t95J05ProjectionPullback (η : T95J05ProjectiveThreeForm) :
    t95J05SphereThree → ℝ := η.1

/-- Repaired: conventional Euclidean surface measure, rather than Mathlib's
diameter-normalized raw Hausdorff measure. -/
def t95J05Integral (η : T95J05ProjectiveThreeForm) : ℝ :=
  (1 / 2 : ℝ) * ∫ x, η.1 x ∂μHE[3]

theorem apm_t95j05 :
    (∃! η : T95J05ProjectiveThreeForm,
      t95J05ProjectionPullback η = t95J05InclusionPullback) ∧
    (∀ η : T95J05ProjectiveThreeForm,
      t95J05ProjectionPullback η = t95J05InclusionPullback →
      t95J05Integral η = -Real.pi ^ 2) := by
  sorry

