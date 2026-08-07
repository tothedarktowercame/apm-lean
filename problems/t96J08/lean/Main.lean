import Mathlib

/-!
# APM t96J08

## Statement repairs

None.

## Encoding questions

Mathlib does not currently bundle integration of differential forms over
oriented surfaces.  The specified upper hemisphere is therefore encoded by
its standard orientation-preserving parametrization over the closed unit disk.
The two-form itself, its exterior derivative, and exactness are encoded by
their concrete coordinate formulas, rather than by opaque placeholders.
-/

noncomputable section

open MeasureTheory

abbrev apm_t96j08_Point := EuclideanSpace ℝ (Fin 3)
abbrev apm_t96j08_DiskPoint := EuclideanSpace ℝ (Fin 2)

def apm_t96j08_omega
    (p u v : apm_t96j08_Point) : ℝ :=
  p 0 * (u 1 * v 2 - u 2 * v 1) +
  p 1 * (u 0 * v 2 - u 2 * v 0) +
  p 2 * (u 0 * v 1 - u 1 * v 0)

/-- The coordinate exterior derivative of the displayed two-form. -/
def apm_t96j08_domega
    (_p u v w : apm_t96j08_Point) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) -
  u 1 * (v 0 * w 2 - v 2 * w 0) +
  u 2 * (v 0 * w 1 - v 1 * w 0)

def apm_t96j08_IsClosed : Prop :=
  ∀ p u v w : apm_t96j08_Point, apm_t96j08_domega p u v w = 0

def apm_t96j08_dOneForm
    (η : apm_t96j08_Point → apm_t96j08_Point →L[ℝ] ℝ)
    (p u v : apm_t96j08_Point) : ℝ :=
  (fderiv ℝ (fun q => η q v) p) u -
    (fderiv ℝ (fun q => η q u) p) v

def apm_t96j08_IsExact : Prop :=
  ∃ η : apm_t96j08_Point → apm_t96j08_Point →L[ℝ] ℝ,
    ContDiff ℝ (⊤ : ℕ∞) (fun q : apm_t96j08_Point => η q) ∧
    ∀ p u v, apm_t96j08_dOneForm η p u v = apm_t96j08_omega p u v

def apm_t96j08_upperHemisphere (q : apm_t96j08_DiskPoint) : apm_t96j08_Point :=
  WithLp.toLp 2 ![q 0, q 1, 1 + Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)]

def apm_t96j08_paramTangentX (q : apm_t96j08_DiskPoint) : apm_t96j08_Point :=
  WithLp.toLp 2 ![1, 0, -(q 0) / Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)]

def apm_t96j08_paramTangentY (q : apm_t96j08_DiskPoint) : apm_t96j08_Point :=
  WithLp.toLp 2 ![0, 1, -(q 1) / Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)]

def apm_t96j08_hemisphereIntegral : ℝ :=
  ∫ q : apm_t96j08_DiskPoint in Metric.closedBall 0 1,
    apm_t96j08_omega (apm_t96j08_upperHemisphere q)
      (apm_t96j08_paramTangentX q) (apm_t96j08_paramTangentY q)

theorem apm_t96j08 :
    ¬apm_t96j08_IsClosed ∧
    ¬apm_t96j08_IsExact ∧
    apm_t96j08_hemisphereIntegral = 5 * Real.pi / 3 := by
  sorry
