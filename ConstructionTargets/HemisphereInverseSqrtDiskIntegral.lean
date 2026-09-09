import ConstructionTargets.CappedCylinderSurfaceIntegral

/-! # Inverse-square-root terms in the hemispherical disk integral

This file compiles the algebraic and interior analytic part of the frozen
hemisphere calculation.  The remaining measure-theoretic input is isolated as
one standard polar-integrability statement, rather than assuming the value of
the hemisphere integral.
-/

open MeasureTheory Set
noncomputable section

namespace ConstructionTargets.HemisphereInverseSqrtDiskIntegral

def unitDisk : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}
def openUnitDisk : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 < 1}

def inverseSqrtKernel (p : ℝ × ℝ) : ℝ :=
  1 / Real.sqrt (1 - p.1 ^ 2 - p.2 ^ 2)

def xInverseSqrt (p : ℝ × ℝ) : ℝ := p.1 * inverseSqrtKernel p
def yInverseSqrt (p : ℝ × ℝ) : ℝ := p.2 * inverseSqrtKernel p

def reflectX (p : ℝ × ℝ) : ℝ × ℝ := (-p.1, p.2)
def reflectY (p : ℝ × ℝ) : ℝ × ℝ := (p.1, -p.2)

theorem sqrt_denominator_pos {p : ℝ × ℝ} (hp : p ∈ openUnitDisk) :
    0 < Real.sqrt (1 - p.1 ^ 2 - p.2 ^ 2) := by
  apply Real.sqrt_pos.2
  dsimp [openUnitDisk] at hp
  linarith

theorem reflectX_mem_unitDisk_iff (p : ℝ × ℝ) :
    reflectX p ∈ unitDisk ↔ p ∈ unitDisk := by
  simp [reflectX, unitDisk]

theorem reflectY_mem_unitDisk_iff (p : ℝ × ℝ) :
    reflectY p ∈ unitDisk ↔ p ∈ unitDisk := by
  simp [reflectY, unitDisk]

theorem xInverseSqrt_reflectX (p : ℝ × ℝ) :
    xInverseSqrt (reflectX p) = -xInverseSqrt p := by
  simp [xInverseSqrt, inverseSqrtKernel, reflectX]

theorem yInverseSqrt_reflectY (p : ℝ × ℝ) :
    yInverseSqrt (reflectY p) = -yInverseSqrt p := by
  simp [yInverseSqrt, inverseSqrtKernel, reflectY]

theorem xInverseSqrt_pair_cancel (p : ℝ × ℝ) :
    xInverseSqrt p + xInverseSqrt (reflectX p) = 0 := by
  rw [xInverseSqrt_reflectX]
  ring

theorem yInverseSqrt_pair_cancel (p : ℝ × ℝ) :
    yInverseSqrt p + yInverseSqrt (reflectY p) = 0 := by
  rw [yInverseSqrt_reflectY]
  ring

/-- The single standard polar-coordinate estimate still missing from the
current API: local integrability of `(1-r²)⁻¹ᐟ²` on the closed unit disk. -/
def RadialInverseSqrtIntegrable : Prop :=
  IntegrableOn inverseSqrtKernel unitDisk

/-- Exact remaining analytic package.  Once the radial estimate is available,
boundedness of both coordinates on the disk gives these two consequences. -/
def CoordinateInverseSqrtIntegrabilityConsequences : Prop :=
  RadialInverseSqrtIntegrable →
    IntegrableOn xInverseSqrt unitDisk ∧ IntegrableOn yInverseSqrt unitDisk

theorem interior_formula_x {p : ℝ × ℝ} (hp : p ∈ openUnitDisk) :
    xInverseSqrt p = p.1 / Real.sqrt (1 - p.1 ^ 2 - p.2 ^ 2) := by
  rw [xInverseSqrt, inverseSqrtKernel]
  field_simp [ne_of_gt (sqrt_denominator_pos hp)]

theorem interior_formula_y {p : ℝ × ℝ} (hp : p ∈ openUnitDisk) :
    yInverseSqrt p = p.2 / Real.sqrt (1 - p.1 ^ 2 - p.2 ^ 2) := by
  rw [yInverseSqrt, inverseSqrtKernel]
  field_simp [ne_of_gt (sqrt_denominator_pos hp)]

#print axioms sqrt_denominator_pos
#print axioms xInverseSqrt_reflectX
#print axioms yInverseSqrt_reflectY
#print axioms xInverseSqrt_pair_cancel
#print axioms yInverseSqrt_pair_cancel
#print axioms interior_formula_x
#print axioms interior_formula_y

end ConstructionTargets.HemisphereInverseSqrtDiskIntegral
