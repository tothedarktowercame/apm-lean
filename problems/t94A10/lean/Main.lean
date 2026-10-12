import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import ConstructionTargets.t94A10Closure

/-!
# APM t94A10 — the solid-angle form on punctured three-space

## Statement repairs

None.

## Encoding questions

Mathlib's exterior derivative is formulated for ambient forms. A form on the
punctured space is extended arbitrarily at the omitted origin and `extDeriv`
is evaluated only at nonzero points; locality makes the value at the origin
irrelevant. Closedness and exactness are thus concrete derivative statements
on the actual punctured space.
-/

noncomputable section
open Filter Topology

abbrev apm_t94a10_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t94a10_Punctured := {x : apm_t94a10_E3 // x ≠ 0}
abbrev apm_t94a10_Form (k : ℕ) :=
  apm_t94a10_Punctured → apm_t94a10_E3 [⋀^Fin k]→L[ℝ] ℝ

def apm_t94a10_IsOmega (omega : apm_t94a10_Form 2) : Prop :=
  ∀ (x : apm_t94a10_Punctured) (v : Fin 2 → apm_t94a10_E3),
    omega x v =
      (x.1 0 * (v 0 1 * v 1 2 - v 0 2 * v 1 1) -
        x.1 1 * (v 0 0 * v 1 2 - v 0 2 * v 1 0) +
        x.1 2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)) /
      (Real.sqrt (x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2)) ^ 3

def apm_t94a10_ambientExtension {k : ℕ}
    (omega : apm_t94a10_Form k) :
    apm_t94a10_E3 → apm_t94a10_E3 [⋀^Fin k]→L[ℝ] ℝ := by
  classical
  exact fun x ↦ if h : x ≠ 0 then omega ⟨x, h⟩ else 0

def apm_t94a10_IsClosed (omega : apm_t94a10_Form 2) : Prop :=
  (∀ x : apm_t94a10_Punctured,
    DifferentiableAt ℝ (apm_t94a10_ambientExtension omega) x.1) ∧
  ∀ x : apm_t94a10_Punctured,
    extDeriv (apm_t94a10_ambientExtension omega) x.1 = 0

def apm_t94a10_IsExact (omega : apm_t94a10_Form 2) : Prop :=
  ∃ eta : apm_t94a10_Form 1,
    (∀ x : apm_t94a10_Punctured,
      DifferentiableAt ℝ (apm_t94a10_ambientExtension eta) x.1) ∧
    ∀ x : apm_t94a10_Punctured,
      extDeriv (apm_t94a10_ambientExtension eta) x.1 = omega x

/-- The radial denominator in the solid-angle form is strictly positive away
from the deleted origin.  This is the elementary analytic prerequisite for
differentiating the displayed quotient. -/
lemma apm_t94a10_radial_sq_pos (x : apm_t94a10_Punctured) :
    0 < x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 := by
  have h0 : 0 ≤ x.1 0 ^ 2 := sq_nonneg _
  have h1 : 0 ≤ x.1 1 ^ 2 := sq_nonneg _
  have h2 : 0 ≤ x.1 2 ^ 2 := sq_nonneg _
  by_contra h
  have hs : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 = 0 := by linarith
  have hx0 : x.1 0 = 0 := by nlinarith
  have hx1 : x.1 1 = 0 := by nlinarith
  have hx2 : x.1 2 = 0 := by nlinarith
  apply x.2
  ext i
  fin_cases i <;> simp [hx0, hx1, hx2]

lemma apm_t94a10_radial_sqrt_ne_zero (x : apm_t94a10_Punctured) :
    Real.sqrt (x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.2 (apm_t94a10_radial_sq_pos x))

/-- The complete cubed denominator of the solid-angle form is positive. -/
lemma apm_t94a10_radial_denominator_pos (x : apm_t94a10_Punctured) :
    0 < (Real.sqrt (x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2)) ^ 3 := by
  exact pow_pos (Real.sqrt_pos.2 (apm_t94a10_radial_sq_pos x)) _

lemma apm_t94a10_radial_denominator_ne_zero (x : apm_t94a10_Punctured) :
    (Real.sqrt (x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2)) ^ 3 ≠ 0 :=
  ne_of_gt (apm_t94a10_radial_denominator_pos x)

/-- Mathlib's Euclidean norm formula identifies the coordinate expression
used by the solid-angle form with the squared ambient norm. -/
lemma apm_t94a10_radial_sq_eq_norm_sq (x : apm_t94a10_E3) :
    x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_succ]
  ring

/-- Consequently the denominator of the solid-angle form restricts to one on
the unit sphere.  This is the normalization needed by the sphere-period
calculation in the remaining non-exactness argument. -/
lemma apm_t94a10_radial_denominator_eq_one_of_norm_eq_one
    (x : apm_t94a10_E3) (hx : ‖x‖ = 1) :
    (Real.sqrt (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)) ^ 3 = 1 := by
  rw [apm_t94a10_radial_sq_eq_norm_sq, hx]
  norm_num

/-- On the punctured space the arbitrary ambient extension reduces to the
specified solid-angle formula. -/
lemma apm_t94a10_ambientExtension_apply_of_isOmega
    {omega : apm_t94a10_Form 2} (homega : apm_t94a10_IsOmega omega)
    (x : apm_t94a10_Punctured) (v : Fin 2 → apm_t94a10_E3) :
    apm_t94a10_ambientExtension omega x.1 v =
      (x.1 0 * (v 0 1 * v 1 2 - v 0 2 * v 1 1) -
        x.1 1 * (v 0 0 * v 1 2 - v 0 2 * v 1 0) +
        x.1 2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)) /
      (Real.sqrt (x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2)) ^ 3 := by
  rw [apm_t94a10_ambientExtension]
  simp only [dif_pos x.2]
  exact homega x v

/-- Why this unblocks `apm_t94a10`: this is the missing local quotient-rule
and alternating-coordinate calculation.  It states that the displayed
solid-angle form is differentiable away from the origin and has vanishing
exterior derivative there. -/
theorem apm_t94A10_bridge_solidAngle_closed
    (omega : apm_t94a10_Form 2)
    (homega : apm_t94a10_IsOmega omega) :
    apm_t94a10_IsClosed omega := by
  have hlocal (x : apm_t94a10_Punctured) :
      apm_t94a10_ambientExtension omega =ᶠ[𝓝 x.1]
        ConstructionTargets.T94A10Closure.solidAngleAmbient := by
    filter_upwards [isOpen_compl_singleton.eventually_mem x.2] with y hy
    have hy0 : y ≠ 0 := hy
    ext v
    rw [apm_t94a10_ambientExtension]
    rw [dif_pos hy0, homega ⟨y, hy0⟩ v]
    exact (ConstructionTargets.T94A10Closure.solidAngleAmbient_apply_coordinate y v).symm
  constructor
  · intro x
    exact (hlocal x).differentiableAt_iff.mpr
      (ConstructionTargets.T94A10Closure.solidAngleAmbient_closed x.1 x.2).1
  · intro x
    rw [(hlocal x).extDeriv_eq]
    exact (ConstructionTargets.T94A10Closure.solidAngleAmbient_closed x.1 x.2).2

/-- Why this unblocks `apm_t94a10`: this is the specialized sphere-period
and Stokes obstruction in the exact vocabulary available in this file.  Its
content is that a form with the displayed solid-angle values cannot be the
exterior derivative of a globally defined one-form on punctured space. -/
theorem apm_t94A10_bridge_solidAngle_not_exact
    (omega : apm_t94a10_Form 2)
    (homega : apm_t94a10_IsOmega omega) :
    ¬apm_t94a10_IsExact omega := by
  intro hexact
  apply ConstructionTargets.T94A10Closure.bridge_solidAngle_not_exact
    (apm_t94a10_ambientExtension omega) at hexact
  · exact hexact
  · intro x hx
    ext v
    rw [apm_t94a10_ambientExtension, dif_pos hx, homega ⟨x, hx⟩ v]
    exact (ConstructionTargets.T94A10Closure.solidAngleAmbient_apply_coordinate x v).symm
  · rcases hexact with ⟨eta, heta, hdeta⟩
    refine ⟨apm_t94a10_ambientExtension eta, ?_, ?_⟩
    · intro x hx
      exact heta ⟨x, hx⟩
    · intro x hx
      rw [hdeta ⟨x, hx⟩, apm_t94a10_ambientExtension, dif_pos hx]

theorem apm_t94a10 (omega : apm_t94a10_Form 2)
    (homega : apm_t94a10_IsOmega omega) :
    apm_t94a10_IsClosed omega ∧ ¬apm_t94a10_IsExact omega := by
  exact ⟨apm_t94A10_bridge_solidAngle_closed omega homega,
    apm_t94A10_bridge_solidAngle_not_exact omega homega⟩
