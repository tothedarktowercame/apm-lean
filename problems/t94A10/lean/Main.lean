import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

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

theorem apm_t94a10 (omega : apm_t94a10_Form 2)
    (homega : apm_t94a10_IsOmega omega) :
    apm_t94a10_IsClosed omega ∧ ¬apm_t94a10_IsExact omega := by
  /-
  PARTIAL boundary (closer hop 1).

  New progress: `apm_t94a10_radial_sq_pos` and
  `apm_t94a10_radial_sqrt_ne_zero` prove that the denominator of the frozen
  solid-angle formula is nonzero at every punctured point.  The helper
  `apm_t94a10_ambientExtension_apply_of_isOmega` then eliminates the arbitrary
  value of the ambient extension at the origin and exposes the exact formula
  to be differentiated.  These close the domain and division side conditions
  for a direct `extDeriv_apply` computation of closedness.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, the completed corpus,
  Mathlib's differential-form sources, and git history found no reusable
  solid-angle closedness calculation.  More importantly, Mathlib has
  `extDeriv_apply` and local pullback identities but no manifold integration or
  Stokes theorem connecting an exact ambient form to its integral over the
  unit sphere.  Siblings `t01J06`, `t02A05`, and `t94J07` independently record
  the same missing global interface; `t94J07` introduces it only as an
  additional hypothesis, so it cannot be reused here.  The remaining bridge
  is therefore (1) bundle and differentiate the explicit alternating form to
  prove its exterior derivative vanishes, and (2) formalize the sphere period
  `4 * π` plus Stokes to exclude a global primitive.  The second step requires
  substantial integration infrastructure absent from the searched corpus.
  -/
  sorry
