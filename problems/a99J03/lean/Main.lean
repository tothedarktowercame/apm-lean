import Mathlib

/-!
# APM a99J03: A Stieltjes transform of an `L¹` function

## Statement repairs

None.

## Encoding questions

None. The source's `L¹((0,∞))` is interpreted for real-valued functions
using Lebesgue measure. The final question at `a = 0` is encoded by the
explicit counterexample `1_(0,1)`.
-/

open MeasureTheory Set Filter
open scoped ContDiff

noncomputable section

/-- The Stieltjes-type transform in the problem. -/
def apm_a99J03_transform (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), f y / (x + y)

/-- The counterexample `f = 1_(0,1)` for the endpoint question. -/
def apm_a99J03_counterexample (y : ℝ) : ℝ :=
  (Ioo (0 : ℝ) 1).indicator (fun _ ↦ 1) y

/-- The endpoint counterexample is an `L¹` function; its support is the bounded
interval `(0,1)`. -/
lemma apm_a99J03_counterexample_integrableOn :
    IntegrableOn apm_a99J03_counterexample (Ioi 0) := by
  have hconst : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioo 0 1) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  have hind : Integrable ((Ioo (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ))) :=
    hconst.integrable_indicator measurableSet_Ioo
  exact hind.integrableOn

/-- Pointwise parameter derivative of the Stieltjes kernel.  This is the
calculus input to Mathlib's dominated parametric-integral theorem. -/
lemma apm_a99J03_hasDerivAt_kernel
    (f : ℝ → ℝ) {x y : ℝ} (hxy : x + y ≠ 0) :
    HasDerivAt (fun z : ℝ ↦ f y / (z + y)) (-f y / (x + y) ^ 2) x := by
  have hden : HasDerivAt (fun z : ℝ ↦ z + y) 1 x :=
    (hasDerivAt_id x).add_const y
  convert (hasDerivAt_const x (f y)).div hden hxy using 1 <;> ring

/-- Uniform domination of the kernel derivative on the neighborhood
`(x/2, 3x/2)` used for differentiation under the integral sign. -/
lemma apm_a99J03_kernel_deriv_bound
    (f : ℝ → ℝ) {x z y : ℝ} (hx : 0 < x)
    (hz : z ∈ Ioo (x / 2) (3 * x / 2)) (hy : 0 < y) :
    |(-f y) / (z + y) ^ 2| ≤ |f y| / (x / 2) ^ 2 := by
  have hx2 : 0 < x / 2 := by positivity
  have hzy : x / 2 < z + y := by linarith [hz.1]
  have hzy0 : 0 < z + y := hx2.trans hzy
  have habszy : |z + y| = z + y := abs_of_pos hzy0
  rw [abs_div, abs_neg, abs_pow, habszy]
  exact div_le_div_of_nonneg_left (abs_nonneg (f y)) (sq_pos_of_pos hx2)
    ((sq_le_sq₀ hx2.le hzy0.le).2 hzy.le)

theorem apm_a99j03
    (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0)) :
    ContDiffOn ℝ ∞ (apm_a99J03_transform f) (Ioi 0) ∧
    (∀ a : ℝ, 0 < a →
      IntegrableOn (deriv (apm_a99J03_transform f)) (Ici a)) ∧
    IntegrableOn apm_a99J03_counterexample (Ioi 0) ∧
    ¬IntegrableOn
      (deriv (apm_a99J03_transform apm_a99J03_counterexample))
      (Ioi 0) := by
  /-
  Boundary (closer hop 1): `apm_a99J03_counterexample_integrableOn` above
  closes the third conjunct directly from bounded support.  Searches of
  `LEMMA-INDEX.md`, all `ConstructionTargets/`, closed siblings, and Mathlib's
  parameter-integral APIs found the reusable theorem
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`; siblings `a01A09`,
  `a01A11`, and `a96A04` demonstrate its use.  No packaged Stieltjes-transform
  smoothness theorem was found.

  Closer hop 2 proves the two central pointwise inputs to that theorem:
  `apm_a99J03_hasDerivAt_kernel` gives the exact parameter derivative, and
  `apm_a99J03_kernel_deriv_bound` proves its uniform domination on the
  neighborhood `(x/2, 3*x/2)` by `|f y|/(x/2)^2`.

  The remaining common bridge is to package these facts into, for `x > 0`,

  `deriv (apm_a99J03_transform f) x =
     -∫ y in Ioi 0, f y / (x+y)^2`.

  including all measurability and restricted-integrability obligations.
  Iterating the same argument gives `ContDiffOn`; Tonelli then yields
  the derivative `L¹(Ici a)` estimate.  For the counterexample the displayed
  formula reduces to `-1/x + 1/(x+1)`, whose absolute value is
  `1/(x*(x+1))`; the final blocker is its nonintegrability at zero via the
  power-integrability API.  Thus the explicit datum's integrability is proved,
  while differentiation under the improper integral remains open.
  -/
  sorry
