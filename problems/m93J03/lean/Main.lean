import Mathlib

/-!
# APM m93J03: A nonlinear integral equation near its trivial branch

## Statement repairs

The printed global uniqueness claim is stronger than, and is not established
by, the intended implicit-function argument. The exact finite-dimensional
reduction has additional nonzero branches already at `ε = 0`; the invertible
Jacobian proves uniqueness only in a neighborhood of the trivial solution.
We therefore state the minimally repaired local result: fixed radii `δ,η > 0`
give a unique solution with `|ε| < δ` and uniform size below `η`.

## Encoding questions

None. The equation uses the Lebesgue integral on `[-π,π]`; continuity and
uniqueness are both restricted to that exact interval.
-/

open MeasureTheory Set

noncomputable section

def apm_m93J03_isSolution (ε : ℝ) (x : ℝ → ℝ) : Prop :=
  ContinuousOn x (Icc (-Real.pi) Real.pi) ∧
  ∀ t ∈ Icc (-Real.pi) Real.pi,
    x t = ε + ∫ s in Icc (-Real.pi) Real.pi, Real.sin (t + s + x s)

def apm_m93J03_isSmall (x : ℝ → ℝ) (η : ℝ) : Prop :=
  ∀ t ∈ Icc (-Real.pi) Real.pi, |x t| < η

lemma apm_m93J03_isSmall_mono {x : ℝ → ℝ} {η η' : ℝ}
    (hx : apm_m93J03_isSmall x η) (hη : η ≤ η') :
    apm_m93J03_isSmall x η' := by
  intro t ht
  exact (hx t ht).trans_le hη

lemma apm_m93J03_zero_isSmall {η : ℝ} (hη : 0 < η) :
    apm_m93J03_isSmall (fun _ ↦ 0) η := by
  intro t ht
  simpa using hη

theorem apm_m93j03 :
    ∃ δ η : ℝ, 0 < δ ∧ 0 < η ∧
      ∀ ε : ℝ, |ε| < δ →
        ∃ x : ℝ → ℝ,
          apm_m93J03_isSolution ε x ∧
          apm_m93J03_isSmall x η ∧
          ∀ y : ℝ → ℝ,
            apm_m93J03_isSolution ε y →
            apm_m93J03_isSmall y η →
            EqOn x y (Icc (-Real.pi) Real.pi) := by
  /-
  CLOSER HOP 1 (partial). The uniform-radius bookkeeping is now compiled:
  `apm_m93J03_isSmall_mono` permits enlarging a valid solution radius and
  `apm_m93J03_zero_isSmall` supplies the trivial-branch base case.

  The remaining boundary: the intended proof first separates the sine kernel and proves
  that every solution on the interval has the exact form
  `ε + a * sin t + b * cos t`. It must then define the resulting map
  `H : ℝ × (ℝ × ℝ) → ℝ × ℝ`, establish its strict Frechet
  derivative by differentiating two parameterized interval integrals, and
  identify the partial Jacobian at zero with the invertible diagonal map
  having entries `1 + π` and `1 - π`.

  Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, solved
  implicit-function artifacts, the parametric-integral sources, and git
  history found no complete reduction. Mathlib's product-domain implicit-function APIs
  `ContDiffAt.implicitFunction`,
  `ContDiffAt.eventually_apply_eq_iff_implicitFunction`, and
  `HasStrictFDerivAt.implicitFunctionOfProdDomain`. Applying them here still
  requires the missing derivative-under-the-integral construction and the
  final conversion of their neighborhood uniqueness into the statement's
  uniform `apm_m93J03_isSmall` radius for arbitrary function-valued
  solutions. No compiled sibling supplied those bridges in this pass.
  -/
  sorry
