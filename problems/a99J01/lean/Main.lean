import Mathlib

open MeasureTheory Set

noncomputable section

/-!
# APM a99J01

## Statement repairs

None.

## Encoding notes

The integral of `log |f|` may equal `-∞` when `f` vanishes. Consequently it is
encoded as an `EReal` extended integral: the difference of the lintegrals of its
positive and negative parts. At a zero of `f`, the negative part is `⊤`, correctly
representing `log 0 = -∞`; using Lean's real-valued `Real.log 0 = 0` directly would
misstate the problem.
-/

def apmLogAbsPositive {X : Type*} (f : X → ℝ) (x : X) : ENNReal :=
  ENNReal.ofReal (Real.log |f x|)

def apmLogAbsNegative {X : Type*} (f : X → ℝ) (x : X) : ENNReal :=
  if f x = 0 then ⊤ else ENNReal.ofReal (-Real.log |f x|)

noncomputable def apmLogIntegralOn {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (E : Set X) (mu : Measure X) : EReal :=
  ((∫⁻ x in E, apmLogAbsPositive f x ∂mu : ENNReal) : EReal) -
    ((∫⁻ x in E, apmLogAbsNegative f x ∂mu : ENNReal) : EReal)

/-- The positive part of the logarithm is pointwise dominated by `|f|`. -/
lemma apmLogAbsPositive_le_abs {X : Type*} (f : X → ℝ) (x : X) :
    apmLogAbsPositive f x ≤ ENNReal.ofReal |f x| := by
  exact ENNReal.ofReal_le_ofReal (Real.log_le_self (abs_nonneg (f x)))

/-- For an integrable function, the positive part of its logarithm has finite
extended integral on every measurable or nonmeasurable subset. -/
lemma apmLogAbsPositive_setLIntegral_ne_top
    {X : Type*} [MeasurableSpace X] {mu : Measure X} {f : X → ℝ}
    (hf : Integrable f mu) (E : Set X) :
    ∫⁻ x in E, apmLogAbsPositive f x ∂mu ≠ ⊤ := by
  apply ne_top_of_le_ne_top (ne_top_of_lt hf.norm.lintegral_lt_top)
  calc
    ∫⁻ x in E, apmLogAbsPositive f x ∂mu
        ≤ ∫⁻ x in E, ENNReal.ofReal |f x| ∂mu :=
      lintegral_mono (fun x ↦ apmLogAbsPositive_le_abs f x)
    _ ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂mu := setLIntegral_le_lintegral _ _

theorem apm_a99j01
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (f : X → ℝ)
    (hf : Integrable f mu)
    (hf_norm : ∫ x, |f x| ∂mu = 1) :
    ∀ E : Set X, MeasurableSet E → 0 < mu E → mu E < ⊤ →
      apmLogIntegralOn f E mu ≤
        ((-((mu E).toReal) * Real.log (mu E).toReal : ℝ) : EReal) := by
  /-
  Boundary (closer hop 1): renewed Mathlib inspection found the actual Jensen
  API, `ConcaveOn.le_map_set_average`, in `Analysis.Convex.Integral`.  It is
  real-valued and assumes integrability of the composed concave function, so
  it cannot be applied directly when `log |f|` has integral `-∞`.

  The two compiled helpers above close the first extended-integral obligation:
  `log⁺ |f| ≤ |f|`, hence the positive logarithmic part has finite lintegral on
  every `E`.  Therefore `apmLogIntegralOn` is always well-defined and never
  `+∞`; if its negative-part lintegral is `⊤`, the target inequality should
  follow immediately from `EReal` subtraction.  In the finite-negative-part
  case one can recover an integrable real logarithm and apply Jensen after
  normalizing `mu.restrict E` by `(mu E).toReal⁻¹`.

  Searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`, closed artifacts,
  Mathlib's Jensen, entropy/KL-divergence, `EReal`, and tilted-measure APIs, and
  git history found no theorem already combining this finite/infinite negative-
  part split with Jensen.  The remaining bridge is that split, identification
  of the custom `EReal` difference with the real integral in the finite case,
  and normalization arithmetic using `hf_norm`.
  -/
  sorry
