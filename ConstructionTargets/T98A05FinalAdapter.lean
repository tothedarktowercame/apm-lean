import ConstructionTargets.FinTwoTriangleFubiniFinal
import ConstructionTargets.CirclePeriodObstruction

/-! # Final generic adapter for frozen t98A05

The standalone problem file is not a Lake module.  This file therefore repeats
only its public mathematical interfaces and proves the three bridge results
and their final conjunction from the construction targets.
-/

open MeasureTheory Set
noncomputable section

namespace ConstructionTargets.T98A05FinalAdapter

open ConstructionTargets.ExteriorDerivativeSimplexCalculus
open ConstructionTargets.FrozenSimplexIntegralAdapter
open ConstructionTargets.FinTwoTriangleFubiniFinal

abbrev Circle3 := ConstructionTargets.CirclePeriodObstruction.Circle3
abbrev CircleForm1 := ConstructionTargets.CirclePeriodObstruction.CircleForm1

def IsRestriction (alpha : Form 1) (alpha' : CircleForm1) : Prop :=
  ∀ (x : Circle3) (v : E3), alpha' x v = alpha x (fun _ ↦ v)

def IsDifferential (f : Circle3 → ℝ) (alpha' : CircleForm1) : Prop :=
  ∀ c : ℝ → Circle3,
    Differentiable ℝ (fun t => (c t : E3)) →
    Differentiable ℝ (fun t => f (c t)) ∧
      ∀ t : ℝ, deriv (fun s => f (c s)) t =
        alpha' (c t) (deriv (fun s => (c s : E3)) t)

def WedgeEval (alpha : Form 1) (beta : Form 2)
    (x : E3) (v : Fin 3 → E3) : ℝ :=
  alpha x ![v 0] * beta x ![v 1, v 2] -
    alpha x ![v 1] * beta x ![v 0, v 2] +
    alpha x ![v 2] * beta x ![v 0, v 1]

def simplexParameter (u : E2) : E3 :=
  WithLp.toLp 2 ![u 0, u 1, 1 - u 0 - u 1]

def simplexTangent0 : E3 := WithLp.toLp 2 ![(1 : ℝ), 0, -1]
def simplexTangent1 : E3 := WithLp.toLp 2 ![(0 : ℝ), 1, -1]

def orientedSimplexIntegral (omega : Form 2) : ℝ :=
  ∫ u in frozenTriangleDomain,
    omega (simplexParameter u) ![simplexTangent0, simplexTangent1]

def IsCircleTangent (x : Circle3) (v : E3) : Prop :=
  (x : E3) 0 * v 0 + (x : E3) 1 * v 1 = 0 ∧ v 2 = 0

def IsCircleClosed (alpha : Form 1) : Prop :=
  ∀ (x : Circle3) (v : Fin 2 → E3),
    (∀ i, IsCircleTangent x (v i)) → extDeriv alpha x v = 0

/-- The bundled coordinate exterior-derivative bridge. -/
theorem bridge_extDerivs
    (alpha : Form 1) (halpha : IsAlpha alpha)
    (beta : Form 2) (hbeta : IsBeta beta)
    (gamma : Form 3) (hgamma : IsGamma gamma) :
    (∀ (x : E3) (v : Fin 2 → E3), extDeriv alpha x v =
      2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)) ∧
    extDeriv beta = 3 • gamma ∧ extDeriv gamma = 0 :=
  frozen_extDerivs alpha halpha beta hbeta gamma hgamma

theorem wedgeEval_eq_zero
    (alpha : Form 1) (halpha : IsAlpha alpha)
    (beta : Form 2) (hbeta : IsBeta beta)
    (x : E3) (v : Fin 3 → E3) : WedgeEval alpha beta x v = 0 := by
  simp only [WedgeEval]
  rw [halpha x ![v 0], halpha x ![v 1], halpha x ![v 2],
    hbeta x ![v 1, v 2], hbeta x ![v 0, v 2], hbeta x ![v 0, v 1]]
  simp
  ring

/-- The frozen affine simplex pullback is the constant function `2`; the
finite-coordinate Fubini theorem evaluates its set integral. -/
theorem bridge_simplexIntegral
    (alpha : Form 1) (halpha : IsAlpha alpha) :
    orientedSimplexIntegral (extDeriv alpha) = 1 := by
  have hd : ∀ (x : E3) (v : Fin 2 → E3), extDeriv alpha x v =
      2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0) :=
    extDeriv_alpha alpha halpha (differentiable_alpha alpha halpha)
  rw [orientedSimplexIntegral]
  have hpullback : (fun u : E2 => extDeriv alpha (simplexParameter u)
      ![simplexTangent0, simplexTangent1]) = fun _ => (2 : ℝ) := by
    funext u
    rw [hd]
    simp [simplexTangent0, simplexTangent1]
  rw [hpullback]
  exact frozenTriangleIntegral_value

/-- The first derivative formula implies closedness after restriction to two
circle-tangent vectors. -/
theorem circleClosed_of_extDeriv_formula
    (alpha : Form 1)
    (hd : ∀ (x : E3) (v : Fin 2 → E3), extDeriv alpha x v =
      2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)) :
    IsCircleClosed alpha := by
  intro x v hv
  rw [hd]
  have ht0 := (hv 0).1
  have ht1 := (hv 1).1
  have hx := x.2.1
  have hA := congrArg (fun z : ℝ ↦ z * v 1 1) ht0
  have hB := congrArg (fun z : ℝ ↦ z * v 0 1) ht1
  have hC := congrArg (fun z : ℝ ↦ z * v 1 0) ht0
  have hD := congrArg (fun z : ℝ ↦ z * v 0 0) ht1
  have ha : (x : E3) 0 * (v 0 0 * v 1 1 - v 0 1 * v 1 0) = 0 := by
    nlinarith
  have hb : (x : E3) 1 * (v 0 0 * v 1 1 - v 0 1 * v 1 0) = 0 := by
    nlinarith
  nlinarith [sq_nonneg (v 0 0 * v 1 1 - v 0 1 * v 1 0)]

/-- The circle-period obstruction, expressed through the frozen-compatible
restriction and differential predicates. -/
theorem bridge_circle_not_differential
    (alpha : Form 1) (halpha : IsAlpha alpha)
    (alpha' : CircleForm1) (halpha' : IsRestriction alpha alpha') :
    ¬ ∃ f : Circle3 → ℝ, IsDifferential f alpha' := by
  exact ConstructionTargets.CirclePeriodObstruction.circle_not_differential
    alpha (by simpa [ConstructionTargets.CirclePeriodObstruction.IsAlpha,
      IsAlpha] using halpha) alpha'
    (by simpa [ConstructionTargets.CirclePeriodObstruction.IsRestriction,
      IsRestriction] using halpha')

/-- Generic final conjunction with the same fields and nesting as frozen
`apm_t98a05`. -/
theorem final_conjunction
    (alpha : Form 1) (halpha : IsAlpha alpha)
    (beta : Form 2) (hbeta : IsBeta beta)
    (gamma : Form 3) (hgamma : IsGamma gamma)
    (alpha' : CircleForm1) (halpha' : IsRestriction alpha alpha') :
    (∀ (x : E3) (v : Fin 2 → E3), extDeriv alpha x v =
      2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)) ∧
    extDeriv beta = 3 • gamma ∧
    extDeriv gamma = 0 ∧
    (∀ (x : E3) (v : Fin 3 → E3), WedgeEval alpha beta x v = 0) ∧
    orientedSimplexIntegral (extDeriv alpha) = 1 ∧
    IsCircleClosed alpha ∧
    ¬ ∃ f : Circle3 → ℝ, IsDifferential f alpha' := by
  obtain ⟨ha, hb, hg⟩ := bridge_extDerivs alpha halpha beta hbeta gamma hgamma
  exact ⟨ha, hb, hg, wedgeEval_eq_zero alpha halpha beta hbeta,
    bridge_simplexIntegral alpha halpha, circleClosed_of_extDeriv_formula alpha ha,
    bridge_circle_not_differential alpha halpha alpha' halpha'⟩

#print axioms bridge_extDerivs
#print axioms bridge_simplexIntegral
#print axioms bridge_circle_not_differential
#print axioms final_conjunction

end ConstructionTargets.T98A05FinalAdapter
