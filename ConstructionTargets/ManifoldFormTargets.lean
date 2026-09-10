import Mathlib

/-! Differential-form vocabulary on boundaryless smooth manifolds.
Values are alternating covectors on the actual tangent spaces (whose carriers
Mathlib identifies with the model space). Smoothness is tested after pullback
through EVERY chart inverse. The exterior derivative is computed in the
chosen chart and transported back by its tangent map. Chart-independence and
the usual calculus identities are subsequent theorem targets, not assumptions.
-/

open scoped Manifold ContDiff
noncomputable section
namespace ConstructionTargets.ManifoldFormTargets

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

abbrev Form (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :=
  M → E [⋀^Fin k]→L[ℝ] ℝ

/-- Coefficients in a specified chart, obtained using its actual tangent map. -/
def inChart {k : ℕ} (form : Form E M k) (e : OpenPartialHomeomorph M E) (y : E) :
    E [⋀^Fin k]→L[ℝ] ℝ :=
  (form (e.symm y)).compContinuousLinearMap (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm y)

def IsSmooth {k : ℕ} (form : Form E M k) : Prop :=
  ∀ e ∈ atlas E M, ContDiffOn ℝ ∞ (inChart form e) e.target

/-- Pullback on the actual derivative of f. -/
def pullback {k : ℕ} (f : M → N) (form : Form F N k) : Form E M k :=
  fun x => (form (f x)).compContinuousLinearMap (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x)

/-- Exterior derivative in a chart, transported to the tangent space at x. -/
def exteriorDerivative {k : ℕ} (form : Form E M k) : Form E M (k + 1) :=
  fun x =>
    let e := chartAt E x
    (extDeriv (inChart form e) (e x)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e x)

def IsClosed {k : ℕ} (form : Form E M k) : Prop := exteriorDerivative form = 0

def IsExact {k : ℕ} (form : Form E M (k + 1)) : Prop :=
  ∃ η : Form E M k, IsSmooth η ∧ exteriorDerivative η = form

/-- A nowhere-zero smooth top form supplies the orientation and its positive
volume form together; no free orientability flag is used. -/
def IsVolumeForm {n : ℕ} (form : Form (Fin n → ℝ) M n)
    [ChartedSpace (Fin n → ℝ) M] : Prop :=
  IsSmooth form ∧ ∀ x, form x ≠ 0

end ConstructionTargets.ManifoldFormTargets
