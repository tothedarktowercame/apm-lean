/-
  C7 — Learn-to-Swim: Monadic integration

  arxiv-1108.2913: A Banach space with enough Pettis integrals is
  an M-algebra for the signed-measure monad.

  We formalise the key algebraic properties: Dirac evaluation (unit law)
  and linearity of integration in the measure (algebra map property).
-/
import Mathlib

open MeasureTheory Measure

/-- The unit law: integrating f against δ_a evaluates f at a.
    This is the monad unit: η(a) = δ_a, and c(η(a)) = a. -/
theorem monad_unit_law {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : α → E) (a : α) :
    ∫ x, f x ∂(dirac a) = f a :=
  integral_dirac f a

/-- Linearity of integration in the measure: c(μ + ν) = c(μ) + c(ν).
    This is part of what makes integration an algebra map. -/
theorem algebra_map_additive
    {α : Type*} [MeasurableSpace α]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : α → E) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfμ : Integrable f μ) (hfν : Integrable f ν) :
    ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ x, f x ∂ν :=
  integral_add_measure hfμ hfν

-- Note: scalar multiplication theorem (c(r•μ) = r•c(μ)) requires
-- careful type alignment between ENNReal and ℝ scalars.
-- The key Mathlib lemma is `integral_smul_measure`.
