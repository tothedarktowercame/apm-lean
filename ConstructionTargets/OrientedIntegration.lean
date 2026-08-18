import Mathlib
import Mathlib.LinearAlgebra.Orientation

/-!
# Orientation-sensitive integration of top forms

This module supplies the algebraic and measure-theoretic core needed before
passing to oriented manifold charts.  A degree-`n` top form takes values in the
one-dimensional space of alternating `n`-forms on the model `ℝⁿ`; it is not an
arbitrary scalar function.  An orientation chooses the sign with which its
coefficient relative to the standard basis is integrated.
-/

open MeasureTheory

noncomputable section

namespace OrientedIntegration

/-- The real `n`-dimensional model space used by manifold charts. -/
abbrev Model (n : ℕ) := Fin n → ℝ

/-- Standard orientation of the chart model. -/
def standardOrientation (n : ℕ) : Orientation ℝ (Model n) (Fin n) :=
  (Pi.basisFun ℝ (Fin n)).orientation

/-- The sign of an orientation relative to the standard chart orientation. -/
def orientationSign {n : ℕ} (o : Orientation ℝ (Model n) (Fin n)) : ℝ :=
  by
    classical
    exact if o = standardOrientation n then 1 else -1

/-- A measurable degree-`n` top form, integrable relative to `volume`.

The `form` field genuinely has alternating degree `n`; its scalar coefficient
is obtained only after evaluation on the standard `n`-frame. -/
structure TopForm (n : ℕ) (X : Type*) [MeasurableSpace X]
    (volume : Measure X) where
  form : X → (Model n [⋀^Fin n]→ₗ[ℝ] ℝ)
  integrable_coefficient : Integrable
    (fun x => form x (fun i => Pi.basisFun ℝ (Fin n) i)) volume

/-- Scalar coefficient of a top form in the standard oriented frame. -/
def TopForm.coefficient {n : ℕ} {X : Type*} [MeasurableSpace X]
    {volume : Measure X} (ω : TopForm n X volume) (x : X) : ℝ :=
  ω.form x (fun i => Pi.basisFun ℝ (Fin n) i)

/-- Integral of a top form with respect to the chosen orientation. -/
def integral {n : ℕ} {X : Type*} [MeasurableSpace X]
    {volume : Measure X} (o : Orientation ℝ (Model n) (Fin n))
    (ω : TopForm n X volume) : ℝ :=
  orientationSign o * ∫ x, ω.coefficient x ∂volume

theorem orientationSign_standard (n : ℕ) :
    orientationSign (standardOrientation n) = 1 := by
  simp [orientationSign]

theorem orientationSign_neg {n : ℕ}
    (o : Orientation ℝ (Model n) (Fin n)) :
    orientationSign (-o) = -orientationSign o := by
  let s := standardOrientation n
  have hne : s ≠ -s := Module.Ray.ne_neg_self s
  have hne' : -s ≠ s := Ne.symm hne
  have hor : o = s ∨ o = -s := by
    simpa [s, standardOrientation] using
      (Pi.basisFun ℝ (Fin n)).orientation_eq_or_eq_neg o
  rcases hor with h | h
  · subst o
    simp [orientationSign, s, hne']
  · subst o
    have hnn : - -s = s := neg_neg s
    rw [hnn]
    rw [orientationSign_standard]
    simp [orientationSign, s, hne']

/-- Reversing orientation negates the integral. -/
theorem integral_neg_orientation {n : ℕ} {X : Type*} [MeasurableSpace X]
    {volume : Measure X} (o : Orientation ℝ (Model n) (Fin n))
    (ω : TopForm n X volume) :
    integral (-o) ω = -integral o ω := by
  simp [integral, orientationSign_neg]

/-- Sharp anti-vacuity witness.  The standard determinant `1`-form on the
oriented point integrates to `1`, while reversing orientation gives `-1`. -/
theorem integral_point_standard_and_reversed :
    let ω : TopForm 1 PUnit (Measure.dirac PUnit.unit) :=
      { form := fun _ => (Pi.basisFun ℝ (Fin 1)).det,
        integrable_coefficient := by simp }
    integral (standardOrientation 1) ω = 1 ∧
      integral (-(standardOrientation 1)) ω = -1 := by
  let b := Pi.basisFun ℝ (Fin 1)
  have hcoefficient :
      (fun _ : PUnit => b.det (fun i => b i)) = fun _ => (1 : ℝ) := by
    funext x
    exact b.det_self
  constructor
  · simp only [integral, orientationSign_standard, one_mul, TopForm.coefficient]
    rw [(show (fun _ : PUnit =>
        (Pi.basisFun ℝ (Fin 1)).det
          (fun i => Pi.basisFun ℝ (Fin 1) i)) = fun _ => (1 : ℝ) from
      hcoefficient)]
    simp
  · rw [integral_neg_orientation]
    simp only [integral, orientationSign_standard, one_mul, TopForm.coefficient]
    rw [(show (fun _ : PUnit =>
        (Pi.basisFun ℝ (Fin 1)).det
          (fun i => Pi.basisFun ℝ (Fin 1) i)) = fun _ => (1 : ℝ) from
      hcoefficient)]
    simp

end OrientedIntegration
