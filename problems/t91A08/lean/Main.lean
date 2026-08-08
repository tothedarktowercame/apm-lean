import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Fourier.AddCircle

/-!
# APM t91A08 — a two-form on the torus

The torus is the genuine quotient `(ℝ/ℤ)²`, equipped with its normalized Haar
measure.  Forms are continuous fields of alternating continuous multilinear
maps on the standard tangent model.  Descent is expressed along the quotient
map, pullback uses the actual derivative matrix, and integration is a Haar
integral over the torus.

## Statement repairs

None.

## Encoding questions

The tangent bundle of the quotient Lie group is represented in its canonical
translation trivialization by `ℝ²`; this is why every fiber below has the same
model vector space.

The alternating-form and Haar-integral encoding follows `t01J06`.
-/

open MeasureTheory
open scoped LinearAlgebra

noncomputable section

abbrev T91A08Torus := UnitAddCircle × UnitAddCircle
abbrev T91A08R2 := EuclideanSpace ℝ (Fin 2)
abbrev T91A08Alt2 := T91A08R2 [⋀^Fin 2]→L[ℝ] ℝ
abbrev T91A08Form2 := C(T91A08Torus, T91A08Alt2)

/-- The quotient covering `ℝ² → (ℝ/ℤ)²`. -/
def t91A08Cover (x : T91A08R2) : T91A08Torus :=
  (x 0, x 1)

/-- Pointwise descent of `3 dx ∧ dy` along the quotient covering. -/
def t91A08IsInduced (beta : T91A08Form2) : Prop :=
  ∀ (x : T91A08R2) (v : Fin 2 → T91A08R2),
    beta (t91A08Cover x) v =
      3 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)

def t91A08Linear (u : T91A08R2) : T91A08R2 :=
  WithLp.toLp 2 ![5 * u 0 + 2 * u 1, 4 * u 0 + 3 * u 1]

/-- The torus map induced by the integer matrix `[[5,2],[4,3]]`. -/
def t91A08g : C(T91A08Torus, T91A08Torus) :=
  ⟨fun p ↦ (5 • p.1 + 2 • p.2, 4 • p.1 + 3 • p.2), by fun_prop⟩

/-- `gamma` is the pullback of `beta` by `g`, in translation-trivialized
tangent coordinates. -/
def t91A08IsPullback (gamma beta : T91A08Form2) : Prop :=
  ∀ (p : T91A08Torus) (v : Fin 2 → T91A08R2),
    gamma p v = beta (t91A08g p) (fun i ↦ t91A08Linear (v i))

/-- Integral of a top-degree form against normalized Haar measure, using the
standard oriented translation-invariant frame. -/
def t91A08Integral (beta : T91A08Form2) : ℝ :=
  ∫ p : T91A08Torus,
    beta p ![EuclideanSpace.single 0 1, EuclideanSpace.single 1 1]

theorem apm_t91a08
    (beta gamma : T91A08Form2)
    (hbeta : t91A08IsInduced beta)
    (hgamma : t91A08IsPullback gamma beta) :
    t91A08Integral beta = 3 ∧
    t91A08Integral gamma = 21 ∧
    ¬ ContinuousMap.Homotopic t91A08g (ContinuousMap.id T91A08Torus) := by
  sorry
