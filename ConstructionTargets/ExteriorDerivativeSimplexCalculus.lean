import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Explicit exterior derivatives and the standard oriented triangle -/

open MeasureTheory Set
noncomputable section

namespace ConstructionTargets.ExteriorDerivativeSimplexCalculus

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev Form (k : ℕ) := E3 → E3 [⋀^Fin k]→L[ℝ] ℝ

def IsAlpha (alpha : Form 1) : Prop := ∀ x v,
  alpha x v = x 0 * v 0 1 - x 1 * v 0 0

def IsBeta (beta : Form 2) : Prop := ∀ x v,
  beta x v =
    x 0 * (v 0 1 * v 1 2 - v 0 2 * v 1 1) +
    x 1 * (v 0 2 * v 1 0 - v 0 0 * v 1 2) +
    x 2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)

def IsGamma (gamma : Form 3) : Prop := ∀ x v,
  gamma x v =
    v 0 0 * (v 1 1 * v 2 2 - v 1 2 * v 2 1) -
    v 0 1 * (v 1 0 * v 2 2 - v 1 2 * v 2 0) +
    v 0 2 * (v 1 0 * v 2 1 - v 1 1 * v 2 0)

lemma fderiv_coordinateLinear (a b c : ℝ) (x w : E3) :
    fderiv ℝ (fun y : E3 => y 0 * a + y 1 * b + y 2 * c) x w =
      w 0 * a + w 1 * b + w 2 * c := by
  let L : E3 →L[ℝ] ℝ :=
    a • EuclideanSpace.proj 0 + b • EuclideanSpace.proj 1 +
      c • EuclideanSpace.proj 2
  have h : HasFDerivAt (fun y : E3 => L y) L x := L.hasFDerivAt
  have hf := h.fderiv
  change fderiv ℝ (fun y : E3 => y 0 * a + y 1 * b + y 2 * c) x w = _
  rw [show (fun y : E3 => y 0 * a + y 1 * b + y 2 * c) = L by
    funext y
    simp [L, mul_comm]]
  rw [hf]
  simp [L, mul_comm]

lemma extDeriv_alpha (alpha : Form 1) (ha : IsAlpha alpha)
    (hda : Differentiable ℝ alpha) (x : E3) (v : Fin 2 → E3) :
    extDeriv alpha x v = 2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0) := by
  rw [extDeriv_apply (hda x)]
  rw [Fin.sum_univ_two]
  have h0 : (fun y => alpha y (Fin.removeNth 0 v)) =
      fun y => y 0 * v 1 1 + y 1 * (-v 1 0) + y 2 * 0 := by
    funext y
    rw [ha y (Fin.removeNth 0 v)]
    simp [Fin.removeNth, Fin.tail]
    ring
  have h1 : (fun y => alpha y (Fin.removeNth 1 v)) =
      fun y => y 0 * v 0 1 + y 1 * (-v 0 0) + y 2 * 0 := by
    funext y
    rw [ha y (Fin.removeNth 1 v)]
    simp [Fin.removeNth, Fin.tail]
    ring
  rw [h0, h1]
  rw [fderiv_coordinateLinear, fderiv_coordinateLinear]
  simp
  ring

lemma extDeriv_beta (beta : Form 2) (hb : IsBeta beta)
    (hdb : Differentiable ℝ beta) (x : E3) (v : Fin 3 → E3) :
    extDeriv beta x v = 3 *
      (v 0 0 * (v 1 1 * v 2 2 - v 1 2 * v 2 1) -
       v 0 1 * (v 1 0 * v 2 2 - v 1 2 * v 2 0) +
       v 0 2 * (v 1 0 * v 2 1 - v 1 1 * v 2 0)) := by
  rw [extDeriv_apply (hdb x)]
  rw [Fin.sum_univ_three]
  simp_rw [show ∀ i : Fin 3, (fun y => beta y (i.removeNth v)) = fun y =>
      y 0 * ((i.removeNth v) 0 1 * (i.removeNth v) 1 2 -
        (i.removeNth v) 0 2 * (i.removeNth v) 1 1) +
      y 1 * ((i.removeNth v) 0 2 * (i.removeNth v) 1 0 -
        (i.removeNth v) 0 0 * (i.removeNth v) 1 2) +
      y 2 * ((i.removeNth v) 0 0 * (i.removeNth v) 1 1 -
        (i.removeNth v) 0 1 * (i.removeNth v) 1 0) by
    intro i; funext y; exact hb y _]
  simp_rw [fderiv_coordinateLinear]
  simp [Fin.removeNth, Fin.tail]
  have hs : v (Fin.succAbove (2 : Fin 3) (1 : Fin 2)) = v 1 := by congr 1
  rw [hs]
  ring

lemma extDeriv_gamma (gamma : Form 3) (hg : IsGamma gamma)
    (hdg : Differentiable ℝ gamma) : extDeriv gamma = 0 := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  rw [extDeriv_apply (hdg x)]
  simp_rw [show ∀ i : Fin 4, (fun y => gamma y (i.removeNth v)) = fun _y =>
      (i.removeNth v) 0 0 * ((i.removeNth v) 1 1 * (i.removeNth v) 2 2 -
        (i.removeNth v) 1 2 * (i.removeNth v) 2 1) -
      (i.removeNth v) 0 1 * ((i.removeNth v) 1 0 * (i.removeNth v) 2 2 -
        (i.removeNth v) 1 2 * (i.removeNth v) 2 0) +
      (i.removeNth v) 0 2 * ((i.removeNth v) 1 0 * (i.removeNth v) 2 1 -
        (i.removeNth v) 1 1 * (i.removeNth v) 2 0) by
    intro i; funext y; exact hg y _]
  simp

/-- Iterated-coordinate integral over the oriented triangle
`0 ≤ x`, `0 ≤ y`, `x + y ≤ 1`. -/
def orientedTriangleIntegral (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1 - x), f x y

/-- A constant two-form of value `2` integrates to `1` over the standard
oriented triangle. -/
lemma integral_const_two_triangle : orientedTriangleIntegral (fun _ _ => 2) = 1 := by
  simp [orientedTriangleIntegral]
  have hc : IntervalIntegrable (fun _x : ℝ => (1 : ℝ)) volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hi : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub hc hi, intervalIntegral.integral_const,
    show (∫ x : ℝ in (0 : ℝ)..1, x) = 1 / 2 by
      simpa using (integral_pow (a := (0 : ℝ)) (b := 1) 1)]
  norm_num

#print axioms extDeriv_alpha
#print axioms extDeriv_beta
#print axioms extDeriv_gamma
#print axioms integral_const_two_triangle

end ConstructionTargets.ExteriorDerivativeSimplexCalculus
