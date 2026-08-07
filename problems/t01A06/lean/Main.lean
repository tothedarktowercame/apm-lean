import Mathlib

/-! # APM t01A06: differential forms and periods on an embedded torus

## Statement repairs

None.

## Encoding note

Mathlib does not yet bundle integration of differential forms over manifolds.
The surface integral is encoded by the pullback of the printed two-form along
the standard outward-oriented torus parametrization.  An ambient one-form is
encoded without loss as a smooth field of continuous linear covectors on
`ℝ³`; closedness is symmetry of its derivative.
-/

open MeasureTheory
open scoped ContDiff

noncomputable section

abbrev t01A06Point := EuclideanSpace ℝ (Fin 3)
abbrev t01A06OneForm := t01A06Point → (t01A06Point →L[ℝ] ℝ)

def t01A06Torus (R r : ℝ) : Set t01A06Point :=
  {p | (Real.sqrt (p 0 ^ 2 + p 1 ^ 2) - R) ^ 2 + p 2 ^ 2 = r ^ 2}

def t01A06Param (R r u v : ℝ) : t01A06Point :=
  EuclideanSpace.equiv (Fin 3) ℝ |>.symm
    ![(R + r * Real.cos v) * Real.cos u,
      (R + r * Real.cos v) * Real.sin u,
      r * Real.sin v]

def t01A06OmegaPullback (R r u v : ℝ) : ℝ :=
  r * (R + r * Real.cos v) ^ 2 * Real.sin u ^ 2 * Real.cos v

def t01A06SurfaceIntegral (R r : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..2 * Real.pi,
    ∫ v in (0 : ℝ)..2 * Real.pi, t01A06OmegaPullback R r u v

def IsT01A06ClosedOneForm (η : t01A06OneForm) : Prop :=
  ContDiff ℝ ∞ η ∧ ∀ (p v w : t01A06Point),
    fderiv ℝ η p v w = fderiv ℝ η p w v

def IsT01A06LoopOnTorus (R r : ℝ) (γ : ℝ → t01A06Point) : Prop :=
  ContDiff ℝ ∞ γ ∧
  (∀ t : ℝ, γ (t + 2 * Real.pi) = γ t) ∧
  ∀ t : ℝ, γ t ∈ t01A06Torus R r

def t01A06LineIntegral (η : t01A06OneForm) (γ : ℝ → t01A06Point) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi, η (γ t) (deriv γ t)

theorem apm_t01a06 :
    (∀ R r : ℝ, R > r → r > 0 →
      t01A06SurfaceIntegral R r = 2 * Real.pi ^ 2 * R * r ^ 2) ∧
    (∀ R r : ℝ, R > r → r > 0 →
      ¬∃ (η : t01A06OneForm) (γ : ℝ → t01A06Point),
        IsT01A06ClosedOneForm η ∧ IsT01A06LoopOnTorus R r γ ∧
        t01A06LineIntegral η γ ≠ 0) := by
  have hsurface : ∀ R r : ℝ, R > r → r > 0 →
      t01A06SurfaceIntegral R r = 2 * Real.pi ^ 2 * R * r ^ 2 := by
    intro R r _ _
    unfold t01A06SurfaceIntegral t01A06OmegaPullback
    have hv (u : ℝ) :
        (∫ v in (0 : ℝ)..2 * Real.pi,
          r * (R + r * Real.cos v) ^ 2 * Real.sin u ^ 2 * Real.cos v) =
          2 * Real.pi * R * r ^ 2 * Real.sin u ^ 2 := by
      rw [show (fun v : ℝ =>
          r * (R + r * Real.cos v) ^ 2 * Real.sin u ^ 2 * Real.cos v) =
          fun v => r * R ^ 2 * Real.sin u ^ 2 * Real.cos v +
            2 * R * r ^ 2 * Real.sin u ^ 2 * Real.cos v ^ 2 +
            r ^ 3 * Real.sin u ^ 2 * Real.cos v ^ 3 by
        funext v
        ring]
      rw [intervalIntegral.integral_add, intervalIntegral.integral_add] <;>
        try apply Continuous.intervalIntegrable <;> try fun_prop
      simp [integral_cos_sq, integral_cos_pow_three]
      ring
    simp_rw [hv]
    rw [intervalIntegral.integral_const_mul]
    simp [integral_sin_sq]
    ring
  have hexact : ∀ η : t01A06OneForm,
      IsT01A06ClosedOneForm η →
        ∃ g : t01A06Point → ℝ, ∀ p, HasFDerivAt g (η p) p := by
    intro η hη
    obtain ⟨g, hg⟩ := convex_univ.exists_forall_hasFDerivAt_of_fderiv_symmetric
      isOpen_univ (hη.1.differentiable (by simp)).differentiableOn
        fun p _ v w ↦ hη.2 p v w
    exact ⟨g, fun p ↦ hg p (Set.mem_univ p)⟩
  /- The ambient Poincaré lemma supplies a global potential.  Composing it
  with a smooth periodic loop identifies the line-integral integrand with the
  derivative of a periodic scalar function, whose interval integral is zero. -/
  refine ⟨hsurface, ?_⟩
  intro R r _ _
  rintro ⟨η, γ, hη, hγ, hne⟩
  obtain ⟨g, hg⟩ := hexact η hη
  apply hne
  unfold t01A06LineIntegral
  have hγdiff : Differentiable ℝ γ := hγ.1.differentiable (by simp)
  have hcomp (t : ℝ) :
      HasDerivAt (g ∘ γ) (η (γ t) (deriv γ t)) t :=
    (hg (γ t)).comp_hasDerivAt t hγdiff.differentiableAt.hasDerivAt
  have heq : (fun t => η (γ t) (deriv γ t)) = deriv (g ∘ γ) := by
    funext t
    exact (hcomp t).deriv.symm
  rw [heq]
  have hint : IntervalIntegrable (deriv (g ∘ γ)) volume 0 (2 * Real.pi) := by
    rw [← heq]
    apply Continuous.intervalIntegrable
    exact (hη.1.continuous.comp hγ.1.continuous).clm_apply
      (hγ.1.continuous_deriv (by simp))
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun t _ => (hcomp t).differentiableAt) hint]
  simp only [Function.comp_apply]
  rw [show γ (2 * Real.pi) = γ 0 by
    simpa using hγ.2.1 0]
  simp

#print axioms apm_t01a06
