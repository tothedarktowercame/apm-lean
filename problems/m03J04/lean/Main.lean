import Mathlib

/-! # APM m03J04: adjoints, annihilators, and an inf-sup condition

## Statement repairs

The displayed supremum divides by `‖w‖` while quantifying over all `w`, including
zero.  The standard inf-sup expression, and the one used below, ranges over
`w ≠ 0`.
-/

noncomputable section

/-- The adjoint defined by transposing the bilinear pairing. -/
def dualAdjoint {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B : V →L[ℝ] W →L[ℝ] ℝ) : W →L[ℝ] V →L[ℝ] ℝ :=
  B.flip

/-- Functionals vanishing on a subset. -/
def dualAnnihilator {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] (U : Set W) :
    Submodule ℝ (W →L[ℝ] ℝ) :=
  ⨅ w : U, ((ContinuousLinearMap.apply ℝ ℝ) w.1).ker

/-- All four parts: continuity and involutivity of the adjoint, closedness of
annihilators, the closure-of-range identity, and the inf-sup isomorphism. -/
theorem apm_m03j04
    (V W : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (B : V →L[ℝ] W →L[ℝ] ℝ) :
    dualAdjoint (dualAdjoint B) = B ∧
    (∀ U : Set W, IsClosed (dualAnnihilator U : Set (W →L[ℝ] ℝ))) ∧
    closure (B.range : Set (W →L[ℝ] ℝ)) =
      (dualAnnihilator ((dualAdjoint B).ker : Set W) : Set (W →L[ℝ] ℝ)) ∧
    ((∃ α : ℝ, 0 < α ∧ ∀ v : V,
      sSup {r : ℝ | ∃ w : W, w ≠ 0 ∧ r = B v w / ‖w‖} ≥ α * ‖v‖) →
      ∃ e : V ≃L[ℝ]
          dualAnnihilator ((dualAdjoint B).ker : Set W),
        ∀ v : V, (e v).1 = B v) := by
  sorry
