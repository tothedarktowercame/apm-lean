import Mathlib

/-! # APM t92J08: complete integral curves of vector fields

## Statement repairs

None.

## Encoding question

Mathlib does not yet provide general smooth vector fields, their maximal flows,
or integral curves on arbitrary manifolds.  Those genuine objects and the
restriction relation between curves are retained as typed placeholders.  The
sufficient hypothesis is compactness of the manifold, and the counterexample
is the field `x² ∂/∂x` on `ℝ` with its finite-time blow-up curve.
-/

def T92J08SmoothManifold : Type := by sorry
def IsT92J08Compact (M : T92J08SmoothManifold) : Prop := by sorry
def T92J08SmoothVectorField (M : T92J08SmoothManifold) : Type := by sorry
def T92J08IntegralCurve {M : T92J08SmoothManifold}
    (X : T92J08SmoothVectorField M) : Type := by sorry
def IsT92J08CompleteCurve {M : T92J08SmoothManifold}
    {X : T92J08SmoothVectorField M} (γ : T92J08IntegralCurve X) : Prop := by sorry
def IsT92J08ContainedIn {M : T92J08SmoothManifold}
    {X : T92J08SmoothVectorField M}
    (γ δ : T92J08IntegralCurve X) : Prop := by sorry

def t92J08RealLine : T92J08SmoothManifold := by sorry
def t92J08QuadraticField : T92J08SmoothVectorField t92J08RealLine := by sorry
def t92J08BlowupCurve : T92J08IntegralCurve t92J08QuadraticField := by sorry

theorem apm_t92j08 :
    (∀ (M : T92J08SmoothManifold), IsT92J08Compact M →
      ∀ (X : T92J08SmoothVectorField M) (γ : T92J08IntegralCurve X),
        ∃ δ : T92J08IntegralCurve X,
          IsT92J08CompleteCurve δ ∧ IsT92J08ContainedIn γ δ) ∧
    ¬∃ δ : T92J08IntegralCurve t92J08QuadraticField,
      IsT92J08CompleteCurve δ ∧ IsT92J08ContainedIn t92J08BlowupCurve δ := by
  sorry
