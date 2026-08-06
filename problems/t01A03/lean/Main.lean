import Mathlib

/-! # APM t01A03: three retraction problems for surfaces

## Statement repairs

None.

## Encoding question

The source specifies all three spaces only by pictures, and Mathlib has no
bundled models of the closed genus-two surface, its separating curves, or the
standard CW embedding `S¹ ∨ S¹ ↪ T²`.  The six pictured spaces and their three
inclusions are therefore retained as explicitly named, `sorry`-typed `TopCat`
placeholders.  The theorem states the requested decisions about those genuine
topological objects; it does not replace them by algebraic shadows.
-/

open CategoryTheory

def t01A03MiddleCircle : TopCat := by sorry
def t01A03GenusTwoA : TopCat := by sorry
def t01A03MiddleCircleInclusion : t01A03MiddleCircle ⟶ t01A03GenusTwoA := by sorry

def t01A03TwoCircleWedge : TopCat := by sorry
def t01A03Torus : TopCat := by sorry
def t01A03WedgeInclusion : t01A03TwoCircleWedge ⟶ t01A03Torus := by sorry

def t01A03SeparatingTwoCircles : TopCat := by sorry
def t01A03GenusTwoC : TopCat := by sorry
def t01A03TwoCirclesInclusion :
    t01A03SeparatingTwoCircles ⟶ t01A03GenusTwoC := by sorry

def HasT01A03Retraction {A X : TopCat} (i : A ⟶ X) : Prop :=
  ∃ r : X ⟶ A, i ≫ r = 𝟙 A

theorem apm_t01a03 :
    ¬HasT01A03Retraction t01A03MiddleCircleInclusion ∧
    ¬HasT01A03Retraction t01A03WedgeInclusion ∧
    ¬HasT01A03Retraction t01A03TwoCirclesInclusion := by
  sorry
