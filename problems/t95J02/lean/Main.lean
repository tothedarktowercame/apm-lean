import Mathlib

/-! # APM t95J02: retractions of the Klein bottle onto its core circles

## Statement repairs

None.

## Encoding question

The two circles are specified only by the standard square picture, and Mathlib
has no bundled Klein-bottle model with these embeddings.  The Klein bottle,
circles, and inclusions are retained as named `TopCat` placeholders.
-/

open CategoryTheory

def t95J02KleinBottle : TopCat := by sorry
def t95J02CircleA : TopCat := by sorry
def t95J02CircleB : TopCat := by sorry
def t95J02InclusionA : t95J02CircleA ⟶ t95J02KleinBottle := by sorry
def t95J02InclusionB : t95J02CircleB ⟶ t95J02KleinBottle := by sorry

def HasT95J02Retraction {A X : TopCat} (i : A ⟶ X) : Prop :=
  ∃ r : X ⟶ A, i ≫ r = 𝟙 A

theorem apm_t95j02 :
    HasT95J02Retraction t95J02InclusionA ∧
    ¬HasT95J02Retraction t95J02InclusionB := by
  sorry
