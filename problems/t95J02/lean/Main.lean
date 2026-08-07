import Mathlib

/-! # APM t95J02: retractions of the Klein bottle onto its core circles

## Statement repairs

None.

## Encoding question

The standard square picture is encoded as the quotient of `ℝ × ℝ` generated
by vertical translation and a horizontal glide reflection. The two circles
are the images of the coordinate axes, bundled as subspaces of that concrete
quotient, and their inclusions are the corresponding continuous subtype maps.
-/

open CategoryTheory

noncomputable section

/-- Generating identifications `(x,y) ∼ (x+1,-y)` and
`(x,y) ∼ (x,y+1)` for the Klein bottle. -/
inductive t95J02KleinRel : (ℝ × ℝ) → (ℝ × ℝ) → Prop
  | glide (x y : ℝ) : t95J02KleinRel (x, y) (x + 1, -y)
  | vertical (x y : ℝ) : t95J02KleinRel (x, y) (x, y + 1)

def t95J02KleinBottleType :=
  Quotient (Relation.EqvGen.setoid t95J02KleinRel)

noncomputable instance : TopologicalSpace t95J02KleinBottleType :=
  TopologicalSpace.coinduced
    (fun p : ℝ × ℝ ↦ Quotient.mk (Relation.EqvGen.setoid t95J02KleinRel) p)
    inferInstance

def t95J02QuotientPoint (p : ℝ × ℝ) : t95J02KleinBottleType :=
  Quotient.mk _ p

def t95J02KleinBottle : TopCat := TopCat.of t95J02KleinBottleType

/-- The horizontal core circle in the standard quotient picture. -/
def t95J02CircleA : TopCat :=
  TopCat.of {z : t95J02KleinBottleType // ∃ x : ℝ, z = t95J02QuotientPoint (x, 0)}

/-- The vertical core circle in the standard quotient picture. -/
def t95J02CircleB : TopCat :=
  TopCat.of {z : t95J02KleinBottleType // ∃ y : ℝ, z = t95J02QuotientPoint (0, y)}

def t95J02InclusionA : t95J02CircleA ⟶ t95J02KleinBottle :=
  ⟨Subtype.val, continuous_subtype_val⟩

def t95J02InclusionB : t95J02CircleB ⟶ t95J02KleinBottle :=
  ⟨Subtype.val, continuous_subtype_val⟩

def HasT95J02Retraction {A X : TopCat} (i : A ⟶ X) : Prop :=
  ∃ r : X ⟶ A, i ≫ r = 𝟙 A

theorem apm_t95j02 :
    HasT95J02Retraction t95J02InclusionA ∧
    ¬HasT95J02Retraction t95J02InclusionB := by
  sorry
