import Mathlib

/-! # APM t01A05: oriented finite covers, integrals, and intersections

## Statement repairs

The construction in part (a) requires `k > 0`; a zero-sheeted map is not a
covering of a nonempty compact surface.

## Encoding question

Mathlib does not yet bundle oriented smooth manifolds together with integration
of differential forms, oriented submanifolds, and intersection numbers.  Those
specific geometric types and operations are retained below as `sorry`-typed
placeholders.  This preserves the full manifold, top-form, pullback, preimage,
and intersection-number statement instead of replacing it by cardinalities or
ordinary scalar integrals.
-/

open CategoryTheory

def IsT01A05CompactOrientedManifold (n : ℕ) (X : TopCat) : Prop := by sorry

def IsT01A05KSheetedOrientationPreservingCover
    {X Y : TopCat} (k : ℕ) (π : X ⟶ Y) : Prop := by sorry

def T01A05TopForm (n : ℕ) (X : TopCat) : Type := by sorry

def t01A05Pullback {n : ℕ} {X Y : TopCat} (π : X ⟶ Y)
    (ω : T01A05TopForm n Y) : T01A05TopForm n X := by sorry

def t01A05Integral {n : ℕ} {X : TopCat} (ω : T01A05TopForm n X) : ℝ := by sorry

def T01A05OrientedSubmanifold (d : ℕ) (X : TopCat) : Type := by sorry

def IsT01A05CompactSubmanifold {d : ℕ} {X : TopCat}
    (Z : T01A05OrientedSubmanifold d X) : Prop := by sorry

def t01A05PreimageSubmanifold {d : ℕ} {X Y : TopCat} (π : X ⟶ Y)
    (Z : T01A05OrientedSubmanifold d Y) : T01A05OrientedSubmanifold d X := by sorry

def t01A05IntersectionNumber {n d₁ d₂ : ℕ} {X : TopCat}
    (Z₁ : T01A05OrientedSubmanifold d₁ X)
    (Z₂ : T01A05OrientedSubmanifold d₂ X) : ℤ := by sorry

theorem apm_t01a05 :
    (∀ k : ℕ, 0 < k → ∃ (X Xtilde : TopCat) (π : Xtilde ⟶ X),
      IsT01A05CompactOrientedManifold 2 X ∧
      IsT01A05CompactOrientedManifold 2 Xtilde ∧
      IsT01A05KSheetedOrientationPreservingCover k π) ∧
    (∀ (n k : ℕ) (X Xtilde : TopCat) (π : Xtilde ⟶ X),
      IsT01A05CompactOrientedManifold n X →
      IsT01A05CompactOrientedManifold n Xtilde →
      IsT01A05KSheetedOrientationPreservingCover k π →
      ∀ ω : T01A05TopForm n X,
        t01A05Integral (t01A05Pullback π ω) = k * t01A05Integral ω) ∧
    (∀ (n d₁ d₂ k : ℕ) (hdim : d₁ + d₂ = n)
      (X Xtilde : TopCat) (π : Xtilde ⟶ X),
      IsT01A05CompactOrientedManifold n X →
      IsT01A05CompactOrientedManifold n Xtilde →
      IsT01A05KSheetedOrientationPreservingCover k π →
      ∀ (Z₁ : T01A05OrientedSubmanifold d₁ X)
        (Z₂ : T01A05OrientedSubmanifold d₂ X),
        IsT01A05CompactSubmanifold Z₁ → IsT01A05CompactSubmanifold Z₂ →
        IsT01A05CompactSubmanifold (t01A05PreimageSubmanifold π Z₁) ∧
        IsT01A05CompactSubmanifold (t01A05PreimageSubmanifold π Z₂) ∧
        t01A05IntersectionNumber (n := n)
            (t01A05PreimageSubmanifold π Z₁)
            (t01A05PreimageSubmanifold π Z₂) =
          k * t01A05IntersectionNumber (n := n) Z₁ Z₂) := by
  sorry
