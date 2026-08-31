import Mathlib
import ConstructionTargets.ProductEvenlyCoveredTrivialization

/-!
# The coordinatewise deck action for the square map on the torus

This file packages the four sign changes of `Circle × Circle`, independently
of any particular problem statement.
-/

namespace ConstructionTargets.TorusSquareDeckAction

open ConstructionTargets.ProductEvenlyCoveredTrivialization

noncomputable section

abbrev Torus := Circle × Circle
abbrev Deck := ZMod 2 × ZMod 2

/-- Multiplication by `-1` on the circle. -/
def antipode (z : Circle) : Circle :=
  ⟨-(z : ℂ), by simp [Submonoid.unitSphere]⟩

/-- The nontrivial element of `ZMod 2` acts antipodally. -/
def signAction (g : ZMod 2) (z : Circle) : Circle :=
  if g = 0 then z else antipode z

/-- The coordinatewise action of the four-element deck group. -/
def deckAction (g : Deck) (x : Torus) : Torus :=
  (signAction g.1 x.1, signAction g.2 x.2)

/-- Coordinatewise squaring on the torus. -/
def squareCover (x : Torus) : Torus := (x.1 ^ 2, x.2 ^ 2)

lemma antipode_involutive (z : Circle) : antipode (antipode z) = z := by
  ext
  simp [antipode]

lemma antipode_ne_self (z : Circle) : antipode z ≠ z := by
  intro h
  have hc : -(z : ℂ) = (z : ℂ) := congrArg Subtype.val h
  have hz : (z : ℂ) = 0 := neg_eq_self.mp hc
  have hn := z.property
  rw [hz] at hn
  simp [Submonoid.unitSphere] at hn

lemma antipode_sq (z : Circle) : (antipode z) ^ 2 = z ^ 2 := by
  ext
  simp [antipode, pow_two]

lemma continuous_antipode : Continuous antipode := by
  simpa only [antipode] using
    (continuous_subtype_val.neg : Continuous fun z : Circle => -(z : ℂ)).subtype_mk
      (fun z => by simp [Submonoid.unitSphere])

lemma signAction_zero (z : Circle) : signAction 0 z = z := by
  simp [signAction]

lemma signAction_add (g h : ZMod 2) (z : Circle) :
    signAction (g + h) z = signAction g (signAction h z) := by
  have hg : g = 0 ∨ g = 1 := by
    fin_cases g
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hh : h = 0 ∨ h = 1 := by
    fin_cases h
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hg with rfl | rfl <;> rcases hh with rfl | rfl
  all_goals simp [signAction, show (1 : ZMod 2) + 1 = 0 by decide,
    antipode_involutive]

lemma continuous_signAction (g : ZMod 2) : Continuous (signAction g) := by
  by_cases hg : g = 0
  · subst g
    simpa only [signAction, if_pos rfl] using (continuous_id : Continuous (fun z : Circle => z))
  · change Continuous (fun z : Circle => if g = 0 then z else antipode z)
    simpa only [if_neg hg] using continuous_antipode

lemma signAction_sq (g : ZMod 2) (z : Circle) :
    (signAction g z) ^ 2 = z ^ 2 := by
  by_cases hg : g = 0
  · simp [signAction, hg]
  · simp [signAction, hg, antipode_sq]

lemma signAction_fixed (g : ZMod 2) (z : Circle)
    (h : signAction g z = z) : g = 0 := by
  by_contra hg
  exact antipode_ne_self z (by simpa [signAction, hg] using h)

lemma squareCover_isCoveringMap : IsCoveringMap squareCover := by
  letI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  have h : IsCoveringMap (fun z : Circle => z ^ 2) :=
    (Circle.isQuotientCoveringMap_npow 2).isCoveringMap
  simpa [squareCover, productMap] using isCoveringMap_productMap h h

lemma deckAction_zero (x : Torus) : deckAction 0 x = x := by
  ext <;> simp [deckAction, signAction_zero]

lemma deckAction_add (g h : Deck) (x : Torus) :
    deckAction (g + h) x = deckAction g (deckAction h x) := by
  ext <;> simp [deckAction, signAction_add]

lemma continuous_deckAction (g : Deck) : Continuous (deckAction g) := by
  change Continuous (fun x : Torus => (signAction g.1 x.1, signAction g.2 x.2))
  exact ((continuous_signAction g.1).comp continuous_fst).prodMk
    ((continuous_signAction g.2).comp continuous_snd)

lemma squareCover_deckAction (g : Deck) (x : Torus) :
    squareCover (deckAction g x) = squareCover x := by
  simp [squareCover, deckAction, signAction_sq]

lemma deckAction_free (g : Deck) (x : Torus)
    (h : deckAction g x = x) : g = 0 := by
  apply Prod.ext
  · exact signAction_fixed g.1 x.1 (congrArg Prod.fst h)
  · exact signAction_fixed g.2 x.2 (congrArg Prod.snd h)

/-- Choosing independently equality or antipodality in each coordinate
produces the corresponding deck transformation. -/
lemma exists_deckAction_eq_of_coordinate_choices (x y : Torus)
    (h₁ : x.1 = y.1 ∨ x.1 = antipode y.1)
    (h₂ : x.2 = y.2 ∨ x.2 = antipode y.2) :
    ∃ g : Deck, deckAction g x = y := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact ⟨(0, 0), by simp [deckAction, signAction, h₁, h₂]⟩
  · exact ⟨(0, 1), by
      ext <;> simp [deckAction, signAction, h₁, h₂, antipode_involutive]⟩
  · exact ⟨(1, 0), by
      ext <;> simp [deckAction, signAction, h₁, h₂, antipode_involutive]⟩
  · exact ⟨(1, 1), by
      ext <;> simp [deckAction, signAction, h₁, h₂, antipode_involutive]⟩

end

end ConstructionTargets.TorusSquareDeckAction
