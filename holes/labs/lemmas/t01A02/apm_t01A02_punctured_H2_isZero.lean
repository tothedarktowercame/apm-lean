import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.TorusSquareDeckAction
import ConstructionTargets.T01A02PuncturedTorusH2

open CategoryTheory
open CategoryTheory.Limits
open ConstructionTargets.TorusSquareDeckAction

abbrev apm_t01A02_Torus := Circle × Circle
abbrev apm_t01A02_Deck := ZMod 2 × ZMod 2

noncomputable section

def apm_t01A02_cover (x : apm_t01A02_Torus) : apm_t01A02_Torus :=
  (x.1 ^ 2, x.2 ^ 2)

def apm_t01A02_hasCoveringGroup
    {S T G : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [AddGroup G] (p : S → T) : Prop :=
  IsCoveringMap p ∧
  ∃ act : G → S → S,
    (∀ x, act 0 x = x) ∧
    (∀ g h x, act (g + h) x = act g (act h x)) ∧
    (∀ g, Continuous (act g)) ∧
    (∀ g x, p (act g x) = p x) ∧
    (∀ g x, act g x = x → g = 0) ∧
    (∀ x y, p x = p y ↔ ∃ g, act g x = y)

abbrev apm_t01A02_H2 (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t01A02_H2map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 2).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)

lemma apm_t01A02_cover_eq_prod_pow_two (x : apm_t01A02_Torus) :
    apm_t01A02_cover x = (x.1 ^ 2, x.2 ^ 2) := rfl

def apm_t01A02_antipode (z : Circle) : Circle :=
  ⟨-(z : ℂ), by
    simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using z.property⟩

lemma apm_t01A02_circle_sq_eq_sq_iff (z w : Circle) :
    z ^ 2 = w ^ 2 ↔ z = w ∨ z = apm_t01A02_antipode w := by
  constructor
  · intro h
    have hc : (z : ℂ) ^ 2 = (w : ℂ) ^ 2 := by exact_mod_cast h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc with hzw | hzw
    · exact Or.inl (Subtype.ext hzw)
    · exact Or.inr (Subtype.ext hzw)
  · rintro (rfl | rfl)
    · rfl
    · ext
      simp [apm_t01A02_antipode]

lemma apm_t01A02_cover_eq_iff (x y : apm_t01A02_Torus) :
    apm_t01A02_cover x = apm_t01A02_cover y ↔
      (x.1 = y.1 ∨ x.1 = apm_t01A02_antipode y.1) ∧
      (x.2 = y.2 ∨ x.2 = apm_t01A02_antipode y.2) := by
  simp only [apm_t01A02_cover, Prod.mk.injEq]
  exact and_congr (apm_t01A02_circle_sq_eq_sq_iff x.1 y.1)
    (apm_t01A02_circle_sq_eq_sq_iff x.2 y.2)

theorem apm_t01A02_covering_group :
    apm_t01A02_hasCoveringGroup
      (G := apm_t01A02_Deck) apm_t01A02_cover := by
  refine ⟨?_, deckAction, deckAction_zero, deckAction_add,
    continuous_deckAction, ?_, deckAction_free, ?_⟩
  · simpa [apm_t01A02_cover, squareCover] using squareCover_isCoveringMap
  · intro g x
    simpa [apm_t01A02_cover, squareCover] using squareCover_deckAction g x
  · intro x y
    constructor
    · intro hxy
      rcases (apm_t01A02_cover_eq_iff x y).mp hxy with ⟨h₁, h₂⟩
      apply exists_deckAction_eq_of_coordinate_choices x y
      · simpa [antipode, apm_t01A02_antipode] using h₁
      · simpa [antipode, apm_t01A02_antipode] using h₂
    · rintro ⟨g, rfl⟩
      exact (squareCover_deckAction g x).symm

/-- Transport the banked computation for the torus punctured at `(-1,-1)`
to a puncture at an arbitrary point, by coordinatewise circle translation. -/
-- BEGIN SEAT AREA
theorem apm_t01A02_punctured_H2_isZero (q : apm_t01A02_Torus) :
    IsZero (apm_t01A02_H2 {x : apm_t01A02_Torus // x ≠ q}) := by
  sorry
-- END SEAT AREA

theorem apm_t01A02_H2map_eq_zero
    (f : C(apm_t01A02_Torus, apm_t01A02_Torus))
    (hf : ¬Function.Surjective f) :
    apm_t01A02_H2map f = 0 := by
  simp only [Function.Surjective, not_forall, not_exists] at hf
  obtain ⟨q, hq⟩ := hf
  let W := {x : apm_t01A02_Torus // x ≠ q}
  let g : C(apm_t01A02_Torus, W) :=
    ⟨fun x ↦ ⟨f x, hq x⟩, f.continuous.subtype_mk _⟩
  let i : C(W, apm_t01A02_Torus) := ⟨fun x ↦ x.1, continuous_subtype_val⟩
  apply ConstructionTargets.T01A02PuncturedTorus.H2map_eq_zero_of_factor f g i
  · ext x <;> rfl
  · exact apm_t01A02_punctured_H2_isZero q

/-- LIBRARY: the torus fixed-point dichotomy.  Its proof is the integer-lift
and bounded-planar-perturbation argument: a fixed-point-free lift forces the
induced integer matrix to have invertible `I-A`, hence forces surjectivity. -/
theorem apm_t01A02_fixedPoint_or_surjective_of_lift
    (f : C(apm_t01A02_Torus, apm_t01A02_Torus))
    (hlift : ∃ g : C(apm_t01A02_Torus, apm_t01A02_Torus),
      ∀ x, f x = apm_t01A02_cover (g x)) :
    (∃ x, f x = x) ∨ Function.Surjective f := by
  sorry

theorem apm_t01a02 :
    ∀ f : C(apm_t01A02_Torus, apm_t01A02_Torus),
      ¬Function.Surjective f →
      apm_t01A02_H2map f = 0 ∧
      apm_t01A02_hasCoveringGroup
        (G := apm_t01A02_Deck) apm_t01A02_cover ∧
      ((∃ g : C(apm_t01A02_Torus, apm_t01A02_Torus),
          ∀ x, f x = apm_t01A02_cover (g x)) →
        ∃ x, f x = x) := by
  intro f hf
  refine ⟨apm_t01A02_H2map_eq_zero f hf, apm_t01A02_covering_group, ?_⟩
  intro hlift
  exact (apm_t01A02_fixedPoint_or_surjective_of_lift f hlift).resolve_right hf

#print axioms apm_t01a02
