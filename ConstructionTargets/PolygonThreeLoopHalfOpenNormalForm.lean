import ConstructionTargets.PolygonSixEdgeInteriorUniqueness

noncomputable section

namespace ConstructionTargets.PolygonThreeLoopHalfOpenNormalForm

open PointWedgeQuotient
open IntervalEndpointQuotientCircle
open ThreeEndpointLoopsHomeomorph
open PolygonBoundaryThreeLoopSurjectivityReduction

def halfOpenToInterval (t : Set.Ico (0 : ℝ) 1) : Interval :=
  ⟨t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

theorem endpointQuotient_halfOpen_rep (x : EndpointQuotient) :
    ∃ t : Set.Ico (0 : ℝ) 1,
      x = intervalQuotientMap (halfOpenToInterval t) := by
  induction x using Quot.ind with
  | _ t =>
      by_cases ht : t.1 < 1
      · exact ⟨⟨t.1, t.2.1, ht⟩, rfl⟩
      · have ht1 : t.1 = 1 := by linarith [t.2.2]
        refine ⟨⟨0, by norm_num⟩, ?_⟩
        rw [show t = ⟨1, by norm_num⟩ by apply Subtype.ext; exact ht1]
        exact intervalQuotientMap_zero_eq_one.symm

theorem twoEndpointLoops_halfOpen_rep (x : TwoEndpointLoops) :
    (∃ t : Set.Ico (0 : ℝ) 1,
      x = quotientMap endpointBase endpointBase
        (.inl (intervalQuotientMap (halfOpenToInterval t)))) ∨
    (∃ t : Set.Ico (0 : ℝ) 1,
      x = quotientMap endpointBase endpointBase
        (.inr (intervalQuotientMap (halfOpenToInterval t)))) := by
  induction x using Quotient.inductionOn with
  | _ s =>
      cases s with
      | inl a =>
          obtain ⟨t, rfl⟩ := endpointQuotient_halfOpen_rep a
          exact Or.inl ⟨t, rfl⟩
      | inr b =>
          obtain ⟨t, rfl⟩ := endpointQuotient_halfOpen_rep b
          exact Or.inr ⟨t, rfl⟩

theorem threeEndpointLoops_halfOpen_rep (x : ThreeEndpointLoops) :
    (∃ t : Set.Ico (0 : ℝ) 1, x = firstLoopPoint (halfOpenToInterval t)) ∨
    (∃ t : Set.Ico (0 : ℝ) 1, x = secondLoopPoint (halfOpenToInterval t)) ∨
    (∃ t : Set.Ico (0 : ℝ) 1, x = thirdLoopPoint (halfOpenToInterval t)) := by
  induction x using Quotient.inductionOn with
  | _ s =>
      cases s with
      | inl a =>
          rcases twoEndpointLoops_halfOpen_rep a with ⟨t, rfl⟩ | ⟨t, rfl⟩
          · exact Or.inl ⟨t, rfl⟩
          · exact Or.inr (Or.inl ⟨t, rfl⟩)
      | inr b =>
          obtain ⟨t, rfl⟩ := endpointQuotient_halfOpen_rep b
          exact Or.inr (Or.inr ⟨t, rfl⟩)

end ConstructionTargets.PolygonThreeLoopHalfOpenNormalForm
