import ConstructionTargets.PlaneArcEndpointTotalDifferenceSubmersive

noncomputable section
open Set
open scoped ContDiff

namespace PlaneArcEndpointTotalDifferenceRelativeSubmersion
open PlaneArcEndpointTotalCoincidenceSmooth
open PlaneArcEndpointTotalDifferenceSubmersive

abbrev Plane := ℝ × ℝ

theorem totalDifference_differentiableAt (a b : ℝ → Plane) (U V : Set ℝ)
    (hU : IsOpen U) (hV : IsOpen V)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V)
    {t s : ℝ} (htU : t ∈ U) (hsV : s ∈ V) (va vb : Plane) :
    DifferentiableAt ℝ (totalDifference a b) ((t, s), (va, vb)) := by
  have hp : ((t, s), (va, vb)) ∈
      ((U ×ˢ V) ×ˢ (Set.univ : Set (Plane × Plane))) :=
    ⟨⟨htU, hsV⟩, mem_univ _⟩
  have hd := (totalDifference_contDiffOn a b U V ha hb).differentiableOn (by simp)
  exact (hd ((t, s), (va, vb)) hp).differentiableAt
    ((hU.prod hV).prod isOpen_univ |>.mem_nhds hp)

theorem fderiv_totalDifference_surjective_on_interior_direction
    (a b : ℝ → Plane) (U V : Set ℝ)
    (hU : IsOpen U) (hV : IsOpen V)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V)
    {t s : ℝ} (htU : t ∈ U) (hsV : s ∈ V) (va vb : Plane)
    (hdir : t ∈ Ioo (0 : ℝ) 1 ∨ s ∈ Ioo (0 : ℝ) 1) :
    Function.Surjective
      (fderiv ℝ (totalDifference a b) ((t, s), (va, vb))) := by
  have hd := totalDifference_differentiableAt a b U V hU hV ha hb htU hsV va vb
  rcases hdir with ht | hs
  · exact fderiv_totalDifference_surjective_of_left a b ht s va vb hd
  · exact fderiv_totalDifference_surjective_of_right a b t hs va vb hd

#print axioms totalDifference_differentiableAt
#print axioms fderiv_totalDifference_surjective_on_interior_direction

end PlaneArcEndpointTotalDifferenceRelativeSubmersion
