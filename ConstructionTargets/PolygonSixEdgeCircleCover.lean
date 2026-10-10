import ConstructionTargets.PolygonBoundaryThreeLoopSurjectivityReduction

noncomputable section

namespace ConstructionTargets.PolygonSixEdgeCircleCover

open PolygonBoundaryCircleRelations
open PolygonBoundaryCircleSource
open Surfaces
open PolygonBoundaryThreeLoopMaps
open PolygonBoundaryThreeLoopSurjectivityReduction

theorem circleEdgePoint_eq_toCircle (j : Fin 6) (t : Set.Icc (0 : ℝ) 1) :
    circleEdgePoint j t =
      AddCircle.toCircle (((j : ℕ) : ℝ) + t.1 : AddCircle (6 : ℝ)) := by
  apply Subtype.ext
  change Complex.exp _ = Complex.exp _
  congr 1
  push_cast
  ring

theorem sixEdgeCircleCover (z : Circle) :
    ∃ (j : Fin 6) (t : Set.Icc (0 : ℝ) 1), circleEdgePoint j t = z := by
  letI : Fact (0 < (6 : ℝ)) := ⟨by norm_num⟩
  let x : AddCircle (6 : ℝ) :=
    (AddCircle.homeomorphCircle (T := (6 : ℝ)) (by norm_num)).symm z
  let s := AddCircle.equivIco (6 : ℝ) 0 x
  have hs0 : 0 ≤ s.1 := s.2.1
  have hs6 : s.1 < 6 := by simpa using s.2.2
  have hsx : (s.1 : AddCircle (6 : ℝ)) = x := by
    apply (AddCircle.equivIco (6 : ℝ) 0).injective
    rw [AddCircle.equivIco_coe_eq]
  have hxz : AddCircle.toCircle x = z := by
    rw [← AddCircle.homeomorphCircle_apply]
    exact Homeomorph.apply_symm_apply _ z
  by_cases h1 : s.1 ≤ 1
  · refine ⟨0, ⟨s.1, hs0, h1⟩, ?_⟩
    rw [circleEdgePoint_eq_toCircle]
    simpa [hsx] using hxz
  by_cases h2 : s.1 ≤ 2
  · refine ⟨1, ⟨s.1 - 1, by linarith, by linarith⟩, ?_⟩
    rw [circleEdgePoint_eq_toCircle]
    norm_num
    simpa [hsx] using hxz
  by_cases h3 : s.1 ≤ 3
  · refine ⟨2, ⟨s.1 - 2, by linarith, by linarith⟩, ?_⟩
    rw [circleEdgePoint_eq_toCircle]
    norm_num
    simpa [hsx] using hxz
  by_cases h4 : s.1 ≤ 4
  · refine ⟨3, ⟨s.1 - 3, by linarith, by linarith⟩, ?_⟩
    rw [circleEdgePoint_eq_toCircle]
    norm_num
    simpa [hsx] using hxz
  by_cases h5 : s.1 ≤ 5
  · refine ⟨4, ⟨s.1 - 4, by linarith, by linarith⟩, ?_⟩
    rw [circleEdgePoint_eq_toCircle]
    norm_num
    simpa [hsx] using hxz
  · refine ⟨5, ⟨s.1 - 5, by linarith, by linarith⟩, ?_⟩
    rw [circleEdgePoint_eq_toCircle]
    norm_num
    simpa [hsx] using hxz

theorem surjective_n3ThreeLoops : Function.Surjective n3ThreeLoops :=
  surjective_n3ThreeLoops_of_edge_cover sixEdgeCircleCover

theorem surjective_torusCrosscapThreeLoops :
    Function.Surjective torusCrosscapThreeLoops :=
  surjective_torusCrosscapThreeLoops_of_edge_cover sixEdgeCircleCover

end ConstructionTargets.PolygonSixEdgeCircleCover
