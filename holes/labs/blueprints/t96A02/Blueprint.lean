import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.RationalLefschetz

/-! # t96A02: fixed points on the wedge of two real projective planes -/

open ConstructionTargets.StatementSurfaceModels
open ConstructionTargets.RationalLefschetz

noncomputable section

/-- **LIBRARY.** Every self-map of the wedge of two projective planes has
rational Lefschetz number one. -/
theorem t96A02_wedge_lefschetz_number :
    ∀ f : C(ProjectivePlaneWedge, ProjectivePlaneWedge),
      HasLefschetzNumber f 1 := by
  sorry

/-- **LIBRARY.** The Lefschetz fixed-point implication, specialized to the
wedge of two projective planes. Its homology calculation is supplied as a
hypothesis so this foundation can be developed in parallel with it. -/
theorem t96A02_wedge_fixed_point_of_lefschetz
    (hL : ∀ f : C(ProjectivePlaneWedge, ProjectivePlaneWedge),
      HasLefschetzNumber f 1) :
    ∀ f : C(ProjectivePlaneWedge, ProjectivePlaneWedge), ∃ x, f x = x := by
  sorry

theorem apm_t96a02 :
    ∀ f : ContinuousMap ProjectivePlaneWedge ProjectivePlaneWedge, ∃ x, f x = x := by
  exact t96A02_wedge_fixed_point_of_lefschetz
    t96A02_wedge_lefschetz_number

#print axioms apm_t96a02
