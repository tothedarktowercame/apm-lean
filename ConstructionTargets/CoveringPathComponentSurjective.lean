import ConstructionTargets.CoveringPathComponentDomain
import Mathlib.Topology.Homotopy.Lifting

open Function unitInterval

noncomputable section

namespace ConstructionTargets.CoveringPathComponentSurjective

open ConstructionTargets.CoveringPathComponentDomain

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- The restriction of a covering projection to the path component of any
chosen point is onto a path-connected base. -/
theorem componentProjection_surjective [PathConnectedSpace B]
    {p : E → B} (hp : IsCoveringMap p) (e : E) :
    Surjective (fun x : Component e => p x.1) := by
  intro b
  obtain ⟨γ⟩ := PathConnectedSpace.joined (p e) b
  let Γ := hp.liftPath γ e (by simp)
  have hΓ0 : Γ 0 = e := hp.liftPath_zero γ e (by simp)
  have hΓpath : Joined e (Γ 1) := by
    exact ⟨⟨Γ, hΓ0, rfl⟩⟩
  refine ⟨⟨Γ 1, hΓpath⟩, ?_⟩
  exact (congr_fun (hp.liftPath_lifts γ e (by simp)) 1).trans γ.target

#print axioms componentProjection_surjective

end ConstructionTargets.CoveringPathComponentSurjective
