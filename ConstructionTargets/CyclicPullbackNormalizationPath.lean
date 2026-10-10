import ConstructionTargets.ThreeCirclesCollapseFiberPath
import ConstructionTargets.CyclicThreeCirclesPullbackCover

open ConstructionTargets.StatementSurfaceModels

noncomputable section

namespace ConstructionTargets.CyclicPullbackNormalizationPath

open ConstructionTargets.CyclicThreeCirclesCollapse
open ConstructionTargets.CyclicThreeCirclesPullbackCover
open ConstructionTargets.ThreeCirclesCollapseFiberPath

/-- A pullback point can be normalized into the final-circle section while
its circle coordinate remains fixed. -/
theorem exists_normalization_path (n : ℕ) (x : Pullback n) :
    ∃ γ : Path x
      ⟨(firstCircle (collapse x.1.1), x.1.2), by
        simpa [circlePower] using x.2⟩,
      ∀ t, (γ t).1.2 = x.1.2 := by
  obtain ⟨δ, hδ⟩ := exists_collapseFiber_path x.1.1
  let γ : Path x
      ⟨(firstCircle (collapse x.1.1), x.1.2), by
        simpa [circlePower] using x.2⟩ :=
    { toFun := fun t =>
        ⟨(δ t, x.1.2), by
          change collapse (δ t) = circlePower n x.1.2
          rw [hδ]
          exact x.2⟩
      continuous_toFun := Continuous.subtype_mk
        (δ.continuous.prodMk continuous_const) (fun t => by
          change collapse (δ t) = circlePower n x.1.2
          rw [hδ]
          exact x.2)
      source' := by
        apply Subtype.ext
        exact Prod.ext δ.source' rfl
      target' := by
        apply Subtype.ext
        exact Prod.ext δ.target' rfl }
  exact ⟨γ, fun _ => rfl⟩

#print axioms exists_normalization_path

end ConstructionTargets.CyclicPullbackNormalizationPath
