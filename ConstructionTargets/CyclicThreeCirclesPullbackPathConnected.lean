import ConstructionTargets.CyclicPullbackNormalizationPath
import ConstructionTargets.CircleHomology

open Set

noncomputable section

namespace ConstructionTargets.CyclicThreeCirclesPullbackPathConnected

open ConstructionTargets.CyclicThreeCirclesCollapse
open ConstructionTargets.CyclicThreeCirclesPullbackCover
open ConstructionTargets.CyclicPullbackNormalizationPath

local instance circlePathConnectedSpace : PathConnectedSpace Circle :=
  pathConnectedSpace_iff_univ.mpr (by
    have h : IsPathConnected
        (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
          (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
        isPathConnected_univ
    simpa using h)

theorem exists_section_path (n : ℕ) (z₀ z₁ : Circle) :
    ∃ γ : Path
      (⟨(firstCircle (z₀ ^ n), z₀), by simp [circlePower]⟩ : Pullback n)
      (⟨(firstCircle (z₁ ^ n), z₁), by simp [circlePower]⟩ : Pullback n),
      ∀ t, (γ t).1.1 = firstCircle ((γ t).1.2 ^ n) := by
  obtain ⟨α⟩ := PathConnectedSpace.joined z₀ z₁
  let γ : Path
      (⟨(firstCircle (z₀ ^ n), z₀), by simp [circlePower]⟩ : Pullback n)
      (⟨(firstCircle (z₁ ^ n), z₁), by simp [circlePower]⟩ : Pullback n) :=
    { toFun := fun t => ⟨(firstCircle ((α t) ^ n), α t), by simp [circlePower]⟩
      continuous_toFun := Continuous.subtype_mk
        ((continuous_firstCircle.comp ((continuous_pow n).comp α.continuous)).prodMk
          α.continuous) (fun _ => by simp [circlePower])
      source' := by
        apply Subtype.ext
        exact Prod.ext (congrArg (fun z => firstCircle (z ^ n)) α.source') α.source'
      target' := by
        apply Subtype.ext
        exact Prod.ext (congrArg (fun z => firstCircle (z ^ n)) α.target') α.target' }
  exact ⟨γ, fun _ => rfl⟩

theorem pullback_joined (n : ℕ) (x y : Pullback n) : Joined x y := by
  obtain ⟨γx, -⟩ := exists_normalization_path n x
  obtain ⟨γy, -⟩ := exists_normalization_path n y
  obtain ⟨σ, -⟩ := exists_section_path n x.1.2 y.1.2
  have hx :
      (⟨(firstCircle (collapse x.1.1), x.1.2), by
        simpa [circlePower] using x.2⟩ : Pullback n) =
      ⟨(firstCircle (x.1.2 ^ n), x.1.2), by simp [circlePower]⟩ := by
    apply Subtype.ext
    exact Prod.ext (congrArg firstCircle x.2) rfl
  have hy :
      (⟨(firstCircle (collapse y.1.1), y.1.2), by
        simpa [circlePower] using y.2⟩ : Pullback n) =
      ⟨(firstCircle (y.1.2 ^ n), y.1.2), by simp [circlePower]⟩ := by
    apply Subtype.ext
    exact Prod.ext (congrArg firstCircle y.2) rfl
  exact ⟨(γx.cast rfl hx.symm).trans (σ.trans (γy.cast rfl hy.symm).symm)⟩

theorem pullback_isPathConnected (n : ℕ) :
    IsPathConnected (Set.univ : Set (Pullback n)) := by
  rw [isPathConnected_iff]
  refine ⟨⟨⟨(firstCircle ((1 : Circle) ^ n), 1), by simp [circlePower]⟩, Set.mem_univ _⟩, ?_⟩
  intro x _ y _
  exact joinedIn_univ.mpr (pullback_joined n x y)

noncomputable instance pullbackPathConnectedSpace (n : ℕ) :
    PathConnectedSpace (Pullback n) :=
  pathConnectedSpace_iff_univ.mpr (pullback_isPathConnected n)

#print axioms pullback_joined
#print axioms pullback_isPathConnected
#print axioms pullbackPathConnectedSpace

end ConstructionTargets.CyclicThreeCirclesPullbackPathConnected
