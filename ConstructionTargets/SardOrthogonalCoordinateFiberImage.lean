import ConstructionTargets.SardTargetOrthogonalCoordinateEquiv

open Set

namespace SardOrthogonalCoordinateFiberImageProbe

/-- Orthogonal projection of a target-image fiber is exactly the residual
coordinate image of the corresponding source fiber. -/
theorem orthogonalProjection_image_fiber_eq
    {Y X : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [FiniteDimensional ℝ Y]
    (R : Submodule ℝ Y) (f : X → Y) (K : Set X) (r : R) :
    Rᗮ.orthogonalProjection '' (f '' K ∩ {y | R.orthogonalProjection y = r}) =
      (fun x => Rᗮ.orthogonalProjection (f x)) ''
        (K ∩ {x | R.orthogonalProjection (f x) = r}) := by
  ext z
  constructor
  · rintro ⟨y, ⟨⟨x, hx, rfl⟩, hr⟩, rfl⟩
    exact ⟨x, ⟨hx, hr⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hr⟩, rfl⟩
    exact ⟨f x, ⟨⟨x, hx, rfl⟩, hr⟩, rfl⟩

#print axioms orthogonalProjection_image_fiber_eq

end SardOrthogonalCoordinateFiberImageProbe
