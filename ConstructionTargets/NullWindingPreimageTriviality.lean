import ConstructionTargets.EmbeddedCirclePreimage
import ConstructionTargets.SingularHomologyHomotopy

open CategoryTheory Set
noncomputable section
namespace ConstructionTargets.NullWindingPreimageTriviality

abbrev integralH1 : TopCat ⥤ ModuleCat ℤ :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ)

/-- The actual induced integral H1 map of a constant circle map vanishes. -/
theorem constant_map_zero (z : Circle) :
    integralH1.map (TopCat.ofHom (ContinuousMap.const Circle z)) = 0 := by
  exact SingularHomologyHomotopy.singularHomology_map_const_eq_zero
    (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) 1 one_ne_zero z

/-- Constant loops satisfy every clause of the literal null-winding predicate.
This proves no component parametrization or manifold duality theorem. -/
theorem always {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (f : C(X,S)) (c : C(Circle,S)) :
    EmbeddedCirclePreimage.HasNullWindingPreimage integralH1 f c := by
  intro x hx
  obtain ⟨z, hz⟩ := hx
  refine ⟨ContinuousMap.const Circle x, ContinuousMap.const Circle z,
    ⟨z, rfl⟩, ?_, ?_, constant_map_zero z⟩
  · rintro y ⟨w, rfl⟩
    exact ⟨z, hz⟩
  · ext w
    exact hz

/-- Exact logical equivalence with True, for the existing predicate only. -/
theorem iff_true {X S : Type} [TopologicalSpace X] [TopologicalSpace S]
    (f : C(X,S)) (c : C(Circle,S)) :
    EmbeddedCirclePreimage.HasNullWindingPreimage integralH1 f c ↔ True :=
  ⟨fun _ => trivial, fun _ => always f c⟩

#print axioms constant_map_zero
#print axioms always
#print axioms iff_true
end ConstructionTargets.NullWindingPreimageTriviality
