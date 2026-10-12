import ConstructionTargets.SardGenuineSmoothManifoldVector
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped ContDiff Manifold
open Set

noncomputable section

namespace ConstructionTargets.SardGeneralModel

abbrev SupPlane := Fin 2 → ℝ

abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

noncomputable def targetEquiv : SupPlane ≃L[ℝ] EuclideanPlane :=
  (LinearEquiv.ofFinrankEq SupPlane EuclideanPlane (by simp)).toContinuousLinearEquiv

theorem linearTargetTransport
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] SupPlane) :
    Function.Surjective (targetEquiv.toContinuousLinearMap.comp D) ↔
      Function.Surjective D := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (targetEquiv y)
    refine ⟨x, targetEquiv.injective ?_⟩
    simpa using hx
  · intro h
    exact targetEquiv.surjective.comp h

theorem modelRange_geometry
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) :
    Convex ℝ (Set.range I) ∧
      IsClosed (Set.range I) ∧
      (interior (Set.range I)).Nonempty ∧
      Set.range I = closure (interior (Set.range I)) := by
  exact ⟨I.convex_range, I.isClosed_range, I.nonempty_interior,
    I.range_eq_closure_interior⟩

end ConstructionTargets.SardGeneralModel

#print axioms ConstructionTargets.SardGeneralModel.linearTargetTransport
