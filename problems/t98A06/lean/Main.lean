import Mathlib
import ConstructionTargets.ManifoldTargetRegularFiberGlobalAtlas

/-! # t98A06: lifting vector fields and diffeomorphic submersion fibers

A smooth vector field is a smooth section of the actual tangent bundle.
A submersion is a smooth map with pointwise surjective manifold derivative.
Part (b) uses the already constructed regular-fiber atlases on the literal
fibers over +1 and -1 in Circle. Thus the conclusion is a Diffeomorph between
those fibers with induced smooth structures, not between arbitrary types.
The usual Hausdorff/second-countable finite-dimensional manifold convention
is explicit. Neither partitions of unity nor flow existence is assumed.
-/

open scoped Manifold ContDiff
noncomputable section
namespace T98A06
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Smoothness of a tangent section uses the tangent-bundle manifold structure. -/
def SmoothVectorField {X : Type} [TopologicalSpace X] {n : ℕ}
    [ChartedSpace (E n) X] [IsManifold (𝓡 n) ∞ X]
    (v : ∀ x : X, TangentSpace (𝓡 n) x) : Prop :=
  ContMDiff (𝓡 n) (𝓡 n).tangent ∞ (fun x => (v x : TangentBundle (𝓡 n) X))

def minusOne : Circle := ⟨-1, mem_sphere_zero_iff_norm.mpr (by norm_num)⟩

abbrev FiberModel (n : ℕ) :=
  ConstructionTargets.ManifoldTargetRegularFiberCharts.Model (E := E n) (F := E 1)

end T98A06
open T98A06 ConstructionTargets.ManifoldTargetRegularFiberGlobalAtlas

theorem apm_t98a06 :
    (∀ (n m : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
      [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]
      [ChartedSpace (E n) X] [ChartedSpace (E m) Y]
      [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]
      (f : X → Y), ContMDiff (𝓡 n) (𝓡 m) ∞ f →
      (∀ x, Function.Surjective (mfderiv (𝓡 n) (𝓡 m) f x)) →
      ∀ v : ∀ y : Y, TangentSpace (𝓡 m) y, SmoothVectorField v →
      ∃ w : ∀ x : X, TangentSpace (𝓡 n) x,
        SmoothVectorField w ∧ ∀ x, mfderiv (𝓡 n) (𝓡 m) f x (w x) = v (f x)) ∧
    (∀ (n : ℕ) (X : Type) [TopologicalSpace X] [T2Space X]
      [SecondCountableTopology X] [CompactSpace X]
      [ChartedSpace (E n) X] [IsManifold (𝓡 n) ∞ X]
      (f : X → Circle) (hsm : ContMDiff (𝓡 n) (𝓡 1) ∞ f)
      (hsub : ∀ x, Function.Surjective (mfderiv (𝓡 n) (𝓡 1) f x)),
      letI := chartedSpace f (1 : Circle) hsm (fun x _ => hsub x)
      letI := chartedSpace f minusOne hsm (fun x _ => hsub x)
      Nonempty (Diffeomorph 𝓘(ℝ, FiberModel n) 𝓘(ℝ, FiberModel n)
        {x : X // f x = (1 : Circle)} {x : X // f x = minusOne} ∞)) := by
  sorry
