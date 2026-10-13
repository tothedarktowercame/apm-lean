import Mathlib
import ConstructionTargets.ManifoldTargetRegularFiberGlobalAtlas

/-! # t98A06: lifting vector fields and diffeomorphic submersion fibers -/

open scoped Manifold ContDiff Topology
noncomputable section

namespace T98A06

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def SmoothVectorField {X : Type} [TopologicalSpace X] {n : ℕ}
    [ChartedSpace (E n) X] [IsManifold (𝓡 n) ∞ X]
    (v : ∀ x : X, TangentSpace (𝓡 n) x) : Prop :=
  ContMDiff (𝓡 n) (𝓡 n).tangent ∞ (fun x => (v x : TangentBundle (𝓡 n) X))

def minusOne : Circle := ⟨-1, mem_sphere_zero_iff_norm.mpr (by norm_num)⟩

abbrev FiberModel (n : ℕ) :=
  ConstructionTargets.ManifoldTargetRegularFiberCharts.Model (E := E n) (F := E 1)

/-- A neighborhoodwise smooth lift of `v` through the derivative of `f`.
This is the exact local datum used by partition-of-unity gluing. -/
def HasLocalSmoothLift {n m : ℕ} {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (E n) X] [ChartedSpace (E m) Y]
    [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]
    (f : X → Y) (v : ∀ y : Y, TangentSpace (𝓡 m) y) : Prop :=
  ∀ x₀ : X, ∃ U ∈ 𝓝 x₀, ∃ w : ∀ x : X, TangentSpace (𝓡 n) x,
    ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞
      (fun x => (w x : TangentBundle (𝓡 n) X)) U ∧
    ∀ x ∈ U, mfderiv (𝓡 n) (𝓡 m) f x (w x) = v (f x)

/-- The global conclusion of part (a), named so the two large foundations can
be passed to independent lemma seats without repeating their content. -/
def HasSmoothLift {n m : ℕ} {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (E n) X] [ChartedSpace (E m) Y]
    [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]
    (f : X → Y) (v : ∀ y : Y, TangentSpace (𝓡 m) y) : Prop :=
  ∃ w : ∀ x : X, TangentSpace (𝓡 n) x,
    SmoothVectorField w ∧
      ∀ x, mfderiv (𝓡 n) (𝓡 m) f x (w x) = v (f x)

end T98A06

open T98A06 ConstructionTargets.ManifoldTargetRegularFiberGlobalAtlas

/-- **LIBRARY.** A smooth submersion admits neighborhoodwise smooth lifts of
every smooth target vector field. -/
theorem t98A06_local_smooth_submersion_lift :
    ∀ (n m : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
      [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]
      [ChartedSpace (E n) X] [ChartedSpace (E m) Y]
      [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]
      (f : X → Y), ContMDiff (𝓡 n) (𝓡 m) ∞ f →
      (∀ x, Function.Surjective (mfderiv (𝓡 n) (𝓡 m) f x)) →
      ∀ v : ∀ y : Y, TangentSpace (𝓡 m) y, SmoothVectorField v →
      HasLocalSmoothLift (n := n) (m := m) f v := by
  sorry

/-- Convex partition-of-unity gluing turns neighborhoodwise derivative lifts
into a global smooth vector field.  The local theorem is supplied as a
hypothesis so this lemma is independent of the LIBRARY seat. -/
-- BEGIN SEAT AREA
theorem t98A06_global_vectorField_lift
    (hlocal : ∀ (n m : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
      [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]
      [ChartedSpace (E n) X] [ChartedSpace (E m) Y]
      [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]
      (f : X → Y), ContMDiff (𝓡 n) (𝓡 m) ∞ f →
      (∀ x, Function.Surjective (mfderiv (𝓡 n) (𝓡 m) f x)) →
      ∀ v : ∀ y : Y, TangentSpace (𝓡 m) y, SmoothVectorField v →
      HasLocalSmoothLift (n := n) (m := m) f v) :
    ∀ (n m : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
      [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]
      [ChartedSpace (E n) X] [ChartedSpace (E m) Y]
      [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]
      (f : X → Y), ContMDiff (𝓡 n) (𝓡 m) ∞ f →
      (∀ x, Function.Surjective (mfderiv (𝓡 n) (𝓡 m) f x)) →
      ∀ v : ∀ y : Y, TangentSpace (𝓡 m) y, SmoothVectorField v →
      HasSmoothLift (n := n) (m := m) f v := by
  sorry
-- END SEAT AREA

/-- **LIBRARY.** The complete smooth flow of a lifted angular vector field
restricts at time `π` to a diffeomorphism of the two regular fibers.  The
global lifting theorem is an explicit hypothesis so this can be developed in
parallel with the preceding gluing lemma. -/
theorem t98A06_compact_circle_fibers_diffeomorphic
    (hlift : ∀ (n m : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
      [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]
      [ChartedSpace (E n) X] [ChartedSpace (E m) Y]
      [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]
      (f : X → Y), ContMDiff (𝓡 n) (𝓡 m) ∞ f →
      (∀ x, Function.Surjective (mfderiv (𝓡 n) (𝓡 m) f x)) →
      ∀ v : ∀ y : Y, TangentSpace (𝓡 m) y, SmoothVectorField v →
      HasSmoothLift (n := n) (m := m) f v) :
    ∀ (n : ℕ) (X : Type) [TopologicalSpace X] [T2Space X]
      [SecondCountableTopology X] [CompactSpace X]
      [ChartedSpace (E n) X] [IsManifold (𝓡 n) ∞ X]
      (f : X → Circle) (hsm : ContMDiff (𝓡 n) (𝓡 1) ∞ f)
      (hsub : ∀ x, Function.Surjective (mfderiv (𝓡 n) (𝓡 1) f x)),
      letI := chartedSpace f (1 : Circle) hsm (fun x _ => hsub x)
      letI := chartedSpace f minusOne hsm (fun x _ => hsub x)
      Nonempty (Diffeomorph 𝓘(ℝ, FiberModel n) 𝓘(ℝ, FiberModel n)
        {x : X // f x = (1 : Circle)} {x : X // f x = minusOne} ∞) := by
  sorry

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
  have hlift := t98A06_global_vectorField_lift t98A06_local_smooth_submersion_lift
  exact ⟨hlift, t98A06_compact_circle_fibers_diffeomorphic hlift⟩

#print axioms apm_t98a06
