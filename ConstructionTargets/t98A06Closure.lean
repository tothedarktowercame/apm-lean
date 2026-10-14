import Mathlib
import ConstructionTargets.ManifoldTargetRegularFiberGlobalAtlas

open scoped Manifold ContDiff Topology
noncomputable section

namespace ConstructionTargets.T98A06Closure

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def SmoothVectorField {X : Type} [TopologicalSpace X] {n : ℕ}
    [ChartedSpace (E n) X] [IsManifold (𝓡 n) ∞ X]
    (v : ∀ x : X, TangentSpace (𝓡 n) x) : Prop :=
  ContMDiff (𝓡 n) (𝓡 n).tangent ∞ (fun x => (v x : TangentBundle (𝓡 n) X))

def HasLocalSmoothLift {n m : ℕ} {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (E n) X] [ChartedSpace (E m) Y]
    [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]
    (f : X → Y) (v : ∀ y : Y, TangentSpace (𝓡 m) y) : Prop :=
  ∀ x₀ : X, ∃ U ∈ 𝓝 x₀, ∃ w : ∀ x : X, TangentSpace (𝓡 n) x,
    ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞
      (fun x => (w x : TangentBundle (𝓡 n) X)) U ∧
    ∀ x ∈ U, mfderiv (𝓡 n) (𝓡 m) f x (w x) = v (f x)

def HasSmoothLift {n m : ℕ} {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (E n) X] [ChartedSpace (E m) Y]
    [IsManifold (𝓡 n) ∞ X] [IsManifold (𝓡 m) ∞ Y]
    (f : X → Y) (v : ∀ y : Y, TangentSpace (𝓡 m) y) : Prop :=
  ∃ w : ∀ x : X, TangentSpace (𝓡 n) x,
    SmoothVectorField w ∧ ∀ x, mfderiv (𝓡 n) (𝓡 m) f x (w x) = v (f x)

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
  intro n m X Y _ _ _ _ _ _ _ _ _ _ f hf hsurj v hv
  let t : ∀ x : X, Set (TangentSpace (modelWithCornersSelf ℝ (E n)) x) :=
    fun x ↦ {u | mfderiv (modelWithCornersSelf ℝ (E n))
      (modelWithCornersSelf ℝ (E m)) f x u = v (f x)}
  have ht : ∀ x, Convex ℝ (t x) := by
    intro x
    exact (convex_singleton (v (f x)) : Convex ℝ {v (f x)}).linear_preimage
      (mfderiv (modelWithCornersSelf ℝ (E n))
        (modelWithCornersSelf ℝ (E m)) f x).toLinearMap
  have hloc : ∀ x₀ : X, ∃ U ∈ nhds x₀,
      ∃ w : ∀ x : X, TangentSpace (modelWithCornersSelf ℝ (E n)) x,
        ContMDiffOn (modelWithCornersSelf ℝ (E n))
          (modelWithCornersSelf ℝ (E n)).tangent ∞
          (fun x ↦ (w x : TangentBundle (modelWithCornersSelf ℝ (E n)) X)) U ∧
        ∀ x ∈ U, w x ∈ t x := by
    simpa [t] using hlocal n m X Y f hf hsurj v hv
  letI : LocallyCompactSpace X :=
    Manifold.locallyCompact_of_finiteDimensional (modelWithCornersSelf ℝ (E n))
  letI : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨w, hw⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local (modelWithCornersSelf ℝ (E n))
      (fun x : X ↦ TangentSpace (modelWithCornersSelf ℝ (E n)) x) t ht hloc
  refine ⟨fun x ↦ w x, w.contMDiff, ?_⟩
  intro x
  exact hw x

#print axioms t98A06_global_vectorField_lift

end ConstructionTargets.T98A06Closure
