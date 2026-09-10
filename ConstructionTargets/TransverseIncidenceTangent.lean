import ConstructionTargets.TransverseIncidenceChosenAtlas
import ConstructionTargets.ManifoldRegularFiberTangentImage
import ConstructionTargets.TransverseDifferenceKernel
open Set
open scoped ContDiff Manifold
noncomputable section
namespace ConstructionTargets.TransverseIncidenceTangent
open TransverseIncidenceChosenAtlas
variable {A B V M N : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] [CompleteSpace B]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace A M] [IsManifold 𝓘(ℝ,A) ∞ M]
  [TopologicalSpace N] [ChartedSpace B N] [IsManifold 𝓘(ℝ,B) ∞ N]
  (f : M → V) (g : N → V)
  (hf : ContMDiff 𝓘(ℝ,A) 𝓘(ℝ,V) ∞ f)
  (hg : ContMDiff 𝓘(ℝ,B) 𝓘(ℝ,V) ∞ g)
  (ht : ∀ x y, f x = g y →
    LinearMap.range (R := ℝ) (mfderiv 𝓘(ℝ,A) 𝓘(ℝ,V) f x).toLinearMap ⊔
    LinearMap.range (R := ℝ) (mfderiv 𝓘(ℝ,B) 𝓘(ℝ,V) g y).toLinearMap = ⊤)


theorem zero_derivative (x : Zero f g) :
    letI := ChartedSpaceModelTransport.productChartedSpace (E := A) (G := B) (M := M) (N := N)
    letI := zeroAtlas f g hf hg ht
    mfderiv 𝓘(ℝ,Model (A := A) (B := B) (V := V)) (𝓘(ℝ,A).prod 𝓘(ℝ,B))
      (Subtype.val : Zero f g → M × N) x =
    (WithLp.prodContinuousLinearEquiv 2 ℝ A B).toContinuousLinearMap.comp
      (mfderiv 𝓘(ℝ,Model (A := A) (B := B) (V := V)) 𝓘(ℝ,WithLp 2 (A × B))
        (Subtype.val : Zero f g → M × N) x) := by
  letI := ChartedSpaceModelTransport.productChartedSpace (E := A) (G := B) (M := M) (N := N)
  letI := ChartedSpaceModelSmoothTransport.product_isManifold (A := A) (B := B) (X := M) (Y := N)
  letI := zeroAtlas f g hf hg ht
  have hi := (ManifoldRegularFiberGlobalAtlas.smooth_inclusion
    (TransverseDifferenceRegularity.difference f g) 0
    (ChartedSpaceModelDerivativeTransport.difference_smooth f g hf hg)
    (ChartedSpaceModelDerivativeTransport.difference_regular f g hf hg ht)).mdifferentiable (by simp) x
  have hd := (ChartedSpaceModelDerivativeTransport.product_identity_smooth (A := A) (B := B) (X := M) (Y := N)).2.mdifferentiable (by simp) x.val
  have hc := mfderiv_comp x hd hi
  rw [(ChartedSpaceModelDerivativeTransport.product_identity_derivative (A := A) (B := B) (X := M) (Y := N) x.val).2] at hc
  exact hc

theorem inclusion_injective (x : Incidence f g) :
    letI := chosenAtlas f g hf hg ht
    Function.Injective (mfderiv 𝓘(ℝ,Model (A := A) (B := B) (V := V)) (𝓘(ℝ,A).prod 𝓘(ℝ,B))
      (Subtype.val : Incidence f g → M × N) x) := by
  letI := ChartedSpaceModelTransport.productChartedSpace (E := A) (G := B) (M := M) (N := N)
  letI := ChartedSpaceModelSmoothTransport.product_isManifold (A := A) (B := B) (X := M) (Y := N)
  letI := zeroAtlas f g hf hg ht
  rw [chosen_inclusion_derivative f g hf hg ht x, zero_derivative f g hf hg ht]
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ A B).injective.comp
    (ManifoldRegularFiberTangentImage.inclusion_injective
      (TransverseDifferenceRegularity.difference f g) 0
      (ChartedSpaceModelDerivativeTransport.difference_smooth f g hf hg)
      (ChartedSpaceModelDerivativeTransport.difference_regular f g hf hg ht) _)

def inclusionLinear (x : Incidence f g) : Model (A := A) (B := B) (V := V) →L[ℝ] (A × B) :=
  letI := chosenAtlas f g hf hg ht
  mfderiv 𝓘(ℝ,Model (A := A) (B := B) (V := V)) (𝓘(ℝ,A).prod 𝓘(ℝ,B))
    (Subtype.val : Incidence f g → M × N) x

theorem inclusion_range (x : Incidence f g) :
    letI := chosenAtlas f g hf hg ht
    LinearMap.range (inclusionLinear f g hf hg ht x).toLinearMap =
    (mfderiv (𝓘(ℝ,A).prod 𝓘(ℝ,B)) 𝓘(ℝ,V) (TransverseDifferenceRegularity.difference f g) x.val).ker := by
  letI := chosenAtlas f g hf hg ht
  letI := chosen_isManifold f g hf hg ht
  have hi := (chosen_smooth_inclusion f g hf hg ht).mdifferentiable (by simp) x
  have hd := (TransverseDifferenceRegularity.smooth f g hf hg).mdifferentiable (by simp) x.val
  have hc := mfderiv_comp x hd hi
  have he : TransverseDifferenceRegularity.difference f g ∘ (Subtype.val : Incidence f g → M × N) = (fun _ => (0 : V)) := by
    funext y
    exact sub_eq_zero.mpr y.property
  rw [he, mfderiv_const] at hc
  have hle : LinearMap.range (inclusionLinear f g hf hg ht x).toLinearMap ≤
    (mfderiv (𝓘(ℝ,A).prod 𝓘(ℝ,B)) 𝓘(ℝ,V) (TransverseDifferenceRegularity.difference f g) x.val).ker := by
    rintro y ⟨v,rfl⟩
    have hv := congrArg (fun L => L v) hc
    exact hv.symm
  letI : FiniteDimensional ℝ (TangentSpace (𝓘(ℝ,A).prod 𝓘(ℝ,B)) x.val) :=
    inferInstanceAs (FiniteDimensional ℝ (A × B))
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hj : Function.Injective (inclusionLinear f g hf hg ht x) := inclusion_injective f g hf hg ht x
  rw [LinearMap.finrank_range_of_inj hj]
  change Module.finrank ℝ (Model (A := A) (B := B) (V := V)) = _
  rw [model_dimension]
  exact (TransverseDifferenceKernel.kernel_dimension f g hf hg ht x.val x.property).symm

theorem mem_inclusion_range (x : Incidence f g) (v : A × B) :
    letI := chosenAtlas f g hf hg ht
    v ∈ LinearMap.range (inclusionLinear f g hf hg ht x).toLinearMap ↔
    mfderiv 𝓘(ℝ,A) 𝓘(ℝ,V) f x.val.1 v.1 = mfderiv 𝓘(ℝ,B) 𝓘(ℝ,V) g x.val.2 v.2 := by
  rw [inclusion_range f g hf hg ht]
  exact TransverseDifferenceKernel.mem_kernel f g hf hg x.val v

#print axioms zero_derivative
#print axioms inclusionLinear
#print axioms inclusion_injective
#print axioms inclusion_range
#print axioms mem_inclusion_range
end ConstructionTargets.TransverseIncidenceTangent
