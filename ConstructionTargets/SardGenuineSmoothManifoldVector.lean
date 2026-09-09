import ConstructionTargets.SardGenuineSmoothEuclidean
open Set MeasureTheory
open scoped ContDiff Manifold
noncomputable section
namespace T93A04ManifoldWork
variable {E F M : Type*}
 [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
 [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
 [MeasurableSpace F] [BorelSpace F]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
 [SecondCountableTopology M]
theorem null_critical (μ : Measure F) [μ.IsAddHaarMeasure] (f : M → F)
 (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) :
 μ (f '' {y | ¬ Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f y)}) = 0 := by
 apply SardFiniteOrderRankLocusLocalAggregationProbe.measure_image_zero_of_rankLocus_pointwise_open
 intro x hx
 let e := chartAt E x
 have he : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm e.target := contMDiffOn_chart_symm
 have hq : ContDiffOn ℝ ∞ (f ∘ e.symm) e.target :=
   (hf.comp_contMDiffOn he).contDiffOn
 have hn := SardGenuineSmoothEuclideanProbe.open_domain_critical_image_null
   μ (f ∘ e.symm) e.target e.target e.open_target (Subset.refl _) hq
 refine ⟨e.source,e.open_source,mem_chart_source E x,measure_mono_null ?_ hn⟩
 rintro v ⟨y,⟨hy,hys⟩,rfl⟩
 refine ⟨e y,⟨e.map_source hys,?_⟩,?_⟩
 · intro hs
   have hd := mfderiv_comp (e y) (hf.mdifferentiable (by simp) (e.symm (e y)))
     ((he.contMDiffAt (e.open_target.mem_nhds (e.map_source hys))).mdifferentiableAt (by simp))
   rw [mfderiv_eq_fderiv] at hd
   rw [hd] at hs
   apply hy
   rw [e.left_inv hys] at hs
   exact Function.Surjective.of_comp hs
 · exact congrArg f (e.left_inv hys)

end T93A04ManifoldWork
#print axioms T93A04ManifoldWork.null_critical
