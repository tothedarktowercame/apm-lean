import ConstructionTargets.SmoothRegularFiberCoordinates
import Mathlib.Analysis.InnerProductSpace.PiL2
open Set
open scoped ContDiff Topology
noncomputable section
namespace ConstructionTargets.RegularFiberFixedModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (L : E →L[ℝ] F) (hs : Function.Surjective L)
abbrev Model := EuclideanSpace ℝ (Fin (Module.finrank ℝ E - Module.finrank ℝ F))
include hs in
omit [CompleteSpace E] [FiniteDimensional ℝ F] in
lemma kernel_dimension : Module.finrank ℝ L.ker = Module.finrank ℝ E - Module.finrank ℝ F := by
  have h := L.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs] at h
  simp only [finrank_top] at h
  omega

def kernelEquiv : L.ker ≃L[ℝ] Model (E := E) (F := F) :=
  ContinuousLinearEquiv.ofFinrankEq (by simpa using kernel_dimension L hs)

def tangentInclusion : Model (E := E) (F := F) →L[ℝ] E :=
  L.ker.subtypeL.comp (kernelEquiv L hs).symm.toContinuousLinearMap

omit [CompleteSpace E] [FiniteDimensional ℝ F] in
lemma tangent_range : LinearMap.range (tangentInclusion L hs).toLinearMap = L.ker := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩; exact ((kernelEquiv L hs).symm z).property
  · intro hy
    refine ⟨kernelEquiv L hs ⟨y,hy⟩, ?_⟩
    simp [tangentInclusion]

variable (f : E → F) (x : E) (hf : HasStrictFDerivAt f L x) (hsm : ContDiff ℝ ∞ f)
include hf hsm in
theorem exists_parameterization :
    ∃ (U : Set E) (V : Set (Model (E := E) (F := F))) (g : Model (E := E) (F := F) → E),
      IsOpen U ∧ x ∈ U ∧ IsOpen V ∧ 0 ∈ V ∧ g 0 = x ∧
      ContDiffOn ℝ ∞ g V ∧ Set.InjOn g V ∧ g '' V = U ∩ {y | f y = f x} ∧
      HasStrictFDerivAt g (tangentInclusion L hs) 0 := by
  obtain ⟨e, hx, he0, hfst, _, _, hopen, hz, himage, hsmg, hder⟩ :=
    SmoothRegularFiberCoordinates.exists_smooth_fiber_slice f L x hf hs hsm
  let A := kernelEquiv L hs
  let V : Set (Model (E := E) (F := F)) := {z | (0, A.symm z) ∈ e.target}
  let g : Model (E := E) (F := F) → E := fun z => e.symm (0,A.symm z)
  refine ⟨e.source, V, g, e.open_source, hx, hopen.preimage A.symm.continuous, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [V] using hz
  · change e.symm (0,A.symm 0) = x
    rw [map_zero, ← he0]; exact e.left_inv hx
  · exact hsmg.comp A.symm.contDiff.contDiffOn (fun _ h => h)
  · intro a ha b hb hab
    exact A.symm.injective (congrArg Prod.snd (e.symm.injOn ha hb hab))
  · rw [← himage]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨A.symm z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨A z, ?_, ?_⟩
      · simpa [V] using hz
      · simp [g]
  · have hder' : HasStrictFDerivAt (fun z => e.symm (0,z)) L.ker.subtypeL (A.symm 0) := by
      simpa only [map_zero] using hder
    exact hder'.comp 0 A.symm.hasStrictFDerivAt
#print axioms kernel_dimension
#print axioms tangent_range
#print axioms exists_parameterization
end ConstructionTargets.RegularFiberFixedModel
