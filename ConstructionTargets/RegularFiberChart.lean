import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import ConstructionTargets.SardImplicitFunctionLevelSetKernelParameterization
open Set
noncomputable section
namespace ConstructionTargets.RegularFiberChart
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (f : E → F) (L : E →L[ℝ] F) (x : E)
  (hf : HasStrictFDerivAt f L x) (hs : Function.Surjective L)
abbrev base := (hf.sub_const (f x)).implicitToOpenPartialHomeomorph
  (fun y => f y - f x) L (LinearMap.range_eq_top.mpr hs)

def chart : OpenPartialHomeomorph E (L.ker × F) :=
  (base f L x hf hs).trans (Homeomorph.prodComm F L.ker).toOpenPartialHomeomorph
def kernelProjection : E →L[ℝ] L.ker :=
  Classical.choose L.ker_closedComplemented_of_finiteDimensional_range
omit [CompleteSpace E] in
lemma kernelProjection_retract (z : L.ker) : kernelProjection L z = z :=
  Classical.choose_spec L.ker_closedComplemented_of_finiteDimensional_range z
omit [CompleteSpace E] in
lemma kernel_complement : IsCompl L.ker (kernelProjection L).ker :=
  LinearMap.isCompl_of_proj
    (Classical.choose_spec L.ker_closedComplemented_of_finiteDimensional_range)
lemma chart_fst (y : E) : (chart f L x hf hs y).1 = kernelProjection L (y-x) := rfl
lemma chart_snd (y : E) : (chart f L x hf hs y).2 = f y - f x := rfl
lemma base_center : base f L x hf hs x = (0,0) := by
  simp only [base, HasStrictFDerivAt.implicitToOpenPartialHomeomorph_self, sub_self]
lemma center_mem : x ∈ (base f L x hf hs).source :=
  (hf.sub_const (f x)).mem_implicitToOpenPartialHomeomorph_source
    (LinearMap.range_eq_top.mpr hs)

def kernelOpen : Set L.ker := {z | (0,z) ∈ (base f L x hf hs).target}
lemma kernelOpen_isOpen : IsOpen (kernelOpen f L x hf hs) :=
  (base f L x hf hs).open_target.preimage (continuous_const.prodMk continuous_id)
lemma zero_mem : (0 : L.ker) ∈ kernelOpen f L x hf hs := by
  have h := (base f L x hf hs).map_source (center_mem f L x hf hs)
  rwa [base_center] at h

def param (z : L.ker) : E := (base f L x hf hs).symm (0,z)
lemma param_image : param f L x hf hs '' kernelOpen f L x hf hs =
    (base f L x hf hs).source ∩ {y | f y = f x} := by
  have h := SardImplicitFunctionLevelSetKernelParameterizationProbe.OpenPartialHomeomorph.image_symm_mk_left_eq_inter_source_fst
    (base f L x hf hs) (0 : F)
  change _ = _ ∩ {y | f y - f x = 0} at h
  simpa only [sub_eq_zero] using h
lemma param_derivative : HasStrictFDerivAt (param f L x hf hs) L.ker.subtypeL 0 := by
  have h := (hf.sub_const (f x)).to_implicitFunction (LinearMap.range_eq_top.mpr hs)
  simpa only [sub_self] using h

lemma base_fst (y : E) : (base f L x hf hs y).1 = f y - f x := rfl
lemma base_pair (y : E) (hy : f y = f x) :
    base f L x hf hs y = (0, (base f L x hf hs y).2) := by
  apply Prod.ext
  · rw [base_fst, hy, sub_self]
  · rfl

def fiberHomeomorph :
    {y : E // y ∈ (base f L x hf hs).source ∧ f y = f x} ≃ₜ
      kernelOpen f L x hf hs where
  toFun y := ⟨(base f L x hf hs y).2, by
    have h := (base f L x hf hs).map_source y.property.1
    rwa [base_pair f L x hf hs y y.property.2] at h⟩
  invFun z := ⟨param f L x hf hs z, by
    refine ⟨(base f L x hf hs).map_target z.property, ?_⟩
    have h := congrArg Prod.fst ((base f L x hf hs).right_inv z.property)
    change f (param f L x hf hs z) - f x = 0 at h
    exact sub_eq_zero.mp h⟩
  left_inv y := by
    apply Subtype.ext
    change (base f L x hf hs).symm (0, (base f L x hf hs y).2) = y
    rw [← base_pair f L x hf hs y y.property.2]
    exact (base f L x hf hs).left_inv y.property.1
  right_inv z := by
    apply Subtype.ext
    exact congrArg Prod.snd ((base f L x hf hs).right_inv z.property)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((base f L x hf hs).continuousOn.comp_continuous
      continuous_subtype_val (fun y => y.property.1)).snd
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (base f L x hf hs).symm.continuousOn.comp_continuous
      (continuous_const.prodMk continuous_subtype_val) (fun z => z.property)

lemma fiber_neighborhood_open :
    IsOpen {y : {y : E // f y = f x} | y.val ∈ (base f L x hf hs).source} :=
  (base f L x hf hs).open_source.preimage continuous_subtype_val

lemma param_zero : param f L x hf hs 0 = x := by
  have h := (base f L x hf hs).left_inv (center_mem f L x hf hs)
  rwa [base_center] at h

lemma chart_center_mem : x ∈ (chart f L x hf hs).source := by
  exact ⟨center_mem f L x hf hs, Set.mem_univ _⟩

lemma chart_center : chart f L x hf hs x = (0,0) := by
  change Prod.swap (base f L x hf hs x) = _
  rw [base_center]; rfl


def literalFiberHomeomorph :
    {y : {y : E // f y = f x} // y.val ∈ (base f L x hf hs).source} ≃ₜ
      kernelOpen f L x hf hs :=
  (show {y : {y : E // f y = f x} // y.val ∈ (base f L x hf hs).source} ≃ₜ
      {y : E // y ∈ (base f L x hf hs).source ∧ f y = f x} from
    { toFun := fun y => ⟨y.val.val, y.property, y.val.property⟩
      invFun := fun y => ⟨⟨y.val, y.property.2⟩, y.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }).trans
    (fiberHomeomorph f L x hf hs)

lemma literalFiberHomeomorph_inverse (z : kernelOpen f L x hf hs) :
    ((literalFiberHomeomorph f L x hf hs).symm z).val.val = param f L x hf hs z := rfl

variable {f L x}
omit [CompleteSpace E] [FiniteDimensional ℝ F] in
lemma smooth_derivative (h : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    HasStrictFDerivAt f (fderiv ℝ f x) x := h.hasStrictFDerivAt (by simp)


def smoothFiberHomeomorph (h : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (surj : Function.Surjective (fderiv ℝ f x)) :=
  literalFiberHomeomorph f (fderiv ℝ f x) x (smooth_derivative h) surj

def codimensionTwoMap : ℝ × (ℝ × ℝ) → ℝ × ℝ := Prod.snd
abbrev codimensionTwoDerivative : (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)
lemma codimensionTwoSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) codimensionTwoMap :=
  contDiff_snd
lemma codimensionTwoSurjective : Function.Surjective codimensionTwoDerivative :=
  fun z => ⟨(0,z), rfl⟩
lemma codimensionTwoStrict : HasStrictFDerivAt codimensionTwoMap codimensionTwoDerivative 0 :=
  codimensionTwoDerivative.hasStrictFDerivAt

def codimensionTwoFiberHomeomorph :=
  literalFiberHomeomorph codimensionTwoMap codimensionTwoDerivative 0
    codimensionTwoStrict codimensionTwoSurjective
lemma codimensionTwoInverseDerivative :
    HasStrictFDerivAt
      (param codimensionTwoMap codimensionTwoDerivative 0
        codimensionTwoStrict codimensionTwoSurjective)
      codimensionTwoDerivative.ker.subtypeL 0 :=
  param_derivative codimensionTwoMap codimensionTwoDerivative 0
    codimensionTwoStrict codimensionTwoSurjective
lemma codimensionTwoTargetDimension : Module.finrank ℝ (ℝ × ℝ) = 2 := by
  simp

#print axioms kernelProjection_retract
#print axioms kernel_complement
#print axioms chart_fst
#print axioms chart_snd
#print axioms chart_center_mem
#print axioms chart_center
#print axioms kernelOpen_isOpen
#print axioms zero_mem
#print axioms param_image
#print axioms param_zero
#print axioms param_derivative
#print axioms literalFiberHomeomorph
#print axioms literalFiberHomeomorph_inverse
#print axioms fiber_neighborhood_open
#print axioms smoothFiberHomeomorph
#print axioms codimensionTwoFiberHomeomorph
#print axioms codimensionTwoInverseDerivative
#print axioms codimensionTwoTargetDimension
end ConstructionTargets.RegularFiberChart
