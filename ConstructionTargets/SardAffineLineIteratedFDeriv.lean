import Mathlib

open ContinuousLinearMap

noncomputable section

def scalarLineMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) : ℝ →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight v

def affineLineRestriction {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (a v : E) : ℝ → F := fun t ↦ f (a + t • v)

/-- Iterated derivatives of a multivariable map restricted to an affine line
are obtained by feeding the line direction into every slot. -/
theorem iteratedFDeriv_affineLineRestriction_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (a v : E) (n i : ℕ) (hf : ContDiff ℝ n f) (hi : i ≤ n) :
    iteratedFDeriv ℝ i (affineLineRestriction f a v) 0 =
      (iteratedFDeriv ℝ i f a).compContinuousLinearMap
        (fun _ ↦ scalarLineMap v) := by
  let g : E → F := fun x ↦ f (a + x)
  let L : ℝ →L[ℝ] E := scalarLineMap v
  have hg : ContDiff ℝ n g := hf.comp (contDiff_const.add contDiff_id)
  have hfun : affineLineRestriction f a v = g ∘ L := by
    funext t
    simp [affineLineRestriction, g, L, scalarLineMap]
  rw [hfun, L.iteratedFDeriv_comp_right hg 0 (mod_cast hi)]
  simp only [g, L, map_zero, add_zero, iteratedFDeriv_comp_add_left]

/-- Vanishing multivariable iterated derivatives transfer to every affine-line
restriction at its base point. -/
theorem iteratedFDeriv_affineLineRestriction_zero_of_eq_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (a v : E) (n i : ℕ) (hf : ContDiff ℝ n f) (hi : i ≤ n)
    (hzero : iteratedFDeriv ℝ i f a = 0) :
    iteratedFDeriv ℝ i (affineLineRestriction f a v) 0 = 0 := by
  rw [iteratedFDeriv_affineLineRestriction_zero f a v n i hf hi, hzero]
  rfl

#print axioms iteratedFDeriv_affineLineRestriction_zero
#print axioms iteratedFDeriv_affineLineRestriction_zero_of_eq_zero
