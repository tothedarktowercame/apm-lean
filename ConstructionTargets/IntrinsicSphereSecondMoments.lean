import ConstructionTargets.IntrinsicSphereFinite
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace ConstructionTargets.IntrinsicSphereSecondMoments
open IntrinsicSphereFinite

def sphereIsometry (d : ℕ) (e : Ambient d ≃ₗᵢ[ℝ] Ambient d) : Sphere d ≃ᵢ Sphere d where
  toFun x := ⟨e x.val, by simpa only [Metric.mem_sphere, dist_zero_right, e.norm_map] using x.property⟩
  invFun x := ⟨e.symm x.val, by simpa only [Metric.mem_sphere, dist_zero_right, e.symm.norm_map] using x.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact e.apply_symm_apply x.val
  isometry_toFun x y := e.isometry x.val y.val

theorem integral_isometry (d : ℕ) (e : Ambient d ≃ₗᵢ[ℝ] Ambient d) (f : Sphere d → ℝ) :
    (∫ x, f (sphereIsometry d e x) ∂Measure.hausdorffMeasure d) =
    ∫ x, f x ∂Measure.hausdorffMeasure d := by
  let em := (sphereIsometry d e).toHomeomorph.toMeasurableEquiv
  have h : MeasurePreserving em (Measure.hausdorffMeasure d) (Measure.hausdorffMeasure d) :=
    (sphereIsometry d e).measurePreserving_hausdorffMeasure d
  exact h.integral_comp' f

def reflection (d : ℕ) (i : Fin (d+1)) : Ambient d ≃ₗᵢ[ℝ] Ambient d :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun j =>
    if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
lemma reflection_apply (d : ℕ) (i j : Fin (d+1)) (x : Ambient d) :
    reflection d i x j = if j = i then -x j else x j := by
  simp only [reflection, LinearIsometryEquiv.piLpCongrRight_apply]
  split_ifs <;> simp_all

theorem odd_integral (d : ℕ) (i : Fin (d+1)) (f : Sphere d → ℝ)
    (hf : ∀ x, f (sphereIsometry d (reflection d i) x) = -f x) :
    (∫ x, f x ∂Measure.hausdorffMeasure d) = 0 := by
  have h := integral_isometry d (reflection d i) f
  simp only [hf, integral_neg] at h
  linarith

def permutation (d : ℕ) (p : Equiv.Perm (Fin (d+1))) : Ambient d ≃ₗᵢ[ℝ] Ambient d :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p
lemma permutation_apply (d : ℕ) (p : Equiv.Perm (Fin (d+1))) (x : Ambient d) (i : Fin (d+1)) :
    permutation d p x i = x (p.symm i) := by rfl

theorem square_eq (d : ℕ) (i j : Fin (d+1)) :
    (∫ x : Sphere d, x.val i^2 ∂Measure.hausdorffMeasure d) =
    ∫ x : Sphere d, x.val j^2 ∂Measure.hausdorffMeasure d := by
  have h := integral_isometry d (permutation d (Equiv.swap i j)) (fun x => x.val j^2)
  simpa [sphereIsometry, permutation_apply] using h

def mass (d : ℕ) : ℝ := (Measure.hausdorffMeasure d (Set.univ : Set (Sphere d))).toReal

theorem square_moment (d : ℕ) (hd : d ≤ 3) (i : Fin (d+1)) :
    (∫ x : Sphere d, x.val i^2 ∂Measure.hausdorffMeasure d) = mass d / (d+1) := by
  have hi (j : Fin (d+1)) : Integrable (fun x : Sphere d => x.val j^2)
      (Measure.hausdorffMeasure d) := continuous_integrable d hd _ (by fun_prop)
  have hx (x : Sphere d) : ∑ j : Fin (d+1), x.val j^2 = 1 := by
    have hn : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin (d+1) => ℝ) x.val
    rw [hn] at h
    simpa only [Real.norm_eq_abs, sq_abs, one_pow] using h.symm
  have hsum := integral_finset_sum Finset.univ (fun j _ => hi j)
  have hm : (∫ x : Sphere d, (1:ℝ) ∂Measure.hausdorffMeasure d) = mass d := by
    simp [mass, measureReal_def]
  have h : (d+1:ℝ) * (∫ x : Sphere d, x.val i^2 ∂Measure.hausdorffMeasure d) = mass d := by
    calc
      _ = ∑ j : Fin (d+1), ∫ x : Sphere d, x.val j^2 ∂Measure.hausdorffMeasure d := by
        simp_rw [square_eq d _ i]
        simp
      _ = ∫ x : Sphere d, ∑ j : Fin (d+1), x.val j^2 ∂Measure.hausdorffMeasure d := hsum.symm
      _ = mass d := by simp_rw [hx]; exact hm
  apply (eq_div_iff (by positivity : (d+1:ℝ) ≠ 0)).2
  nlinarith [h]

theorem mixed_moment_zero :
    (∫ x : Sphere 3, x.val 1^3*x.val 0 ∂Measure.hausdorffMeasure 3) = 0 := by
  apply odd_integral 3 0
  intro x
  change (reflection 3 0 x.val 1)^3 * reflection 3 0 x.val 0 = -(x.val 1^3*x.val 0)
  simp [reflection_apply]

theorem projective_density_moment :
    (∫ x : Sphere 3, x.val 1^3*x.val 0 - 4*x.val 0^2 ∂Measure.hausdorffMeasure 3) = -mass 3 := by
  have h : (∫ x : Sphere 3, x.val 0^2 ∂Measure.hausdorffMeasure 3) = mass 3 / 4 := by
    have h := square_moment 3 (by decide) 0
    norm_num at h
    exact h
  rw [projective_density_split, mixed_moment_zero, h]
  ring

#print axioms sphereIsometry
#print axioms integral_isometry
#print axioms odd_integral
#print axioms square_eq
#print axioms square_moment
#print axioms mixed_moment_zero
#print axioms projective_density_moment
end ConstructionTargets.IntrinsicSphereSecondMoments
