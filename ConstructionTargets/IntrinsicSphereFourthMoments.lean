import ConstructionTargets.IntrinsicSphereSecondMoments
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace ConstructionTargets.IntrinsicSphereFourthMoments
open IntrinsicSphereFinite IntrinsicSphereSecondMoments
abbrev E := Ambient 2
abbrev S := Sphere 2

def rotate (x : E) : E := WithLp.toLp 2 ![(x 0+x 1)/Real.sqrt 2, (x 1-x 0)/Real.sqrt 2, x 2]
def unrotate (x : E) : E := WithLp.toLp 2 ![(x 0-x 1)/Real.sqrt 2, (x 1+x 0)/Real.sqrt 2, x 2]
lemma sqrt_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
lemma sqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
lemma rotate_inverse (x : E) : rotate (unrotate x) = x := by
  ext i
  fin_cases i <;> simp [rotate, unrotate] <;> field_simp <;> rw [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)] <;> ring
lemma inverse_rotate (x : E) : unrotate (rotate x) = x := by
  ext i
  fin_cases i <;> simp [rotate, unrotate] <;> field_simp <;> rw [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)] <;> ring
def rotateLinear : E →ₗ[ℝ] E where
  toFun := rotate
  map_add' x y := by ext i; fin_cases i <;> simp [rotate] <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp [rotate] <;> ring
lemma norm_sq (x : E) : ‖x‖^2 = x 0^2+x 1^2+x 2^2 := by
  simpa [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc] using
    PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x
lemma rotate_norm (x : E) : ‖rotate x‖ = ‖x‖ := by
  have h : ‖rotate x‖^2 = ‖x‖^2 := by
    rw [norm_sq, norm_sq]
    simp [rotate, div_pow, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    ring
  nlinarith [norm_nonneg (rotate x), norm_nonneg x]
def rotation : E ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofSurjective
    { rotateLinear with norm_map' := rotate_norm } (fun x => ⟨unrotate x, rotate_inverse x⟩)
lemma rotation_apply (x : E) : rotation x = rotate x := rfl

theorem quartic_rotation_identity :
    (∫ x : S, (x.val 0+x.val 1)^4 ∂Measure.hausdorffMeasure 2) =
      4*(∫ x : S, x.val 0^4 ∂Measure.hausdorffMeasure 2) := by
  have h := integral_isometry 2 rotation (fun x => x.val 0^4)
  have he (x : S) : (sphereIsometry 2 rotation x).val 0^4 =
      (x.val 0+x.val 1)^4 / 4 := by
    change ((x.val 0+x.val 1)/Real.sqrt 2)^4 = _
    rw [div_pow]
    have hs : Real.sqrt 2 ^4 = 4 := by nlinarith [sqrt_sq]
    rw [hs]
  simp_rw [he] at h
  rw [integral_div] at h
  norm_num at h
  linarith

lemma fourth_eq (i j : Fin 3) :
    (∫ x : S, x.val i^4 ∂Measure.hausdorffMeasure 2) =
    ∫ x : S, x.val j^4 ∂Measure.hausdorffMeasure 2 := by
  have h := integral_isometry 2 (permutation 2 (Equiv.swap i j)) (fun x => x.val j^4)
  simpa [sphereIsometry, permutation_apply] using h
lemma odd31 : (∫ x : S, x.val 0^3*x.val 1 ∂Measure.hausdorffMeasure 2) = 0 := by
  apply odd_integral 2 1
  intro x
  change (reflection 2 1 x.val 0)^3 * reflection 2 1 x.val 1 = _
  simp [reflection_apply]
lemma odd13 : (∫ x : S, x.val 0*x.val 1^3 ∂Measure.hausdorffMeasure 2) = 0 := by
  apply odd_integral 2 0
  intro x
  change reflection 2 0 x.val 0 * (reflection 2 0 x.val 1)^3 = _
  simp [reflection_apply]
theorem fourth_eq_three_mixed :
    (∫ x : S, x.val 0^4 ∂Measure.hausdorffMeasure 2) =
      3*(∫ x : S, x.val 0^2*x.val 1^2 ∂Measure.hausdorffMeasure 2) := by
  have h := quartic_rotation_identity
  have he (x : S) : (x.val 0+x.val 1)^4 =
      x.val 0^4 + 4*(x.val 0^3*x.val 1) + 6*(x.val 0^2*x.val 1^2) +
        4*(x.val 0*x.val 1^3) + x.val 1^4 := by ring
  simp_rw [he] at h
  rw [integral_add, integral_add, integral_add, integral_add] at h <;>
    try (apply continuous_integrable 2 (by decide); fun_prop)
  simp only [integral_const_mul] at h
  rw [odd31, odd13, ← fourth_eq 0 1] at h
  linarith


lemma mixed02 : (∫ x : S, x.val 0^2*x.val 2^2 ∂Measure.hausdorffMeasure 2) =
    ∫ x : S, x.val 0^2*x.val 1^2 ∂Measure.hausdorffMeasure 2 := by
  have h := integral_isometry 2 (permutation 2 (Equiv.swap 1 2)) (fun x => x.val 0^2*x.val 1^2)
  simpa [sphereIsometry, permutation_apply, Equiv.swap_apply_def] using h
lemma norm_identity (x : S) : x.val 0^2+x.val 1^2+x.val 2^2 = 1 := by
  have hn : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  rw [← norm_sq, hn]; norm_num

theorem fourth_moment (i : Fin 3) :
    (∫ x : S, x.val i^4 ∂Measure.hausdorffMeasure 2) = mass 2 / 5 := by
  have h2 : (∫ x : S, x.val 0^2 ∂Measure.hausdorffMeasure 2) = mass 2 / 3 := by
    have h := square_moment 2 (by decide) 0
    norm_num at h
    exact h
  have he (x : S) : x.val 0^2 = x.val 0^4 + x.val 0^2*x.val 1^2 + x.val 0^2*x.val 2^2 := by
    nlinarith [congrArg (fun a : ℝ => x.val 0^2*a) (norm_identity x)]
  have h : (∫ x : S, x.val 0^4 + x.val 0^2*x.val 1^2 + x.val 0^2*x.val 2^2
      ∂Measure.hausdorffMeasure 2) = mass 2/3 :=
    (integral_congr_ae (Filter.Eventually.of_forall he)).symm.trans h2
  rw [integral_add, integral_add] at h <;> try (apply continuous_integrable 2 (by decide); fun_prop)
  rw [mixed02] at h
  rw [fourth_eq i 0]
  linarith [fourth_eq_three_mixed]

theorem mixed_fourth_moment :
    (∫ x : S, x.val 0^2*x.val 1^2 ∂Measure.hausdorffMeasure 2) = mass 2 / 15 := by
  have h := fourth_eq_three_mixed
  rw [fourth_moment 0] at h
  linarith

lemma odd_power (i : Fin 3) (n : ℕ) :
    (∫ x : S, x.val i^(2*n+1) ∂Measure.hausdorffMeasure 2) = 0 := by
  apply odd_integral 2 i
  intro x
  change (reflection 2 i x.val i)^(2*n+1) = _
  simp [reflection_apply, pow_add, pow_mul]

theorem shifted_cube (i : Fin 3) (a : ℝ) :
    (∫ x : S, x.val i*(x.val i+a)^3 ∂Measure.hausdorffMeasure 2) = mass 2/5 + mass 2*a^2 := by
  have he (x : S) : x.val i*(x.val i+a)^3 =
      x.val i^4 + (3*a)*x.val i^3 + (3*a^2)*x.val i^2 + a^3*x.val i := by ring
  simp_rw [he]
  rw [integral_add, integral_add, integral_add] <;> try (apply continuous_integrable 2 (by decide); fun_prop)
  simp only [integral_const_mul]
  have h1 : (∫ x : S, x.val i ∂Measure.hausdorffMeasure 2) = 0 := by simpa using odd_power i 0
  have h3 : (∫ x : S, x.val i^3 ∂Measure.hausdorffMeasure 2) = 0 := by simpa using odd_power i 1
  have h2 : (∫ x : S, x.val i^2 ∂Measure.hausdorffMeasure 2) = mass 2/3 := by
    have h := square_moment 2 (by decide) i
    norm_num at h
    exact h
  rw [h1,h3,h2,fourth_moment]
  ring

theorem shifted_linear (i : Fin 3) (a : ℝ) :
    (∫ x : S, x.val i*(x.val i+a) ∂Measure.hausdorffMeasure 2) = mass 2/3 := by
  have he (x : S) : x.val i*(x.val i+a) = x.val i^2 + a*x.val i := by ring
  simp_rw [he]
  rw [integral_add] <;> try (apply continuous_integrable 2 (by decide); fun_prop)
  rw [integral_const_mul]
  have h1 : (∫ x : S, x.val i ∂Measure.hausdorffMeasure 2) = 0 := by simpa using odd_power i 0
  rw [h1, mul_zero, add_zero]
  have h := square_moment 2 (by decide) i
  norm_num at h
  exact h

theorem unitFlux_moment (c : E) :
    (∫ x : S, x.val 0*(x.val 0+c 0-1)^3 + x.val 1*(x.val 1+c 1-2)^3 +
      x.val 2*(x.val 2+c 2-3) ∂Measure.hausdorffMeasure 2) =
    mass 2*(11/15+(c 0-1)^2+(c 1-2)^2) := by
  rw [unitFlux_split]
  simp_rw [show ∀ a b k : ℝ, a+b-k = a+(b-k) by intros; ring]
  rw [shifted_cube, shifted_cube, shifted_linear]
  ring
#print axioms fourth_moment
#print axioms mixed_fourth_moment
#print axioms unitFlux_moment
#print axioms fourth_eq_three_mixed
#print axioms rotation
#print axioms rotation_apply
#print axioms rotate_inverse
#print axioms inverse_rotate
#print axioms quartic_rotation_identity
end ConstructionTargets.IntrinsicSphereFourthMoments
