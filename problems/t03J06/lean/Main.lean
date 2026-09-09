import ConstructionTargets.T03J06FinalAdapter
import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# APM t03J06 — a two-form and its bullet-surface integral

## Statement repairs

The hemisphere equation contains `(z - 1)^1`; this is corrected to
`(z - 1)^2`. Exponent `2` is forced by “hemisphere,” the stated center and
radius, and the top point `(0,0,2)`.

The surface integral is defined concretely as the sum of pullback integrals
under outward-oriented parametrizations of the cylinder and upper hemisphere.
-/

open MeasureTheory Set
open scoped Interval

noncomputable section

abbrev apm_t03J06_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t03J06_Form1 :=
  apm_t03J06_E3 → apm_t03J06_E3 [⋀^Fin 1]→L[ℝ] ℝ
abbrev apm_t03J06_Form2 :=
  apm_t03J06_E3 → apm_t03J06_E3 [⋀^Fin 2]→L[ℝ] ℝ

def apm_t03J06_isOmega (omega : apm_t03J06_Form2) : Prop :=
  ∀ (x : apm_t03J06_E3) (v : Fin 2 → apm_t03J06_E3),
    omega x v =
      x 2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0) +
      (x 2 ^ 2 * Real.exp (x 0 * x 2) * Real.log (x 0 ^ 2 + 1) - x 1) *
        (v 0 0 * v 1 2 - v 0 2 * v 1 0) +
      (x 0 + x 1 ^ 2 * x 2 ^ 3 * Real.cos (x 1 ^ 2 + x 2 ^ 2)) *
        (v 0 1 * v 1 2 - v 0 2 * v 1 1)

def apm_t03J06_bullet : Set apm_t03J06_E3 :=
  {x | x 0 ^ 2 + x 1 ^ 2 = 1 ∧ -1 ≤ x 2 ∧ x 2 ≤ 1} ∪
  {x | x 0 ^ 2 + x 1 ^ 2 + (x 2 - 1) ^ 2 = 1 ∧ 1 ≤ x 2}

def apm_t03J06_vec3 (a b c : ℝ) : apm_t03J06_E3 :=
  EuclideanSpace.single 0 a + EuclideanSpace.single 1 b +
    EuclideanSpace.single 2 c

def apm_t03J06_cylinderPoint (θ z : ℝ) : apm_t03J06_E3 :=
  apm_t03J06_vec3 (Real.cos θ) (Real.sin θ) z

def apm_t03J06_cylinderTangents (θ : ℝ) : Fin 2 → apm_t03J06_E3 :=
  fun i ↦ if i = 0 then
    apm_t03J06_vec3 (-Real.sin θ) (Real.cos θ) 0
  else apm_t03J06_vec3 0 0 1

def apm_t03J06_hemispherePoint (p : ℝ × ℝ) : apm_t03J06_E3 :=
  apm_t03J06_vec3 p.1 p.2 (1 + Real.sqrt (1 - p.1 ^ 2 - p.2 ^ 2))

def apm_t03J06_hemisphereTangents (p : ℝ × ℝ) :
    Fin 2 → apm_t03J06_E3 :=
  let s := Real.sqrt (1 - p.1 ^ 2 - p.2 ^ 2)
  fun i ↦ if i = 0 then apm_t03J06_vec3 1 0 (-p.1 / s)
  else apm_t03J06_vec3 0 1 (-p.2 / s)

def apm_t03J06_unitDisk : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

/-- Integral of the pullback to the two oriented parametrization domains. -/
def apm_t03J06_bulletIntegral (omega : apm_t03J06_Form2) : ℝ :=
  (∫ θ in (0 : ℝ)..2 * Real.pi,
    ∫ z in (-1 : ℝ)..1,
      omega (apm_t03J06_cylinderPoint θ z)
        (apm_t03J06_cylinderTangents θ)) +
  ∫ p in apm_t03J06_unitDisk,
    omega (apm_t03J06_hemispherePoint p)
      (apm_t03J06_hemisphereTangents p)

/-- The displayed coefficient specification determines the alternating form
pointwise. -/
lemma apm_t03J06_isOmega_unique (omega eta : apm_t03J06_Form2)
    (homega : apm_t03J06_isOmega omega) (heta : apm_t03J06_isOmega eta) :
    omega = eta := by
  funext x
  ext v
  exact (homega x v).trans (heta x v).symm

@[simp] lemma apm_t03J06_vec3_apply (a b c : ℝ) (i : Fin 3) :
    apm_t03J06_vec3 a b c i = ![a, b, c] i := by
  fin_cases i <;> simp [apm_t03J06_vec3]

/-- The raw pullback coefficient on the cylindrical part. -/
lemma apm_t03J06_cylinder_integrand (omega : apm_t03J06_Form2)
    (homega : apm_t03J06_isOmega omega) (theta z : ℝ) :
    omega (apm_t03J06_cylinderPoint theta z)
        (apm_t03J06_cylinderTangents theta) =
      -(z ^ 2 * Real.exp (Real.cos theta * z) *
          Real.log (Real.cos theta ^ 2 + 1) - Real.sin theta) * Real.sin theta +
        (Real.cos theta + Real.sin theta ^ 2 * z ^ 3 *
          Real.cos (Real.sin theta ^ 2 + z ^ 2)) * Real.cos theta := by
  rw [homega]
  simp [apm_t03J06_cylinderPoint, apm_t03J06_cylinderTangents]
  ring

/-- The raw pullback coefficient on the hemispherical graph.  This exposes
the only singular-looking factors (`x / sqrt` and `y / sqrt`) explicitly. -/
lemma apm_t03J06_hemisphere_integrand (omega : apm_t03J06_Form2)
    (homega : apm_t03J06_isOmega omega) (p : ℝ × ℝ) :
    let s := Real.sqrt (1 - p.1 ^ 2 - p.2 ^ 2)
    omega (apm_t03J06_hemispherePoint p)
        (apm_t03J06_hemisphereTangents p) =
      (1 + s) -
        (apm_t03J06_hemispherePoint p 2 ^ 2 *
            Real.exp (p.1 * apm_t03J06_hemispherePoint p 2) *
            Real.log (p.1 ^ 2 + 1) - p.2) * (p.2 / s) +
        (p.1 + p.2 ^ 2 * apm_t03J06_hemispherePoint p 2 ^ 3 *
            Real.cos (p.2 ^ 2 + apm_t03J06_hemispherePoint p 2 ^ 2)) *
          (p.1 / s) := by
  dsimp only
  rw [homega]
  simp [apm_t03J06_hemispherePoint, apm_t03J06_hemisphereTangents]
  ring

/-- The displayed nonzero coordinate value of the exterior derivative makes
the exterior derivative itself nonzero. -/
lemma apm_t03J06_extDeriv_ne_zero_of_eval_three
    (omega : apm_t03J06_Form2)
    (hd : ∀ x : apm_t03J06_E3,
      extDeriv omega x (fun i ↦ EuclideanSpace.single i (1 : ℝ)) = 3) :
    extDeriv omega ≠ 0 := by
  intro hzero
  have h := hd 0
  rw [hzero] at h
  norm_num at h

/-- The same coordinate computation rules out a smooth primitive via
`extDeriv_extDeriv`, so the nonexactness conjunct needs no integration. -/
lemma apm_t03J06_not_exact_of_extDeriv_eval_three
    (omega : apm_t03J06_Form2)
    (hd : ∀ x : apm_t03J06_E3,
      extDeriv omega x (fun i ↦ EuclideanSpace.single i (1 : ℝ)) = 3) :
    ¬(∃ eta : apm_t03J06_Form1,
      ContDiff ℝ (⊤ : ℕ∞) eta ∧ extDeriv eta = omega) := by
  rintro ⟨eta, heta, hetaomega⟩
  have hzero : extDeriv (extDeriv eta) = 0 :=
    extDeriv_extDeriv heta (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have h := hd 0
  rw [← hetaomega, hzero] at h
  norm_num at h

lemma diagnostic_frozen_bulletIntegral (omega : apm_t03J06_Form2)
    (homega : apm_t03J06_isOmega omega) :
    apm_t03J06_bulletIntegral omega = 7 * Real.pi := by
  apply ConstructionTargets.T03J06FinalAdapter.bulletIntegral_eq_seven_pi
  · intro theta z
    rw [apm_t03J06_cylinder_integrand omega homega]
    rfl
  · intro p
    rw [apm_t03J06_hemisphere_integrand omega homega]
    simp [ConstructionTargets.CappedCylinderHemisphereIntegral.hemisphereIntegrand,
      ConstructionTargets.CappedCylinderHemisphereIntegral.capHeight,
      ConstructionTargets.HemisphereInverseSqrtDiskIntegral.xInverseSqrt,
      ConstructionTargets.HemisphereInverseSqrtDiskIntegral.yInverseSqrt,
      ConstructionTargets.HemisphereInverseSqrtDiskIntegral.inverseSqrtKernel,
      div_eq_mul_inv, apm_t03J06_hemispherePoint]

#print axioms diagnostic_frozen_bulletIntegral

lemma diagnostic_smooth (omega : apm_t03J06_Form2)
    (homega : apm_t03J06_isOmega omega) :
    ContDiff ℝ (⊤ : ℕ∞) omega := by
  have heq : omega = fun x =>
      x 2 • omega (apm_t03J06_vec3 0 0 1) +
      (x 2 ^ 2 * Real.exp (x 0 * x 2) * Real.log (x 0 ^ 2 + 1) - x 1) •
        omega (apm_t03J06_vec3 0 (-1) 0) +
      (x 0 + x 1 ^ 2 * x 2 ^ 3 * Real.cos (x 1 ^ 2 + x 2 ^ 2)) •
        omega (apm_t03J06_vec3 1 0 0) := by
    funext x
    ext v
    simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    rw [homega, homega, homega, homega]
    simp
  rw [heq]
  have hp : ∀ x : apm_t03J06_E3, x 0 ^ 2 + 1 ≠ 0 := by
    intro x; exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) zero_lt_one)
  clear heq homega
  fun_prop (disch := aesop)

#print axioms diagnostic_smooth


lemma diagnostic_direction (a : apm_t03J06_E3 → ℝ) (x w : apm_t03J06_E3)
    (c : ℝ) (ha : DifferentiableAt ℝ a x)
    (hline : ∀ t : ℝ, a (x + t • w) = a x + c * t) :
    fderiv ℝ a x w = c := by
  have hpath : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
    simpa only [Pi.add_apply, id_eq, zero_add, one_smul] using (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const w)
  have ha' : HasFDerivAt a (fderiv ℝ a x) (x + (0 : ℝ) • w) := by
    simpa using ha.hasFDerivAt
  have hd := ha'.comp_hasDerivAt 0 hpath
  have he : (fun t : ℝ => a (x + t • w)) = fun t => a x + c * t := funext hline
  change HasDerivAt (fun t : ℝ => a (x + t • w)) (fderiv ℝ a x w) 0 at hd
  rw [he] at hd
  have hc : HasDerivAt (fun t : ℝ => a x + c * t) c 0 := by
    simpa only [Pi.add_apply, id_eq, zero_add, mul_one] using (hasDerivAt_const (0 : ℝ) (a x)).add ((hasDerivAt_id (0 : ℝ)).const_mul c)
  exact hd.unique hc

lemma diagnostic_extDeriv (omega : apm_t03J06_Form2)
    (homega : apm_t03J06_isOmega omega) (x : apm_t03J06_E3) :
    extDeriv omega x (fun i => EuclideanSpace.single i (1 : ℝ)) = 3 := by
  rw [extDeriv_apply ((diagnostic_smooth omega homega).differentiable (by simp) x)]
  change (∑ j : Fin 3, (-1 : ℤ) ^ (j : ℕ) •
    fderiv ℝ (fun y => omega y (j.removeNth (fun i => EuclideanSpace.single i (1 : ℝ)))) x
      (EuclideanSpace.single j 1)) = 3
  rw [Fin.sum_univ_three]
  simp_rw [show ∀ v, (fun y => omega y v) = fun y =>
    y 2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0) +
    (y 2 ^ 2 * Real.exp (y 0 * y 2) * Real.log (y 0 ^ 2 + 1) - y 1) *
      (v 0 0 * v 1 2 - v 0 2 * v 1 0) +
    (y 0 + y 1 ^ 2 * y 2 ^ 3 * Real.cos (y 1 ^ 2 + y 2 ^ 2)) *
      (v 0 1 * v 1 2 - v 0 2 * v 1 1) from fun v => funext (fun y => homega y v)]
  simp only [Fin.removeNth]
  have hs : Fin.succAbove (2 : Fin 3) (1 : Fin 2) = 1 := rfl
  simp [hs]
  have h0 : fderiv ℝ (fun y : apm_t03J06_E3 =>
      y 0 + y 1 ^ 2 * y 2 ^ 3 * Real.cos (y 1 ^ 2 + y 2 ^ 2)) x
      (EuclideanSpace.single 0 1) = 1 := by
    apply diagnostic_direction
    · fun_prop
    · intro t; simp; ring
  have h1 : fderiv ℝ (fun y : apm_t03J06_E3 =>
      y 2 ^ 2 * Real.exp (y 0 * y 2) * Real.log (y 0 ^ 2 + 1) - y 1) x
      (EuclideanSpace.single 1 1) = -1 := by
    apply diagnostic_direction
    · have hp : x 0 ^ 2 + 1 ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) zero_lt_one)
      fun_prop (disch := assumption)
    · intro t; simp; ring
  have h2 : fderiv ℝ (fun y : apm_t03J06_E3 => y 2) x
      (EuclideanSpace.single 2 1) = 1 := by
    apply diagnostic_direction
    · fun_prop
    · intro t; simp
  rw [h0, h1, h2]
  norm_num

#print axioms diagnostic_direction
#print axioms diagnostic_extDeriv

theorem apm_t03j06 (omega : apm_t03J06_Form2)
    (homega : apm_t03J06_isOmega omega) :
    ContDiff ℝ (⊤ : ℕ∞) omega ∧
    (∀ x : apm_t03J06_E3,
      extDeriv omega x (fun i ↦ EuclideanSpace.single i (1 : ℝ)) = 3) ∧
    extDeriv omega ≠ 0 ∧
    ¬(∃ eta : apm_t03J06_Form1,
      ContDiff ℝ (⊤ : ℕ∞) eta ∧ extDeriv eta = omega) ∧
    apm_t03J06_bulletIntegral omega = 7 * Real.pi := by
  have hs := diagnostic_smooth omega homega
  have hd := diagnostic_extDeriv omega homega
  exact ⟨hs, hd, apm_t03J06_extDeriv_ne_zero_of_eval_three omega hd,
    apm_t03J06_not_exact_of_extDeriv_eval_three omega hd,
    diagnostic_frozen_bulletIntegral omega homega⟩

#print axioms apm_t03j06
