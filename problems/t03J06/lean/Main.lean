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

theorem apm_t03j06 (omega : apm_t03J06_Form2)
    (homega : apm_t03J06_isOmega omega) :
    ContDiff ℝ (⊤ : ℕ∞) omega ∧
    (∀ x : apm_t03J06_E3,
      extDeriv omega x (fun i ↦ EuclideanSpace.single i (1 : ℝ)) = 3) ∧
    extDeriv omega ≠ 0 ∧
    ¬(∃ eta : apm_t03J06_Form1,
      ContDiff ℝ (⊤ : ℕ∞) eta ∧ extDeriv eta = omega) ∧
    apm_t03J06_bulletIntegral omega = 7 * Real.pi := by
  /-
  Boundary (closer hop 3): hop 2 went beyond the initial API search by
  compiling the pointwise algebra on both surface pieces.
  `apm_t03J06_isOmega_unique` proves that the coefficient predicate leaves no
  freedom in `omega`. `apm_t03J06_vec3_apply` exposes its three coordinates,
  and `apm_t03J06_cylinder_integrand` and
  `apm_t03J06_hemisphere_integrand` substitute both parametrizations and their
  oriented tangent pairs into the frozen form. Thus the remaining integral is
  now a concrete scalar integral, including the hemisphere's explicit
  `pᵢ / sqrt (1-p₀²-p₁²)` boundary factors.

  Going beyond that boundary, hop 3 proves
  `apm_t03J06_extDeriv_ne_zero_of_eval_three`: the displayed coordinate value
  `3` immediately makes `extDeriv omega` nonzero. It also proves
  `apm_t03J06_not_exact_of_extDeriv_eval_three`, applying Mathlib's
  `extDeriv_extDeriv` to rule out every smooth primitive. Consequently the
  theorem's second conjunct now implies both its third and fourth conjuncts;
  no integration or additional smoothness computation is needed for them.

  The intended short route still needs a Stokes/divergence theorem identifying
  the sum of these parametrized surface integrals with the integral of
  `extDeriv omega` over the solid cylinder-plus-hemisphere. Mathlib's
  `MeasureTheory.Integral.DivergenceTheorem` is for rectangular boxes and its
  differential-form API has `extDeriv_extDeriv`, but no integration/Stokes
  bridge for this surface encoding. Direct integration instead requires
  two-dimensional disk symmetry/change-of-variables results and domination
  for the displayed boundary quotients.

  Renewed searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`, Mathlib's
  differential-form, divergence, disk/radial-integration, and parametrized-
  integral sources, git history, and siblings `t01J06`, `t02A05`, `t94A10`,
  `t96J08`, and `m96J03` found no packaged bridge. In particular `t96J08`
  contains essentially the same hemisphere parametrization but its theorem
  remains unproved. The frozen statement is unchanged.
  -/
  sorry
