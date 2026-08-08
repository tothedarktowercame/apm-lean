import Mathlib

/-!
# APM m93J03: A nonlinear integral equation near its trivial branch

## Statement repairs

The printed global uniqueness claim is stronger than, and is not established
by, the intended implicit-function argument. The exact finite-dimensional
reduction has additional nonzero branches already at `ε = 0`; the invertible
Jacobian proves uniqueness only in a neighborhood of the trivial solution.
We therefore state the minimally repaired local result: fixed radii `δ,η > 0`
give a unique solution with `|ε| < δ` and uniform size below `η`.

## Encoding questions

None. The equation uses the Lebesgue integral on `[-π,π]`; continuity and
uniqueness are both restricted to that exact interval.
-/

open MeasureTheory Set

noncomputable section

def apm_m93J03_isSolution (ε : ℝ) (x : ℝ → ℝ) : Prop :=
  ContinuousOn x (Icc (-Real.pi) Real.pi) ∧
  ∀ t ∈ Icc (-Real.pi) Real.pi,
    x t = ε + ∫ s in Icc (-Real.pi) Real.pi, Real.sin (t + s + x s)

def apm_m93J03_isSmall (x : ℝ → ℝ) (η : ℝ) : Prop :=
  ∀ t ∈ Icc (-Real.pi) Real.pi, |x t| < η

lemma apm_m93J03_isSmall_mono {x : ℝ → ℝ} {η η' : ℝ}
    (hx : apm_m93J03_isSmall x η) (hη : η ≤ η') :
    apm_m93J03_isSmall x η' := by
  intro t ht
  exact (hx t ht).trans_le hη

lemma apm_m93J03_zero_isSmall {η : ℝ} (hη : 0 < η) :
    apm_m93J03_isSmall (fun _ ↦ 0) η := by
  intro t ht
  simpa using hη

/-- Separating `sin (t + s + x s)` shows that every solution belongs to the
three-dimensional affine span of `1`, `sin`, and `cos`.  This is the exact
function-level reduction needed before applying the finite-dimensional
implicit-function theorem. -/
lemma apm_m93J03_solution_eq_affine_trig {ε : ℝ} {x : ℝ → ℝ}
    (hx : apm_m93J03_isSolution ε x) :
    ∃ a b : ℝ, ∀ t ∈ Icc (-Real.pi) Real.pi,
      x t = ε + a * Real.sin t + b * Real.cos t := by
  let u : ℝ → ℝ := fun s ↦ s + x s
  have hu : ContinuousOn u (Icc (-Real.pi) Real.pi) :=
    continuousOn_id.add hx.1
  have hcos : IntegrableOn (fun s ↦ Real.cos (u s))
      (Icc (-Real.pi) Real.pi) :=
    (Real.continuous_cos.comp_continuousOn hu).integrableOn_Icc
  have hsin : IntegrableOn (fun s ↦ Real.sin (u s))
      (Icc (-Real.pi) Real.pi) :=
    (Real.continuous_sin.comp_continuousOn hu).integrableOn_Icc
  refine ⟨∫ s in Icc (-Real.pi) Real.pi, Real.cos (u s),
    ∫ s in Icc (-Real.pi) Real.pi, Real.sin (u s), ?_⟩
  intro t ht
  rw [hx.2 t ht]
  have hpoint : ∀ s : ℝ,
      Real.sin (t + s + x s) =
        Real.sin t * Real.cos (u s) + Real.cos t * Real.sin (u s) := by
    intro s
    rw [show t + s + x s = t + u s by simp [u, add_assoc], Real.sin_add]
  rw [setIntegral_congr_fun measurableSet_Icc (fun s _ ↦ hpoint s)]
  rw [integral_add (hcos.const_mul _) (hsin.const_mul _),
    integral_const_mul, integral_const_mul]
  ring

def apm_m93J03_affineTrig (ε a b t : ℝ) : ℝ :=
  ε + a * Real.sin t + b * Real.cos t

/-- The exact two-dimensional residual to which the implicit-function theorem
is applied after the affine-trigonometric reduction. -/
def apm_m93J03_residual (ε : ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (q.1 - ∫ s in Icc (-Real.pi) Real.pi,
      Real.cos (s + apm_m93J03_affineTrig ε q.1 q.2 s),
    q.2 - ∫ s in Icc (-Real.pi) Real.pi,
      Real.sin (s + apm_m93J03_affineTrig ε q.1 q.2 s))

/-- A zero of the reduced residual reconstructs a genuine solution of the
original function-valued equation. -/
lemma apm_m93J03_isSolution_affineTrig_of_residual_eq_zero
    {ε a b : ℝ} (hres : apm_m93J03_residual ε (a, b) = 0) :
    apm_m93J03_isSolution ε (apm_m93J03_affineTrig ε a b) := by
  have ha : a = ∫ s in Icc (-Real.pi) Real.pi,
      Real.cos (s + apm_m93J03_affineTrig ε a b s) := by
    have h := congrArg Prod.fst hres
    simpa [apm_m93J03_residual] using sub_eq_zero.mp h
  have hb : b = ∫ s in Icc (-Real.pi) Real.pi,
      Real.sin (s + apm_m93J03_affineTrig ε a b s) := by
    have h := congrArg Prod.snd hres
    simpa [apm_m93J03_residual] using sub_eq_zero.mp h
  have hcont : Continuous (apm_m93J03_affineTrig ε a b) :=
    (continuous_const.add (continuous_const.mul Real.continuous_sin)).add
      (continuous_const.mul Real.continuous_cos)
  constructor
  · exact hcont.continuousOn
  · intro t ht
    have hu : ContinuousOn
        (fun s ↦ s + apm_m93J03_affineTrig ε a b s)
        (Icc (-Real.pi) Real.pi) := continuousOn_id.add hcont.continuousOn
    have hcos : IntegrableOn
        (fun s ↦ Real.cos (s + apm_m93J03_affineTrig ε a b s))
        (Icc (-Real.pi) Real.pi) :=
      (Real.continuous_cos.comp_continuousOn hu).integrableOn_Icc
    have hsin : IntegrableOn
        (fun s ↦ Real.sin (s + apm_m93J03_affineTrig ε a b s))
        (Icc (-Real.pi) Real.pi) :=
      (Real.continuous_sin.comp_continuousOn hu).integrableOn_Icc
    have hpoint : ∀ s : ℝ,
        Real.sin (t + s + apm_m93J03_affineTrig ε a b s) =
          Real.sin t * Real.cos (s + apm_m93J03_affineTrig ε a b s) +
          Real.cos t * Real.sin (s + apm_m93J03_affineTrig ε a b s) := by
      intro s
      rw [show t + s + apm_m93J03_affineTrig ε a b s =
        t + (s + apm_m93J03_affineTrig ε a b s) by ring, Real.sin_add]
    have hint : (∫ s in Icc (-Real.pi) Real.pi,
        Real.sin (t + s + apm_m93J03_affineTrig ε a b s)) =
        Real.sin t * a + Real.cos t * b := by
      rw [setIntegral_congr_fun measurableSet_Icc (fun s _ ↦ hpoint s),
        integral_add (hcos.const_mul _) (hsin.const_mul _),
        integral_const_mul, integral_const_mul, ← ha, ← hb]
    rw [hint]
    simp only [apm_m93J03_affineTrig]
    ring

theorem apm_m93j03 :
    ∃ δ η : ℝ, 0 < δ ∧ 0 < η ∧
      ∀ ε : ℝ, |ε| < δ →
        ∃ x : ℝ → ℝ,
          apm_m93J03_isSolution ε x ∧
          apm_m93J03_isSmall x η ∧
          ∀ y : ℝ → ℝ,
            apm_m93J03_isSolution ε y →
            apm_m93J03_isSmall y η →
            EqOn x y (Icc (-Real.pi) Real.pi) := by
  /-
  CLOSER HOP 1 (partial). The uniform-radius bookkeeping is now compiled:
  `apm_m93J03_isSmall_mono` permits enlarging a valid solution radius and
  `apm_m93J03_zero_isSmall` supplies the trivial-branch base case.

  The remaining boundary: the intended proof first separates the sine kernel and proves
  that every solution on the interval has the exact form
  `ε + a * sin t + b * cos t`. It must then define the resulting map
  `H : ℝ × (ℝ × ℝ) → ℝ × ℝ`, establish its strict Frechet
  derivative by differentiating two parameterized interval integrals, and
  identify the partial Jacobian at zero with the invertible diagonal map
  having entries `1 + π` and `1 - π`.

  Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, solved
  implicit-function artifacts, the parametric-integral sources, and git
  history found no complete reduction. Mathlib's product-domain implicit-function APIs
  `ContDiffAt.implicitFunction`,
  `ContDiffAt.eventually_apply_eq_iff_implicitFunction`, and
  `HasStrictFDerivAt.implicitFunctionOfProdDomain`. Applying them here still
  requires the missing derivative-under-the-integral construction and the
  final conversion of their neighborhood uniqueness into the statement's
  uniform `apm_m93J03_isSmall` radius for arbitrary function-valued
  solutions. No compiled sibling supplied those bridges in this pass.

  CLOSER HOP 2 (partial). The function-level finite-dimensional reduction is
  now closed by `apm_m93J03_solution_eq_affine_trig`. For every frozen
  solution it constructs the two coefficients as the integrals of
  `cos (s + x s)` and `sin (s + x s)` and proves pointwise on the interval
  that `x t = ε + a * sin t + b * cos t`. Continuity of the solution supplies
  both restricted integrability obligations, and `Real.sin_add` plus
  `integral_add` and `integral_const_mul` perform the exact separation. Thus
  arbitrary function-valued uniqueness can now be reduced to uniqueness of
  the coefficient pair once the local finite-dimensional theorem is built.

  Searches beyond hop 1 inspected the repository's compiled parameter-
  differentiation users (`a01A09`, `a99J09`, `m93A04`, and `m98A03`) and
  Mathlib's dominated derivative-under-integral API. They confirm an available
  route but do not package the two-variable strict Frechet derivative needed
  here. The remaining bridge is to define the coefficient residual map,
  establish that derivative and its invertibility at zero, apply the product-
  domain implicit-function theorem, and extract uniform scalar radii. The
  frozen statement remains unchanged.

  CLOSER HOP 3 (partial). The finite-dimensional equation is now explicitly
  packaged. `apm_m93J03_affineTrig` defines the reconstructed function and
  `apm_m93J03_residual` defines the exact pair of coefficient residuals.
  `apm_m93J03_isSolution_affineTrig_of_residual_eq_zero` proves that every
  zero of this residual gives a genuine solution of the original integral
  equation, including continuity and the full pointwise identity on the
  frozen interval. It reuses the sine-addition separation and restricted-
  integral calculation from hop 2, so the future implicit-function theorem
  no longer needs to manipulate function-valued solutions on its existence
  side.

  I additionally inspected `Analysis.Calculus.Implicit`,
  `ImplicitFunction.ProdDomain`, `ImplicitContDiff`, the parameter-integral
  differentiation sources, and sibling `m98A05`. They provide the abstract
  local implicit-function machinery, but still no packaged strict Frechet
  derivative for these two parameterized set integrals. The remaining bridge
  is precisely that derivative/Jacobian computation, its invertibility, and
  extraction of uniform scalar radii plus coefficient uniqueness. The frozen
  statement remains unchanged.

  HOP 4 inspected
  `hasFDerivAt_integral_of_dominated_of_fderiv_le`, its set/interval
  variants, and `HasStrictFDerivAt.implicitFunctionOfProdDomain`. The former
  produces only an ordinary Frechet derivative, while the latter genuinely
  requires a strict derivative. No theorem in this snapshot upgrades these
  parameter integrals to a strict derivative or packages their smoothness.

  The exact missing lemma is:

    `∃ L : (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × ℝ),
      HasStrictFDerivAt
        (fun z : ℝ × (ℝ × ℝ) => apm_m93J03_residual z.1 z.2)
        L (0, (0, 0)) ∧
      ∀ h : ℝ × (ℝ × ℝ),
        L h = ((1 + Real.pi) * h.2.1,
          (1 - Real.pi) * h.2.2)`.

  The formula follows by differentiating under the two restricted integrals:
  the mixed and epsilon entries integrate `sin`, `cos`, or `sin*cos` to zero,
  while `sin^2` and `cos^2` both integrate to `π`. Its partial map in the
  coefficient variables is therefore diagonal with nonzero entries
  `1 + π` and `1 - π`, exactly what the product-domain implicit-function
  theorem needs. Proving this strict estimate (or a `ContDiff` theorem that
  implies it) remains the identified Mathlib hole; no weaker assertion was
  introduced and the frozen statement is unchanged.
  -/
  sorry
