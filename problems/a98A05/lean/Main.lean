import Mathlib

/-!
# APM a98A05

## Statement repairs

None.

## Encoding questions

None.  The improper integral over `(0, ∞)` is represented as the Lebesgue
integral over `Set.Ioi 0`.
-/

open MeasureTheory Set

noncomputable section

/-- The real partial-fraction decomposition, with positivity facts packaged so
later improper-integration steps have no pole side conditions. -/
lemma apm_a98a05_partial_fractions {x : ℝ} (hx : 0 ≤ x) :
    0 < x + 1 ∧ 0 < x ^ 2 - x + 1 ∧
      1 / (1 + x ^ 3) =
        (1 / 3 : ℝ) / (x + 1) + (2 - x) / (3 * (x ^ 2 - x + 1)) := by
  have hx1 : 0 < x + 1 := by linarith
  have hq : 0 < x ^ 2 - x + 1 := by
    nlinarith [sq_nonneg (x - (1 / 2 : ℝ))]
  refine ⟨hx1, hq, ?_⟩
  have hcubic : 1 + x ^ 3 = (x + 1) * (x ^ 2 - x + 1) := by ring
  rw [hcubic]
  let A : ℝ := x + 1
  let Q : ℝ := x ^ 2 - x + 1
  have hA : A ≠ 0 := by simpa [A] using ne_of_gt hx1
  have hQ : Q ≠ 0 := by simpa [Q] using ne_of_gt hq
  change 1 / (A * Q) = (1 / 3 : ℝ) / A + (2 - x) / (3 * Q)
  field_simp [hA, hQ]
  simp [A, Q]
  ring

/-- The real antiderivative used for the improper-integral evaluation. -/
def apm_a98a05_primitive (x : ℝ) : ℝ :=
  (1 / 3 : ℝ) * Real.log (x + 1) -
    (1 / 6 : ℝ) * Real.log (x ^ 2 - x + 1) +
      Real.sqrt 3 / 3 * Real.arctan ((2 * x - 1) / Real.sqrt 3)

/-- The displayed primitive differentiates to the integrand on the
nonnegative half-line.  The arctangent normalization follows the calculation
in the solved sibling `a94A06`. -/
lemma apm_a98a05_hasDerivAt_primitive {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt apm_a98a05_primitive (1 / (1 + x ^ 3)) x := by
  have hsqrt : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq : 0 < x ^ 2 - x + 1 := (apm_a98a05_partial_fractions hx).2.1
  have h1 : HasDerivAt (fun y : ℝ => (1 / 3 : ℝ) * Real.log (y + 1))
      ((1 / 3 : ℝ) / (x + 1)) x := by
    have hd : HasDerivAt (fun y : ℝ => y + 1) 1 x :=
      (hasDerivAt_id x).add_const 1
    convert (hd.log (by linarith)).const_mul (1 / 3 : ℝ) using 1 <;> ring
  have h2 : HasDerivAt
      (fun y : ℝ => -(1 / 6 : ℝ) * Real.log (y ^ 2 - y + 1))
      ((2 * x - 1) / (x ^ 2 - x + 1) * (-(1 / 6 : ℝ))) x := by
    have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      convert hasDerivAt_pow 2 x using 1 <;> ring
    have hd : HasDerivAt (fun y : ℝ => y ^ 2 - y + 1) (2 * x - 1) x :=
      (hp.sub (hasDerivAt_id x)).add_const 1
    convert (hd.log hq.ne').const_mul (-(1 / 6 : ℝ)) using 1 <;> ring
  have h3 : HasDerivAt
      (fun y : ℝ => Real.sqrt 3 / 3 *
        Real.arctan ((2 * y - 1) / Real.sqrt 3))
      (1 / (2 * (x ^ 2 - x + 1))) x := by
    have hd : HasDerivAt (fun y : ℝ => (2 * y - 1) / Real.sqrt 3)
        (2 / Real.sqrt 3) x := by
      convert ((hasDerivAt_id x).const_mul 2).sub_const 1 |>.div_const
        (Real.sqrt 3) using 1 <;> ring
    convert hd.arctan.const_mul (Real.sqrt 3 / 3) using 1
    rw [div_pow, hsqrt]
    rw [show x ^ 2 - x + 1 = 1 - x + x ^ 2 by ring]
    have hq' : (1 - x + x ^ 2 : ℝ) ≠ 0 := by nlinarith
    field_simp [hq']
    ring
  unfold apm_a98a05_primitive
  convert h1.add h2 |>.add h3 using 1
  · funext y
    simp only [Pi.add_apply]
    congr 2 <;> ring
  · rw [(apm_a98a05_partial_fractions hx).2.2]
    field_simp [hq.ne']
    ring

theorem apm_a98a05 :
    ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) ∂volume =
      2 * Real.pi / (3 * Real.sqrt 3) := by
  /-
  Boundary (closer hops 1--2): `apm_a98a05_partial_fractions` above compiles
  the exact decomposition

  `1/(1+x³) = (1/3)/(x+1) + (2-x)/(3(x²-x+1))`

  on the nonnegative half-line and simultaneously proves both denominators
  positive.  Hop 2 packages the following antiderivative as
  `apm_a98a05_primitive` and proves its exact derivative on the nonnegative
  half-line in `apm_a98a05_hasDerivAt_primitive`:

  `(1/3) log (x+1) - (1/6) log (x²-x+1)
     + (1/√3) arctan ((2*x-1)/√3)`.

  Searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`, Mathlib's
  Gamma/Beta, improper-integral, substitution, logarithm, and arctangent
  sources, prior exact-integral artifacts, and git history found no packaged
  formula for `∫₀∞ 1/(1+x^n)` and no direct substitution reducing this
  integral to `betaIntegral (1/3) (2/3)`.  Mathlib does provide
  `integral_Ioi_of_hasDerivAt_of_tendsto'`, the derivative rules, and the
  Gamma reflection ingredients, but assembling either route still requires
  proving integrability and the cancellation of the two divergent logarithmic
  terms at infinity.  The remaining closure work is now the endpoint
  evaluation, especially that logarithmic cancellation, followed by the
  improper FTC theorem.
  -/
  sorry
