import Mathlib

/-!
# APM m93J01: The sixth-order Numerov scheme

## Statement repairs

1. The remainders printed as `o(h⁶)` in (a),(b) and `o(h⁴)` in (c)
   must be `O(h⁶)` and `O(h⁴)`: the next Taylor terms generally have
   exactly those orders.
2. Part (b) is dimensionally missing the factor `h²` on `(Ly)ₙ`, and the
   fourth-derivative correction must have sign `+`. We state the corrected
   identity confirmed by direct substitution and by the supplied solution.
3. The lowercase `vₙ` in part (b) is interpreted as the sampled potential
   `V(nh)` defined in the preamble.

## Encoding questions

None. Grid identities are stated at an arbitrary center `x`, with mesh size
`h → 0`; taking `x = nh` recovers the printed nodal notation.
-/

open Filter Asymptotics
open scoped Topology

noncomputable section

def apm_m93J01_kappa : ℝ := 1 / 12

def apm_m93J01_schrodinger (V y : ℝ → ℝ) (x : ℝ) : ℝ :=
  -iteratedDeriv 2 y x + V x * y x

/-- The residual in the discrete Schrödinger identity is exactly the centered
Taylor residual; no additional analytic estimate is needed for part (b). -/
lemma apm_m93J01_schrodinger_residual_eq
    (y V : ℝ → ℝ) (x h : ℝ) :
    h ^ 2 * apm_m93J01_schrodinger V y x -
        (-y (x + h) - y (x - h) +
          (2 + h ^ 2 * V x) * y x +
          apm_m93J01_kappa * h ^ 4 * iteratedDeriv 4 y x) =
      y (x + h) + y (x - h) - 2 * y x -
        (h ^ 2 * iteratedDeriv 2 y x +
          apm_m93J01_kappa * h ^ 4 * iteratedDeriv 4 y x) := by
  simp only [apm_m93J01_schrodinger]
  ring

/-- A translated sixth-order Taylor estimate in the exact neighborhood-filter
form needed by the centered Numerov calculation. -/
lemma apm_m93J01_taylor6_isLittleO
    (y : ℝ → ℝ) (hy : ContDiff ℝ 6 y) (x : ℝ) :
    (fun h : ℝ ↦ y (x + h) -
      (y x + h * iteratedDeriv 1 y x + h ^ 2 / 2 * iteratedDeriv 2 y x +
       h ^ 3 / 6 * iteratedDeriv 3 y x + h ^ 4 / 24 * iteratedDeriv 4 y x +
       h ^ 5 / 120 * iteratedDeriv 5 y x + h ^ 6 / 720 * iteratedDeriv 6 y x))
      =o[nhds 0] (fun h : ℝ ↦ h ^ 6) := by
  have ht : Tendsto (fun h : ℝ ↦ x + h) (nhds 0) (nhds x) := by
    simpa using (tendsto_const_nhds.add tendsto_id :
      Tendsto (fun h : ℝ ↦ x + h) (nhds 0) (nhds (x + 0)))
  have h := (taylor_isLittleO_univ hy (x₀ := x)).comp_tendsto ht
  convert h using 1
  · funext z
    simp [taylor_within_apply, iteratedDerivWithin_univ]
    ring
  · funext z
    simp

/-- Adding the Taylor expansions at `h` and `-h` cancels all odd terms. -/
lemma apm_m93J01_centered6_isBigO
    (y : ℝ → ℝ) (hy : ContDiff ℝ 6 y) (x : ℝ) :
    (fun h : ℝ ↦
      y (x + h) + y (x - h) - 2 * y x -
        (h ^ 2 * iteratedDeriv 2 y x +
          apm_m93J01_kappa * h ^ 4 * iteratedDeriv 4 y x))
      =O[nhds 0] (fun h : ℝ ↦ h ^ 6) := by
  have hp := apm_m93J01_taylor6_isLittleO y hy x
  have ht : Tendsto (fun h : ℝ ↦ -h) (nhds 0) (nhds 0) :=
    by simpa using (tendsto_id.neg : Tendsto (fun h : ℝ ↦ -h) (nhds 0) (nhds (-0)))
  have hm0 := (apm_m93J01_taylor6_isLittleO y hy x).comp_tendsto ht
  have hm :
      (fun h : ℝ ↦ y (x - h) -
        (y x + (-h) * iteratedDeriv 1 y x + (-h) ^ 2 / 2 * iteratedDeriv 2 y x +
         (-h) ^ 3 / 6 * iteratedDeriv 3 y x + (-h) ^ 4 / 24 * iteratedDeriv 4 y x +
         (-h) ^ 5 / 120 * iteratedDeriv 5 y x + (-h) ^ 6 / 720 * iteratedDeriv 6 y x))
        =o[nhds 0] (fun h : ℝ ↦ h ^ 6) := by
    convert hm0 using 1 <;> funext h <;> simp <;> ring
  have hs := (hp.add hm).isBigO
  have hterm :
      (fun h : ℝ ↦ h ^ 6 / 360 * iteratedDeriv 6 y x)
        =O[nhds 0] (fun h : ℝ ↦ h ^ 6) := by
    convert (isBigO_refl (fun h : ℝ ↦ h ^ 6) (nhds 0)).const_mul_left
      (iteratedDeriv 6 y x / 360) using 1
    funext h
    ring
  convert hs.add hterm using 1
  funext h
  simp only [apm_m93J01_kappa]
  ring

/-- Why this unblocks `apm_m93j01`: applying the order-four centered Taylor
estimate to `iteratedDeriv 2 y` requires transferring `ContDiff ℝ 8 y` to that
derived function and identifying its second and fourth iterated derivatives
with orders four and six of `y`.  This is precisely the remaining analytic
estimate used by part (c) and the final Numerov substitution. -/
theorem apm_m93J01_bridge_1
    (y : ℝ → ℝ) (hy : ContDiff ℝ 8 y) (x : ℝ) :
    (fun h : ℝ ↦
      iteratedDeriv 2 y (x + h) + iteratedDeriv 2 y (x - h) -
        2 * iteratedDeriv 2 y x - h ^ 2 * iteratedDeriv 4 y x)
      =O[nhds 0] (fun h : ℝ ↦ h ^ 4) := by
  sorry

theorem apm_m93j01
    (y V : ℝ → ℝ) (hy : ContDiff ℝ 8 y) :
    apm_m93J01_kappa = (1 / 12 : ℝ) ∧
    (∀ x : ℝ,
      (fun h : ℝ ↦
        y (x + h) + y (x - h) - 2 * y x -
          (h ^ 2 * iteratedDeriv 2 y x +
            apm_m93J01_kappa * h ^ 4 * iteratedDeriv 4 y x))
        =O[nhds 0] (fun h : ℝ ↦ h ^ 6)) ∧
    (∀ x : ℝ,
      (fun h : ℝ ↦
        h ^ 2 * apm_m93J01_schrodinger V y x -
          (-y (x + h) - y (x - h) +
            (2 + h ^ 2 * V x) * y x +
            apm_m93J01_kappa * h ^ 4 * iteratedDeriv 4 y x))
        =O[nhds 0] (fun h : ℝ ↦ h ^ 6)) ∧
    (∀ x : ℝ,
      (fun h : ℝ ↦
        iteratedDeriv 2 y (x + h) + iteratedDeriv 2 y (x - h) -
          2 * iteratedDeriv 2 y x - h ^ 2 * iteratedDeriv 4 y x)
        =O[nhds 0] (fun h : ℝ ↦ h ^ 4)) ∧
    ((∀ x : ℝ, apm_m93J01_schrodinger V y x = 0) →
      ∀ x : ℝ,
        (fun h : ℝ ↦
          (1 - h ^ 2 / 12 * V (x + h)) * y (x + h) -
          (2 + 5 * h ^ 2 / 6 * V x) * y x +
          (1 - h ^ 2 / 12 * V (x - h)) * y (x - h))
          =O[nhds 0] (fun h : ℝ ↦ h ^ 6)) := by
  refine ⟨rfl, ?_⟩
  /-
  Boundary: the remaining clauses require a symmetric Taylor estimate with
  an `IsBigO (h ^ 6)` remainder for `y`, and the analogous `IsBigO (h ^ 4)`
  estimate for `iteratedDeriv 2 y`. I searched Mathlib's Taylor APIs
  `taylor_mean_remainder_bound`, `exists_taylor_mean_remainder_bound`, and
  `taylor_mean_remainder_lagrange_iteratedDeriv`. They give interval-wise
  remainder bounds, but I did not complete the substantial bridge from those
  bounds to the neighborhood-filter statements here, including rewriting
  `taylorWithinEval` coefficients as the stated `iteratedDeriv` expressions.

  Once those two estimates are available, the second clause follows
  algebraically from the first and the definition of
  `apm_m93J01_schrodinger`; the final Numerov residual follows by using the
  ODE to rewrite `iteratedDeriv 2 y = V * y`, applying the fourth-order
  estimate, and combining Big-O terms. No compiled sibling proof supplied
  this Taylor-to-filter bridge.

  Closer hop 1 proves `apm_m93J01_schrodinger_residual_eq` above, so the
  second clause is now reduced definitionally and algebraically to the first.
  Further searches covered the generic `WeakBilin`-style asymptotic corpus,
  `Analysis/Analytic/Basic.lean` (whose Taylor `IsBigO` theorem requires
  analyticity), ContDiff/Faa-di-Bruno, all fully closed artifacts, and the
  construction libraries. None returned a finite-order `ContDiff` Taylor
  `IsBigO` theorem. The live boundary is therefore precisely a reusable local
  lemma converting `hy : ContDiff ℝ 8 y` into the symmetric sixth-order
  neighborhood estimate (and its fourth-order specialization for
  `iteratedDeriv 2 y`); the remaining Numerov algebra can then reuse those
  estimates.

  Closer hop 2 found and compiled the direct finite-order API that the earlier
  searches missed: `taylor_isLittleO_univ`.  The helper
  `apm_m93J01_taylor6_isLittleO` above composes it with `h ↦ x + h` and
  normalizes `taylorWithinEval` to the exact `iteratedDeriv` coefficients.
  Thus the Taylor-to-neighborhood-filter bridge is closed.  The remaining
  work is to compose the helper with negation, cancel the odd coefficients,
  weaken the two little-o remainders to `O(h^6)`, and repeat at order four
  for `iteratedDeriv 2 y`; the final Numerov algebra then uses the existing
  residual identity.

  Closer hop 3 proves `apm_m93J01_centered6_isBigO`, completing the symmetric
  sixth-order estimate in part (a). It composes the Taylor remainder with
  negation, cancels the odd coefficients, and treats the surviving sixth-order
  coefficient as an explicit `O(h^6)` term. Part (b) can consequently reuse
  the existing residual identity. The remaining bridge is the order-four
  centered estimate for `iteratedDeriv 2 y`: it requires deriving the needed
  `ContDiff ℝ 4` fact from `hy : ContDiff ℝ 8 y` and normalizing iterated
  derivatives of that derivative function back to orders four and six of `y`.
  The final ODE substitution then remains algebraic.
  -/
  sorry
