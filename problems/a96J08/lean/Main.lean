/-
! # APM a96J08: Evaluate ∫_{-∞}^{∞} e^{ωx}/(1-e^x) dx for 0 < Re(ω) < 1

The integral equals **-π cot(πω)**.

## Proof strategy

Use a rectangular contour with corners at -R and R+2πi, exploiting the 2πi periodicity
of e^z. The bottom edge gives the integral I, the top edge gives -e^{2πiω}I (period shift),
and the vertical edges vanish as R → ∞ (since 0 < Re(ω) < 1). The pole at z = 0 on the
bottom edge contributes a half-residue via indentation, and the pole at z = 2πi on the
top edge contributes similarly. Solving: I(1 - e^{2πiω}) = -πi(1 + e^{2πiω}),
hence I = -π cot(πω).

## Mathlib infrastructure

- `integral_boundary_rect_eq_zero_of_differentiableOn`: Cauchy-Goursat for rectangles
- `circleIntegral.integral_sub_inv_of_mem_ball`: residue of 1/(z-a) = 2πi
- `Complex.exp_add`: e^{a+b} = e^a · e^b (period shift)
- `Complex.abs_exp`: |e^z| = e^{Re(z)} (edge estimates)

## Statement note

The integral is a principal value (pole at x = 0). The statement uses a symmetric
truncation parameter δ for the principal value and R for the tail.
-/

import Mathlib.Analysis.Complex.CauchyIntegral

open Complex MeasureTheory Set Filter Topology

open scoped Real

noncomputable section

/-- The integrand e^{ωx}/(1 - e^x). -/
def integrand (ω : ℂ) (x : ℝ) : ℂ := Complex.exp (ω * x) / (1 - Complex.exp x)

/-- Reflection in the singular point exchanges the parameters `ω` and `1 - ω`.
This is the elementary symmetry behind the oddness of the principal value under
`ω ↦ 1 - ω`; it also reduces any eventual analytic evaluation to half of the
critical strip. -/
lemma integrand_one_sub_neg (ω : ℂ) (x : ℝ) :
    integrand (1 - ω) (-x) = -integrand ω x := by
  unfold integrand
  push_cast
  rw [show (1 - ω) * (-(x : ℂ)) = ω * x - x by ring,
    Complex.exp_sub, Complex.exp_neg]
  field_simp [Complex.exp_ne_zero]
  rw [show (Complex.exp (x : ℂ) - 1) = -(1 - Complex.exp x) by ring,
    div_neg]

/-- **Main theorem**: ∫_{-∞}^{∞} e^{ωx}/(1-e^x) dx = -π cot(πω) for 0 < Re(ω) < 1.

    The integral is interpreted as a principal value at x = 0 (where 1-e^x has a simple zero).
    The answer is -π cos(πω)/sin(πω) = -π cot(πω). -/
theorem apm_a96J08 (ω : ℂ) (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) :
    Tendsto (fun δ : ℝ =>
      (∫ x in -(δ⁻¹)..(-δ), integrand ω x) + (∫ x in δ..δ⁻¹, integrand ω x))
      (𝓝[>] 0) (𝓝 (-π * Complex.cos (π * ω) / Complex.sin (π * ω))) := by
  -- The proof uses a rectangular contour with corners at -R and R+2πi.
  -- Bottom edge: ∫_{-R}^{R} f(x) dx → I (principal value)
  -- Top edge: ∫_{R}^{-R} f(x+2πi) dx = -e^{2πiω} I (period shift, reversed direction)
  -- Vertical edges → 0 as R → ∞
  -- Pole at z=0: residue -1, half-residue contribution πi (indentation)
  -- Pole at z=2πi: residue -e^{2πiω}, half-residue contribution πi·e^{2πiω}
  --
  -- The Cauchy-Goursat theorem for rectangles (available in Mathlib as
  -- integral_boundary_rect_eq_zero_of_differentiableOn) applies to the
  -- region between the two horizontal lines, but the poles at z=0 and z=2πi
  -- require either indentation or the residue theorem for rectangles.
  --
  -- The residue theorem for rectangles (boundary integral = 2πi × sum of residues)
  -- is NOT directly available in Mathlib. The Cauchy-Goursat theorem only handles
  -- the zero-residue case (no poles inside). For a single simple pole, one can
  -- remove a small disk around the pole and apply Cauchy-Goursat to the punctured
  -- region, but this requires significant topological machinery.
  --
  -- Mid-solve lookup: psr_search "rectangular contour integral residue theorem
  -- boundary integral poles" returned no relevant patterns. memory_search with
  -- tags ["contour", "integral", "residue"] returned empty.
  --
  -- Closer hop 2 proved `integrand_one_sub_neg`, the exact reflection identity
  -- `f_{1-ω}(-x) = -f_ω(x)`.  Searches of the repository and Mathlib for a
  -- principal-value change-of-variables theorem, cotangent integral, beta
  -- integral, or rectangle residue theorem found no result that converts this
  -- symmetry into the required value.  The remaining bridge is still an
  -- analytic evaluation (via an indented contour, beta/reflection formula, or
  -- an equivalent principal-value theorem), rather than algebraic rewriting.
  sorry

end

-- #print axioms apm_a96J08
