import Mathlib

/-!
# APM a94A09

## Statement repairs

None.

## Encoding notes

A function whose source is the closed disk is represented by a function on `ℂ`,
with continuity required only on `closedBall 0 1` and analyticity only on
`ball 0 1`. The boundary `∂Δ` is `sphere 0 1`.
-/

open Complex Metric Set

noncomputable section

/-! ## Blocker analysis

This theorem (existence and uniqueness of a fixed point for a holomorphic
self-map of the disk with |f| ≤ 1 on ∂Δ and no boundary fixed points) is a
standard consequence of Rouché's theorem or the argument principle.

The standard proof (from informal-solution.md):
1. Fixed points of f are zeros of g(z) = z - f(z).
2. Use the homotopy h_t(z) = z - t·f(z) for t ∈ [0,1].
3. h_t has no zeros on ∂Δ for any t ∈ [0,1] (for t < 1: |t·f(z)| ≤ t < 1 = |z|;
   for t = 1: by hypothesis).
4. By the argument principle, the number of zeros of h_t in Δ is constant in t.
5. At t = 0: h_0(z) = z has exactly 1 zero in Δ.
6. At t = 1: h_1(z) = z - f(z) has exactly 1 zero = 1 fixed point.

**Mathlib infrastructure gap.** Mathlib (v4.29.0-rc8) does NOT have:
- Rouché's theorem
- The argument principle: `(1/2πi)∮ f'(z)/f(z) dz = number of zeros of f inside`
- Winding number computation for curves
- Brouwer fixed point theorem (even the topological version for the disk)
- A zero-counting lemma via contour integration

Available but insufficient:
- `Complex.circleIntegral_sub_inv_smul` (Cauchy integral formula) — computes
  `∮ f(z)/(z-w) dz`, not `∮ f'(z)/f(z) dz`.
- `Complex.circleIntegral_one_div_sub_center_pow_smul` (derivative formula) —
  same limitation.
- `CanonicalDecomposition` (Blaschke factors) — has the building blocks but no
  zero-counting application.
- `JensenFormula` — counts zeros via `circleAverage log ‖f‖`, not via `∮ f'/f`.

The statement is TRUE as stated. The blocker is a Mathlib infrastructure gap. -/

/-- The non-strict boundary estimate is sufficient to keep the full homotopy
`z - t f z` nonzero: strictness follows from `t < 1`, while the endpoint
`t = 1` is exactly the no-boundary-fixed-point hypothesis. -/
lemma apm_a94a09_homotopy_ne_zero
    {f : ℂ → ℂ}
    (hf_boundary : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ 1)
    (hf_no_boundary_fixed_point : ∀ z ∈ sphere (0 : ℂ) 1, f z ≠ z)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ z ∈ sphere (0 : ℂ) 1, z - (t : ℂ) * f z ≠ 0 := by
  intro z hz hzero
  have hznorm : ‖z‖ = 1 := by
    simpa [mem_sphere, dist_zero_right] using hz
  rcases ht.2.eq_or_lt with rfl | htlt
  · apply hf_no_boundary_fixed_point z hz
    simpa using (sub_eq_zero.mp hzero).symm
  · have hstrict : ‖(t : ℂ) * f z‖ < ‖z‖ := by
      simp only [norm_mul]
      simp [abs_of_nonneg ht.1, hznorm]
      calc
        t * ‖f z‖ ≤ t * 1 :=
          mul_le_mul_of_nonneg_left (hf_boundary z hz) ht.1
        _ < 1 := by simpa using htlt
    have heq : z = (t : ℂ) * f z := sub_eq_zero.mp hzero
    exact (ne_of_lt hstrict) (congrArg norm heq).symm

/-- The boundary estimate propagates to the whole closed disk by the maximum
modulus principle.  This is the disk-self-map input needed by any Schwarz
lemma treatment of uniqueness. -/
lemma apm_a94a09_mapsTo_closedBall
    {f : ℂ → ℂ}
    (hf_continuous : ContinuousOn f (closedBall 0 1))
    (hf_analytic : DifferentiableOn ℂ f (ball 0 1))
    (hf_boundary : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ 1) :
    MapsTo f (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
  intro z hz
  rw [mem_closedBall_zero_iff]
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      ⟨hf_analytic, by simpa [closure_ball] using hf_continuous⟩
  · simpa [frontier_ball] using hf_boundary
  · simpa [closure_ball] using hz

theorem apm_a94a09
    {f : ℂ → ℂ}
    (hf_continuous : ContinuousOn f (closedBall 0 1))
    (hf_analytic : DifferentiableOn ℂ f (ball 0 1))
    (hf_boundary : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ 1)
    (hf_no_boundary_fixed_point : ∀ z ∈ sphere (0 : ℂ) 1, f z ≠ z) :
    ∃! z : ℂ, z ∈ ball 0 1 ∧ f z = z := by
  /-
  Boundary (closer hop 1): the original infrastructure comment is now partly
  obsolete: the sorry-free module `ConstructionTargets.Rouche` proves an
  argument principle and strict Rouché zero-count transfer.  The compiled
  helper `apm_a94a09_homotopy_ne_zero` above closes the elementary non-strict
  boundary-homotopy step required by this problem.

  Two mismatches remain.  `zeroCountInClosedBall_add_eq` requires both summands
  to be `AnalyticOnNhd` on the *closed* disk and a strict boundary inequality.
  The frozen assumptions give only continuity on the closed disk and
  differentiability on the open disk, and allow `‖f z‖ = 1` on the boundary.
  Hence it cannot be applied directly to `id + (-f)`.  Applying it to
  `id + (-t f)` for `t < 1` still fails its closed-neighborhood analyticity
  hypothesis, and passing `t → 1` would additionally require zero persistence
  and multiplicity control.

  Closer hop 2 packages the maximum-modulus reduction as the compiled lemma
  `apm_a94a09_mapsTo_closedBall`: the frozen boundary estimate really does
  make `f` a self-map of the closed disk.  Mathlib's Schwarz file then gives
  metric contraction estimates and an affine equality case, but only after a
  fixed point has already been moved to the origin; it does not supply the
  disk automorphism conjugation or the endpoint existence theorem.

  Searches of `LEMMA-INDEX.md`, Mathlib's maximum-modulus, Schwarz, Hurwitz,
  divisor, and compactness APIs, prior artifacts `a92J05`, `a97A08`, and
  `a97J08`, `ConstructionTargets/`, and git history found no theorem extending
  the reusable zero count to `ContinuousOn closedBall` plus
  `DifferentiableOn ball`, nor a Hurwitz bridge proving existence and
  uniqueness at the endpoint.  Closure should generalize the argument
  principle to this disk-analytic boundary-continuous setting, or develop the
  shrink-radius/limit argument and then use Schwarz equality for uniqueness.

  CLOSER HOP 3: a route around the boundary-analyticity mismatch was checked
  in detail. For each `0 ≤ t < 1`, choose `r` with `t < r < 1`. The frozen
  `DifferentiableOn` hypothesis does give `AnalyticOnNhd` on
  `closedBall 0 r`, and on `sphere 0 r` one has
  `‖t • f z‖ ≤ t < r = ‖z‖`; hence
  `ConstructionTargets.Rouche.zeroCountInClosedBall_add_eq` applies to
  `z - t * f z`. Taking `t → 1` and compactness of the closed disk would then
  produce an endpoint fixed point. This avoids generalizing the argument
  principle to boundary-continuous functions.

  The existing Rouché module nevertheless stops at equality of integer-valued
  divisor sums: it has no exported computation of the identity map's disk
  zero count and no lemma extracting an actual zero from a nonzero count.
  Source inspection of `CanonicalDecomposition` found the factorization
  ingredients but no such bridge. A separate search for disk automorphisms
  found only upper-half-plane Möbius actions; uniqueness would still require
  locally proving that `(z-a)/(1-conj(a)z)` preserves the disk and conjugating
  the two-fixed-point map before applying Schwarz equality. Thus the
  shrink-radius strategy is now precise, but these divisor-existence and
  Möbius-packaging prerequisites remain open; the statement is unchanged.
  -/
  sorry


end
