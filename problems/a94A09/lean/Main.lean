import Mathlib
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Analytic.Polynomial
import ConstructionTargets.Rouche

/-!
# APM a94A09

## Statement repairs

None.

## Encoding notes

A function whose source is the closed disk is represented by a function on `ℂ`,
with continuity required only on `closedBall 0 1` and analyticity only on
`ball 0 1`. The boundary `∂Δ` is `sphere 0 1`.
-/

open Complex Filter MeromorphicOn Metric Polynomial Set

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

/-- A monic polynomial's divisor count is its multiset root count in the
closed ball.  This is the polynomial normalization missing from the exported
Rouché API; the proof is adapted from the compiled local bridge in `a92J05`. -/
lemma apm_a94a09_zeroCount_aeval_eq_card_filter
    (q : ℂ[X]) (hq : q.Monic) (c : ℂ) (R : ℝ) :
    ConstructionTargets.Rouche.zeroCountInClosedBall (fun z ↦ aeval z q) c R =
      (q.roots.filter (fun z ↦ dist z c ≤ R)).card := by
  classical
  let D : Function.locallyFinsupp ℂ ℤ :=
    { toFun := fun z ↦ q.roots.count z
      supportWithinDomain' := fun _ _ ↦ Set.mem_univ _
      supportLocallyFiniteWithinDomain' := by
        intro z _
        refine ⟨Set.univ, Filter.univ_mem, ?_⟩
        apply q.roots.toFinset.finite_toSet.subset
        intro x hx
        simp only [Set.mem_inter_iff, mem_univ, true_and, Function.mem_support,
          ne_eq] at hx
        apply Multiset.mem_toFinset.mpr
        apply Multiset.count_pos.mp
        have : q.roots.count x ≠ 0 := by exact_mod_cast hx
        omega }
  have hD : D.support.Finite := by
    apply q.roots.toFinset.finite_toSet.subset
    intro x hx
    apply Multiset.mem_toFinset.mpr
    apply Multiset.count_pos.mp
    have : q.roots.count x ≠ 0 := by
      change (q.roots.count x : ℤ) ≠ 0 at hx
      exact_mod_cast hx
    omega
  have hfactor : (fun z ↦ aeval z q) = ∏ᶠ u, (· - u) ^ D u := by
    funext z
    change q.eval z = _
    rw [(IsAlgClosed.splits q).eval_eq_prod_roots_of_monic hq]
    rw [Finset.prod_multiset_map_count]
    rw [finprod_eq_prod_of_mulSupport_subset (s := q.roots.toFinset)]
    simp only [Finset.prod_apply]
    · apply Finset.prod_congr rfl
      intro u hu
      change (z - u) ^ q.roots.count u = (z - u) ^ (q.roots.count u : ℤ)
      simp
    · intro u hu
      simp only [Function.FactorizedRational.mulSupport, Function.mem_support] at hu
      apply Multiset.mem_toFinset.mpr
      apply Multiset.count_pos.mp
      have : q.roots.count u ≠ 0 := by
        change (q.roots.count u : ℤ) ≠ 0 at hu
        exact_mod_cast hu
      omega
  unfold ConstructionTargets.Rouche.zeroCountInClosedBall
  rw [hfactor]
  have hmer : MeromorphicOn (∏ᶠ u, (· - u) ^ D u) Set.univ :=
    (Function.FactorizedRational.meromorphicNFOn D Set.univ).meromorphicOn
  rw [← hmer.divisor_restrict (show closedBall c R ⊆ Set.univ from subset_univ _),
    Function.FactorizedRational.divisor hD]
  rw [finsum_eq_sum_of_support_subset (s := q.roots.toFinset)]
  · have hcount :
        (∑ z ∈ q.roots.toFinset, if dist z c ≤ R then q.roots.count z else 0) =
          (q.roots.filter (fun z ↦ dist z c ≤ R)).card := by
      calc
        _ = ∑ z ∈ q.roots.toFinset,
              q.roots.count z * (if dist z c ≤ R then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro z _
            split <;> simp_all
        _ = (q.roots.map fun z ↦ if dist z c ≤ R then 1 else 0).sum :=
          Finset.sum_multiset_map_count q.roots _ |>.symm
        _ = _ := by
          induction q.roots using Multiset.induction_on with
          | empty => simp
          | cons a s ih =>
              by_cases ha : dist a c ≤ R <;> simp [ha, ih, Nat.add_comm]
    simp only [Function.locallyFinsuppWithin.restrict_apply]
    change (∑ z ∈ q.roots.toFinset,
      if dist z c ≤ R then (q.roots.count z : ℤ) else 0) = _
    exact_mod_cast hcount
  · intro z hz
    simp only [Function.mem_support] at hz
    by_contra hzroot
    have hznot : z ∉ q.roots := fun hm => hzroot (Multiset.mem_toFinset.mpr hm)
    have hzcount : q.roots.count z = 0 := Multiset.count_eq_zero.mpr hznot
    simp only [Function.locallyFinsuppWithin.restrict_apply] at hz
    change (if z ∈ closedBall c R then (q.roots.count z : ℤ) else 0) ≠ 0 at hz
    simp [hzcount] at hz

/-- The identity map has exactly one zero in every positive-radius disk
centered at zero. -/
lemma apm_a94a09_zeroCount_id {R : ℝ} (hR : 0 < R) :
    ConstructionTargets.Rouche.zeroCountInClosedBall (fun z : ℂ ↦ z) 0 R = 1 := by
  have h := apm_a94a09_zeroCount_aeval_eq_card_filter (Polynomial.X : ℂ[X])
    Polynomial.monic_X 0 R
  have h' : ConstructionTargets.Rouche.zeroCountInClosedBall (fun z : ℂ ↦ z) 0 R =
      ((Polynomial.X : ℂ[X]).roots.filter (fun z ↦ dist z 0 ≤ R)).card := by
    simpa only [aeval_X] using h
  rw [h']
  simp only [Polynomial.roots_X, Multiset.filter_singleton, dist_zero_right,
    norm_zero, hR.le, if_true, Multiset.card_singleton, Nat.cast_one]

/-- A nonzero divisor count for an analytic function forces an actual zero in
the closed ball.  This supplies the logical extraction step absent from the
exported Rouché API. -/
lemma apm_a94a09_exists_zero_of_zeroCount_ne_zero
    {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (closedBall c R))
    (hcount : ConstructionTargets.Rouche.zeroCountInClosedBall F c R ≠ 0) :
    ∃ z ∈ closedBall c R, F z = 0 := by
  by_contra hzero
  push_neg at hzero
  have hdiv : divisor F (closedBall c R) = 0 := by
    ext z
    by_cases hz : z ∈ closedBall c R
    · rw [divisor_apply hF.meromorphicOn hz]
      have hord : meromorphicOrderAt F z = 0 :=
        (hF z hz).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hzero z hz)
      simp [hord]
    · simp [divisor_def, hz]
  apply hcount
  unfold ConstructionTargets.Rouche.zeroCountInClosedBall
  rw [hdiv]
  simp

/-- The two bridge lemmas turn the exported Rouché count equality into the
usual existence conclusion when the dominant function is the identity. -/
lemma apm_a94a09_exists_zero_id_add_of_rouche
    {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hdom : ∀ z ∈ sphere (0 : ℂ) R, ‖g z‖ < ‖z‖) :
    ∃ z ∈ closedBall (0 : ℂ) R, z + g z = 0 := by
  let F : ℂ → ℂ := fun z ↦ z
  have hF : AnalyticOnNhd ℂ F (closedBall 0 R) := analyticOnNhd_id
  have htransfer := ConstructionTargets.Rouche.zeroCountInClosedBall_add_eq
    hR hF hg hdom
  have hcount : ConstructionTargets.Rouche.zeroCountInClosedBall (F + g) 0 R ≠ 0 := by
    rw [htransfer, apm_a94a09_zeroCount_id hR]
    norm_num
  simpa [F, Pi.add_apply] using
    (apm_a94a09_exists_zero_of_zeroCount_ne_zero (hF.add hg) hcount)

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
