import Mathlib
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Analytic.Polynomial
import ConstructionTargets.Rouche
import ConstructionTargets.SchwarzPick

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

/-- Every strict radial contraction of the disk self-map has an interior fixed
point.  This is the complete Rouché slice needed before passing to `t → 1`. -/
lemma apm_a94a09_exists_scaled_fixed_point
    {f : ℂ → ℂ}
    (hf_continuous : ContinuousOn f (closedBall 0 1))
    (hf_analytic : DifferentiableOn ℂ f (ball 0 1))
    (hf_boundary : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ z ∈ ball (0 : ℂ) 1, z = (t : ℂ) * f z := by
  let r : ℝ := (t + 1) / 2
  have htr : t < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hr0 : 0 < r := lt_of_le_of_lt ht0 htr
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 1 := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    exact mem_ball_zero_iff.mpr (hz.trans_lt hr1)
  have hfan : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r) := by
    intro z hz
    exact hf_analytic.analyticAt (isOpen_ball.mem_nhds (hsub hz))
  let g : ℂ → ℂ := fun z ↦ -(t : ℂ) * f z
  have hgan : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) r) := by
    exact analyticOnNhd_const.mul hfan
  have hmaps := apm_a94a09_mapsTo_closedBall
    hf_continuous hf_analytic hf_boundary
  have hdom : ∀ z ∈ sphere (0 : ℂ) r, ‖g z‖ < ‖z‖ := by
    intro z hz
    have hzr : ‖z‖ = r := by
      simpa [mem_sphere, dist_zero_right] using hz
    have hzclosed : z ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff, hzr]
      exact hr1.le
    have hfz : ‖f z‖ ≤ 1 := by
      simpa [mem_closedBall_zero_iff] using hmaps hzclosed
    have ht_norm : ‖(t : ℂ)‖ = t := by simp [abs_of_nonneg ht0]
    dsimp [g]
    rw [norm_mul, norm_neg, ht_norm, hzr]
    calc
      t * ‖f z‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hfz ht0
      _ < r := by simpa using htr
  obtain ⟨z, hz, hzero⟩ :=
    apm_a94a09_exists_zero_id_add_of_rouche hr0 hgan hdom
  refine ⟨z, hsub hz, ?_⟩
  simpa [g, sub_eq_add_neg] using eq_neg_of_add_eq_zero_left hzero

/-- Compactness passes the fixed points of the strict radial contractions to
an actual fixed point of `f` in the closed unit disk. -/
lemma apm_a94a09_exists_closedBall_fixed_point
    {f : ℂ → ℂ}
    (hf_continuous : ContinuousOn f (closedBall 0 1))
    (hf_analytic : DifferentiableOn ℂ f (ball 0 1))
    (hf_boundary : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ 1) :
    ∃ z ∈ closedBall (0 : ℂ) 1, f z = z := by
  let t : ℕ → ℝ := fun n ↦ (n : ℝ) / (n + 1)
  have ht0 (n : ℕ) : 0 ≤ t n := by positivity
  have ht1 (n : ℕ) : t n < 1 := by
    dsimp [t]
    rw [div_lt_one (by positivity : (0 : ℝ) < n + 1)]
    norm_num
  choose z hz hfix using fun n ↦
    apm_a94a09_exists_scaled_fixed_point hf_continuous hf_analytic hf_boundary
      (ht0 n) (ht1 n)
  have hzclosed (n : ℕ) : z n ∈ closedBall (0 : ℂ) 1 :=
    ball_subset_closedBall (hz n)
  obtain ⟨a, ha, phi, hphi, halim⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).tendsto_subseq hzclosed
  have hwithin : Tendsto (z ∘ phi) atTop (nhdsWithin a (closedBall 0 1)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨halim, Eventually.of_forall (fun n ↦ hzclosed (phi n))⟩
  have hflim : Tendsto (fun n ↦ f (z (phi n))) atTop (nhds (f a)) :=
    (hf_continuous a ha).tendsto.comp hwithin
  have htlim : Tendsto (t ∘ phi) atTop (nhds 1) :=
    (tendsto_natCast_div_add_atTop (1 : ℝ)).comp hphi.tendsto_atTop
  have hprodlim :
      Tendsto (fun n ↦ ((t (phi n) : ℝ) : ℂ) * f (z (phi n))) atTop
        (nhds ((1 : ℂ) * f a)) :=
    ((Complex.continuous_ofReal.tendsto 1).comp htlim).mul hflim
  have heqlim : Tendsto (z ∘ phi) atTop (nhds (f a)) := by
    simpa [Function.comp_apply] using hprodlim.congr'
      (Eventually.of_forall fun n ↦ (hfix (phi n)).symm)
  have hfa : f a = a := tendsto_nhds_unique heqlim halim
  exact ⟨a, ha, hfa⟩

theorem apm_a94a09
    {f : ℂ → ℂ}
    (hf_continuous : ContinuousOn f (closedBall 0 1))
    (hf_analytic : DifferentiableOn ℂ f (ball 0 1))
    (hf_boundary : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ 1)
    (hf_no_boundary_fixed_point : ∀ z ∈ sphere (0 : ℂ) 1, f z ≠ z) :
    ∃! z : ℂ, z ∈ ball 0 1 ∧ f z = z := by
  obtain ⟨z, hzclosed, hfix⟩ :=
    apm_a94a09_exists_closedBall_fixed_point
      hf_continuous hf_analytic hf_boundary
  have hzball : z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    have hzle : ‖z‖ ≤ 1 := by
      simpa [mem_closedBall_zero_iff] using hzclosed
    have hzne : ‖z‖ ≠ 1 := by
      intro hzone
      apply hf_no_boundary_fixed_point z
      · simpa [mem_sphere, dist_zero_right] using hzone
      · exact hfix
    exact lt_of_le_of_ne hzle hzne
  refine ⟨z, ⟨hzball, hfix⟩, ?_⟩
  intro w hw
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
  CLOSER HOP 4 (2026-08-10): the suggested shrink-radius strategy was
  followed and its existence half is now fully compiled.  The new lemma
  `apm_a94a09_exists_scaled_fixed_point` packages every strict Rouché slice:
  for `0 ≤ t < 1`, it chooses `r = (t+1)/2`, derives neighborhood
  analyticity on `closedBall 0 r`, proves strict domination on its boundary,
  and extracts a zero using the already-compiled divisor bridge.  The lemma
  `apm_a94a09_exists_closedBall_fixed_point` then takes
  `t n = n/(n+1)`, applies sequential compactness of the closed disk, and
  passes `z n = t n * f (z n)` to the limit using `ContinuousOn`.  The main
  proof above excludes a boundary limit with
  `hf_no_boundary_fixed_point`, so existence in the open disk is closed.

  The sole remaining obligation is uniqueness: given the fixed points `z`
  and `w` in the open unit disk, prove `w = z`.  The standard Schwarz--Pick
  argument conjugates `f` by
  `phi_z(u) = (u-z)/(1-conj(z)*u)`.  The conjugate fixes `0`; its second fixed
  point forces equality in Schwarz's lemma, hence it is the identity, and the
  original boundary hypothesis then gives a contradiction.  Mathlib and the
  corpus provide Schwarz's affine equality theorem but no unit-disk Möbius
  package or Schwarz--Pick fixed-point uniqueness theorem.  A targeted Zulip
  search for disk automorphisms/Schwarz--Pick/two fixed points was empty.
  Search arm (a), existing components, carried the compiled existence proof;
  arm (b) returned no uniqueness bridge.  No arXiv search was needed because
  the standard Schwarz--Pick route is known. The frozen statement is unchanged.
  -/
  have hclosedmap : MapsTo f (closedBall (0 : ℂ) 1) (closedBall 0 1) :=
    apm_a94a09_mapsTo_closedBall hf_continuous hf_analytic hf_boundary
  have hdiffcl : DiffContOnCl ℂ f (ball (0 : ℂ) 1) :=
    DiffContOnCl.mk_ball hf_analytic hf_continuous
  have hopenmap : MapsTo f (ball (0 : ℂ) 1) (ball 0 1) := by
    intro x hx
    rw [mem_ball_zero_iff]
    have hle : ‖f x‖ ≤ 1 := by
      have := hclosedmap (ball_subset_closedBall hx)
      simpa [mem_closedBall_zero_iff] using this
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hmax : IsMaxOn (norm ∘ f) (ball (0 : ℂ) 1) x := by
      intro y hy
      have hy_le : ‖f y‖ ≤ 1 := by
        have := hclosedmap (ball_subset_closedBall hy)
        simpa [mem_closedBall_zero_iff] using this
      simpa [Function.comp_apply, heq] using hy_le
    have hconst := Complex.eqOn_closure_of_isPreconnected_of_isMaxOn_norm
      isPreconnected_ball isOpen_ball hdiffcl hx hmax
    have hfxsphere : f x ∈ sphere (0 : ℂ) 1 := by
      simpa [mem_sphere, dist_zero_right] using heq
    have hfxclosure : f x ∈ closure (ball (0 : ℂ) 1) := by
      rw [closure_ball _ one_ne_zero]
      exact sphere_subset_closedBall hfxsphere
    apply hf_no_boundary_fixed_point (f x) hfxsphere
    simpa using hconst hfxclosure
  by_contra hwz
  have hid : EqOn f id (ball (0 : ℂ) 1) :=
    ConstructionTargets.SchwarzPick.eq_id_of_two_fixed_points
      hf_analytic hopenmap hzball hw.1 (Ne.symm hwz) hfix hw.2
  have hid_closed : EqOn f id (closedBall (0 : ℂ) 1) :=
    hid.of_subset_closure hf_continuous continuous_id.continuousOn
      ball_subset_closedBall (by rw [closure_ball _ one_ne_zero])
  have hone_sphere : (1 : ℂ) ∈ sphere (0 : ℂ) 1 := by
    simp
  exact hf_no_boundary_fixed_point 1 hone_sphere (hid_closed (sphere_subset_closedBall hone_sphere))


end
