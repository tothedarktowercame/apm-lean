import Mathlib

open MeasureTheory

/-!
# APM t00A05 — a closed angle form and two periods

## Statement repairs

1. The final absolute-value bar in the TeX display is a typographical
   delimiter; the intended error-free claims are the exterior derivative and
   two integrals.
2. The parametrization of `C₂` is required to be injective on the half-open
   period `[0, 2π)`.  This expresses the source's single traversal of the
   oriented intersection while retaining the closed endpoint equation, and
   excludes multiply-traversed parametrizations whose periods are multiplied.

## Encoding note

A one-form on the coordinate domain is represented by its three coefficient
functions, and its line integral is the integral of evaluation on the curve's
velocity.  `C₂` is retained through its two defining equations and its stated
counterclockwise orientation; injectivity on the half-open period records that
the geometric component is traversed exactly once.
-/

def apm_t00a05_U := {p : ℝ × ℝ × ℝ // p.1 ≠ 0 ∨ p.2.1 ≠ 0}

noncomputable def apm_t00a05_omega (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.2.1 / (p.1 ^ 2 + p.2.1 ^ 2),
    -p.1 / (p.1 ^ 2 + p.2.1 ^ 2), Real.cos p.2.2)

noncomputable def apm_t00a05_dOmega (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (deriv (fun x => (apm_t00a05_omega (x, p.2.1, p.2.2)).2.1) p.1 -
      deriv (fun y => (apm_t00a05_omega (p.1, y, p.2.2)).1) p.2.1,
   deriv (fun x => (apm_t00a05_omega (x, p.2.1, p.2.2)).2.2) p.1 -
      deriv (fun z => (apm_t00a05_omega (p.1, p.2.1, z)).1) p.2.2,
   deriv (fun y => (apm_t00a05_omega (p.1, y, p.2.2)).2.2) p.2.1 -
      deriv (fun z => (apm_t00a05_omega (p.1, p.2.1, z)).2.1) p.2.2)

noncomputable def apm_t00a05_lineIntegral
    (γ : ℝ → ℝ × ℝ × ℝ) (a b : ℝ) : ℝ :=
  ∫ t in Set.Icc a b,
    let v := apm_t00a05_omega (γ t)
    v.1 * deriv (fun s => (γ s).1) t +
      v.2.1 * deriv (fun s => (γ s).2.1) t +
      v.2.2 * deriv (fun s => (γ s).2.2) t

noncomputable def apm_t00a05_C1 (t : ℝ) : ℝ × ℝ × ℝ :=
  (Real.cos t, Real.sin t, 0)

def apm_t00a05_IsC2 (γ : ℝ → ℝ × ℝ × ℝ) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = γ (2 * Real.pi) ∧
  Set.InjOn γ (Set.Ico (0 : ℝ) (2 * Real.pi)) ∧
  (∀ t, 0 ≤ t → t ≤ 2 * Real.pi →
    2 * (γ t).1 ^ 2 + (γ t).2.1 ^ 2 + (γ t).2.2 ^ 2 = 10 ∧
    (γ t).2.2 = Real.exp ((γ t).2.1 - (γ t).1)) ∧
  0 < ∫ t in Set.Icc (0 : ℝ) (2 * Real.pi),
    (γ t).1 * deriv (fun s => (γ s).2.1) t -
      (γ t).2.1 * deriv (fun s => (γ s).1) t

noncomputable def apm_t00a05_level (q : ℝ × ℝ) : ℝ :=
  2 * q.1 ^ 2 + q.2 ^ 2 + Real.exp (q.2 - q.1) ^ 2

def apm_t00a05_region : Set (ℝ × ℝ) :=
  {q | apm_t00a05_level q ≤ 10}

lemma apm_t00a05_level_convexOn :
    ConvexOn ℝ Set.univ apm_t00a05_level := by
  let px : ℝ × ℝ →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ
  let py : ℝ × ℝ →ₗ[ℝ] ℝ := LinearMap.snd ℝ ℝ ℝ
  have hsq : ConvexOn ℝ Set.univ (fun x : ℝ ↦ x ^ 2) :=
    (show Even 2 by decide).convexOn_pow
  have hx := hsq.comp_linearMap px
  have hy := hsq.comp_linearMap py
  have he := convexOn_exp.comp_linearMap (2 • (py - px))
  have hsum := (hx.smul (show (0 : ℝ) ≤ 2 by norm_num)).add hy |>.add he
  convert hsum using 1
  funext q
  simp [apm_t00a05_level, px, py, Function.comp_apply, pow_two, ← Real.exp_add]
  ring_nf

lemma apm_t00a05_region_convex : Convex ℝ apm_t00a05_region := by
  simpa [apm_t00a05_region] using apm_t00a05_level_convexOn.convex_le 10

lemma apm_t00a05_level_origin : apm_t00a05_level (0, 0) < 10 := by
  norm_num [apm_t00a05_level]

lemma apm_t00a05_origin_mem_region : (0, 0) ∈ apm_t00a05_region := by
  exact apm_t00a05_level_origin.le

lemma apm_t00a05_level_continuous : Continuous apm_t00a05_level := by
  unfold apm_t00a05_level
  fun_prop

lemma apm_t00a05_region_isClosed : IsClosed apm_t00a05_region := by
  exact isClosed_le apm_t00a05_level_continuous continuous_const

lemma apm_t00a05_origin_mem_interior_region :
    (0, 0) ∈ interior apm_t00a05_region := by
  have hopen : IsOpen {q : ℝ × ℝ | apm_t00a05_level q < 10} :=
    isOpen_lt apm_t00a05_level_continuous continuous_const
  exact (interior_maximal (by
    intro q hq
    simpa [apm_t00a05_region] using hq.le) hopen) apm_t00a05_level_origin

lemma apm_t00a05_region_isBounded : Bornology.IsBounded apm_t00a05_region := by
  apply (Metric.isBounded_Icc (-10 : ℝ) 10).prod
    (Metric.isBounded_Icc (-10 : ℝ) 10) |>.subset
  intro q hq
  change 2 * q.1 ^ 2 + q.2 ^ 2 + Real.exp (q.2 - q.1) ^ 2 ≤ 10 at hq
  constructor <;> constructor <;>
    nlinarith [sq_nonneg q.1, sq_nonneg q.2,
      sq_nonneg (Real.exp (q.2 - q.1))]

lemma apm_t00a05_region_isCompact : IsCompact apm_t00a05_region := by
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨apm_t00a05_region_isClosed, apm_t00a05_region_isBounded⟩

lemma apm_t00a05_region_frontier_homeomorphic_sphere :
    ∃ h : (ℝ × ℝ) ≃ₜ (ℝ × ℝ),
      h '' interior apm_t00a05_region = Metric.ball 0 1 ∧
      h '' closure apm_t00a05_region = Metric.closedBall 0 1 ∧
      h '' frontier apm_t00a05_region = Metric.sphere 0 1 := by
  exact exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    apm_t00a05_region_convex
    ⟨(0, 0), apm_t00a05_origin_mem_interior_region⟩
    apm_t00a05_region_isBounded

lemma apm_t00a05_level_radial_convexOn (q : ℝ × ℝ) :
    ConvexOn ℝ Set.univ (fun t : ℝ ↦ apm_t00a05_level (t • q)) := by
  let ray : ℝ →ₗ[ℝ] ℝ × ℝ := LinearMap.toSpanSingleton ℝ (ℝ × ℝ) q
  simpa [ray, Function.comp_def] using
    apm_t00a05_level_convexOn.comp_linearMap ray

lemma apm_t00a05_level_radial_strictMonoOn {q : ℝ × ℝ}
    (hq : apm_t00a05_level q = 10) :
    StrictMonoOn (fun t : ℝ ↦ apm_t00a05_level (t • q)) (Set.Ici 1) := by
  have hmono := (apm_t00a05_level_radial_convexOn q).strictMonoOn
    (Set.mem_univ 0) (show (0 : ℝ) < 1 by norm_num) (by
      simpa [hq] using apm_t00a05_level_origin)
  simpa only [Set.univ_inter] using hmono

lemma apm_t00a05_level_gt_of_one_lt_smul {q : ℝ × ℝ}
    (hq : apm_t00a05_level q = 10) {t : ℝ} (ht : 1 < t) :
    10 < apm_t00a05_level (t • q) := by
  rw [← hq]
  simpa using apm_t00a05_level_radial_strictMonoOn hq
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht.le) ht

lemma apm_t00a05_level_eq_ten_mem_frontier {q : ℝ × ℝ}
    (hq : apm_t00a05_level q = 10) : q ∈ frontier apm_t00a05_region := by
  have hqmem : q ∈ apm_t00a05_region := by
    simpa [apm_t00a05_region, hq]
  rw [mem_frontier_iff_notMem_interior hqmem]
  intro hqint
  have hray : Continuous (fun t : ℝ ↦ t • q) := by fun_prop
  have hopen : IsOpen ((fun t : ℝ ↦ t • q) ⁻¹' interior apm_t00a05_region) :=
    isOpen_interior.preimage hray
  have h1 : (1 : ℝ) ∈ (fun t : ℝ ↦ t • q) ⁻¹' interior apm_t00a05_region := by
    simpa using hqint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 1 h1
  let t : ℝ := 1 + ε / 2
  have ht : 1 < t := by dsimp [t]; linarith
  have htball : t ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [t]
    rw [abs_of_nonneg] <;> linarith
  have htmem : t • q ∈ apm_t00a05_region :=
    interior_subset (hball htball)
  have htle : apm_t00a05_level (t • q) ≤ 10 := htmem
  exact (not_lt_of_ge htle) (apm_t00a05_level_gt_of_one_lt_smul hq ht)

lemma apm_t00a05_mem_frontier_level_eq_ten {q : ℝ × ℝ}
    (hq : q ∈ frontier apm_t00a05_region) : apm_t00a05_level q = 10 := by
  have hqmem : q ∈ apm_t00a05_region := by
    have : q ∈ closure apm_t00a05_region := frontier_subset_closure hq
    simpa [apm_t00a05_region_isClosed.closure_eq] using this
  have hle : apm_t00a05_level q ≤ 10 := hqmem
  apply le_antisymm hle
  by_contra hnle
  have hlt : apm_t00a05_level q < 10 := lt_of_not_ge hnle
  have hopen : IsOpen {r : ℝ × ℝ | apm_t00a05_level r < 10} :=
    isOpen_lt apm_t00a05_level_continuous continuous_const
  have hqint : q ∈ interior apm_t00a05_region :=
    (interior_maximal (by
      intro r hr
      simpa [apm_t00a05_region] using hr.le) hopen) hlt
  exact (mem_frontier_iff_notMem_interior hqmem).mp hq hqint

lemma apm_t00a05_level_set_eq_frontier :
    {q : ℝ × ℝ | apm_t00a05_level q = 10} =
      frontier apm_t00a05_region := by
  ext q
  exact ⟨apm_t00a05_level_eq_ten_mem_frontier,
    apm_t00a05_mem_frontier_level_eq_ten⟩

lemma apm_t00a05_region_mem_nhds_zero : apm_t00a05_region ∈ nhds (0, 0) := by
  exact Filter.mem_of_superset
    (isOpen_interior.mem_nhds apm_t00a05_origin_mem_interior_region)
    interior_subset

noncomputable def apm_t00a05_radialHomeomorph :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  gaugeRescaleHomeomorph apm_t00a05_region (Metric.ball 0 1)
    apm_t00a05_region_convex apm_t00a05_region_mem_nhds_zero
    (NormedSpace.isVonNBounded_of_isBounded ℝ apm_t00a05_region_isBounded)
    (convex_ball 0 1) (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))
    (NormedSpace.isVonNBounded_ball ℝ (ℝ × ℝ) 1)

lemma apm_t00a05_radialHomeomorph_apply (q : ℝ × ℝ) :
    apm_t00a05_radialHomeomorph q =
      (gauge apm_t00a05_region q / gauge (Metric.ball (0 : ℝ × ℝ) 1) q) • q :=
  rfl

lemma apm_t00a05_radialHomeomorph_smul {c : ℝ} (hc : 0 ≤ c)
    (q : ℝ × ℝ) :
    apm_t00a05_radialHomeomorph (c • q) =
      c • apm_t00a05_radialHomeomorph q := by
  exact gaugeRescale_smul apm_t00a05_region (Metric.ball 0 1) hc q

lemma apm_t00a05_radialHomeomorph_image_frontier :
    apm_t00a05_radialHomeomorph '' frontier apm_t00a05_region =
      Metric.sphere 0 1 := by
  rw [Homeomorph.image_frontier]
  have himage : apm_t00a05_radialHomeomorph '' apm_t00a05_region =
      Metric.closedBall 0 1 := by
    change gaugeRescaleHomeomorph apm_t00a05_region (Metric.ball 0 1)
      apm_t00a05_region_convex apm_t00a05_region_mem_nhds_zero
      (NormedSpace.isVonNBounded_of_isBounded ℝ apm_t00a05_region_isBounded)
      (convex_ball 0 1)
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))
      (NormedSpace.isVonNBounded_ball ℝ (ℝ × ℝ) 1) ''
        apm_t00a05_region = _
    have hclose := image_gaugeRescaleHomeomorph_closure
      apm_t00a05_region_convex apm_t00a05_region_mem_nhds_zero
      (NormedSpace.isVonNBounded_of_isBounded ℝ apm_t00a05_region_isBounded)
      (convex_ball 0 1)
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))
      (NormedSpace.isVonNBounded_ball ℝ (ℝ × ℝ) 1)
    simpa [apm_t00a05_region_isClosed.closure_eq, closure_ball] using hclose
  rw [himage, frontier_closedBall]
  norm_num

noncomputable def apm_t00a05_squarePerimeter (q : ℝ × ℝ) : ℝ :=
  if q.2 = -1 then q.1 + 1
  else if q.1 = 1 then q.2 + 3
  else if q.2 = 1 then 5 - q.1
  else 7 - q.2

lemma apm_t00a05_mem_supSphere_iff (q : ℝ × ℝ) :
    q ∈ Metric.sphere 0 1 ↔ max |q.1| |q.2| = 1 := by
  simp [Metric.mem_sphere, Real.dist_eq, Prod.norm_def]

lemma apm_t00a05_supSphere_coordinate_bounds {q : ℝ × ℝ}
    (hq : q ∈ Metric.sphere 0 1) :
    -1 ≤ q.1 ∧ q.1 ≤ 1 ∧ -1 ≤ q.2 ∧ q.2 ≤ 1 := by
  have hmax := (apm_t00a05_mem_supSphere_iff q).mp hq
  have hx : |q.1| ≤ 1 := by rw [← hmax]; exact le_max_left _ _
  have hy : |q.2| ≤ 1 := by rw [← hmax]; exact le_max_right _ _
  constructor
  · exact (abs_le.mp hx).1
  constructor
  · exact (abs_le.mp hx).2
  · exact ⟨(abs_le.mp hy).1, (abs_le.mp hy).2⟩

lemma apm_t00a05_supSphere_on_edge {q : ℝ × ℝ}
    (hq : q ∈ Metric.sphere 0 1) :
    q.1 = -1 ∨ q.1 = 1 ∨ q.2 = -1 ∨ q.2 = 1 := by
  have hmax := (apm_t00a05_mem_supSphere_iff q).mp hq
  rcases max_choice |q.1| |q.2| with h | h
  · have hx : |q.1| = 1 := by rw [h] at hmax; exact hmax
    rcases (abs_eq (by norm_num : (1 : ℝ) ≥ 0)).mp hx with hx | hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inl hx
  · have hy : |q.2| = 1 := by rw [h] at hmax; exact hmax
    rcases (abs_eq (by norm_num : (1 : ℝ) ≥ 0)).mp hy with hy | hy
    · exact Or.inr (Or.inr (Or.inr hy))
    · exact Or.inr (Or.inr (Or.inl hy))

lemma apm_t00a05_supSphere_open_edge_of_not_corner {q : ℝ × ℝ}
    (hq : q ∈ Metric.sphere (0 : ℝ × ℝ) 1)
    (hcorners : q ≠ (1, -1) ∧ q ≠ (1, 1) ∧
      q ≠ (-1, 1) ∧ q ≠ (-1, -1)) :
    (q.2 = -1 ∧ -1 < q.1 ∧ q.1 < 1) ∨
    (q.1 = 1 ∧ -1 < q.2 ∧ q.2 < 1) ∨
    (q.2 = 1 ∧ -1 < q.1 ∧ q.1 < 1) ∨
    (q.1 = -1 ∧ -1 < q.2 ∧ q.2 < 1) := by
  rcases apm_t00a05_supSphere_coordinate_bounds hq with ⟨hx0, hx1, hy0, hy1⟩
  rcases apm_t00a05_supSphere_on_edge hq with hx | hx | hy | hy
  · right; right; right
    refine ⟨hx, lt_of_le_of_ne hy0 ?_, lt_of_le_of_ne hy1 ?_⟩
    · intro heq
      apply hcorners.2.2.2
      exact Prod.ext hx heq.symm
    · intro heq
      apply hcorners.2.2.1
      exact Prod.ext hx heq
  · right; left
    refine ⟨hx, lt_of_le_of_ne hy0 ?_, lt_of_le_of_ne hy1 ?_⟩
    · intro heq
      apply hcorners.1
      exact Prod.ext hx heq.symm
    · intro heq
      apply hcorners.2.1
      exact Prod.ext hx heq
  · left
    refine ⟨hy, lt_of_le_of_ne hx0 ?_, lt_of_le_of_ne hx1 ?_⟩
    · intro heq
      apply hcorners.2.2.2
      exact Prod.ext heq.symm hy
    · intro heq
      apply hcorners.1
      exact Prod.ext heq hy
  · right; right; left
    refine ⟨hy, lt_of_le_of_ne hx0 ?_, lt_of_le_of_ne hx1 ?_⟩
    · intro heq
      apply hcorners.2.2.1
      exact Prod.ext heq.symm hy
    · intro heq
      apply hcorners.2.1
      exact Prod.ext heq hy

lemma apm_t00a05_squarePerimeter_bottom {q : ℝ × ℝ} (h : q.2 = -1) :
    apm_t00a05_squarePerimeter q = q.1 + 1 := by
  simp [apm_t00a05_squarePerimeter, h]

lemma apm_t00a05_squarePerimeter_right {q : ℝ × ℝ}
    (hy : q.2 ≠ -1) (hx : q.1 = 1) :
    apm_t00a05_squarePerimeter q = q.2 + 3 := by
  simp [apm_t00a05_squarePerimeter, hy, hx]

lemma apm_t00a05_squarePerimeter_top {q : ℝ × ℝ}
    (hyneg : q.2 ≠ -1) (hx : q.1 ≠ 1) (hy : q.2 = 1) :
    apm_t00a05_squarePerimeter q = 5 - q.1 := by
  norm_num [apm_t00a05_squarePerimeter, hyneg, hx, hy]

lemma apm_t00a05_squarePerimeter_left {q : ℝ × ℝ}
    (hyneg : q.2 ≠ -1) (hx : q.1 ≠ 1) (hy : q.2 ≠ 1) :
    apm_t00a05_squarePerimeter q = 7 - q.2 := by
  simp [apm_t00a05_squarePerimeter, hyneg, hx, hy]

lemma apm_t00a05_squarePerimeter_corners :
    apm_t00a05_squarePerimeter ((-1, -1) : ℝ × ℝ) = 0 ∧
    apm_t00a05_squarePerimeter ((1, -1) : ℝ × ℝ) = 2 ∧
    apm_t00a05_squarePerimeter ((1, 1) : ℝ × ℝ) = 4 ∧
    apm_t00a05_squarePerimeter ((-1, 1) : ℝ × ℝ) = 6 := by
  norm_num [apm_t00a05_squarePerimeter]

lemma apm_t00a05_squarePerimeter_mem_Icc {q : ℝ × ℝ}
    (hq : q ∈ Metric.sphere 0 1) :
    apm_t00a05_squarePerimeter q ∈ Set.Icc (0 : ℝ) 8 := by
  rcases apm_t00a05_supSphere_coordinate_bounds hq with ⟨hx0, hx1, hy0, hy1⟩
  unfold apm_t00a05_squarePerimeter
  split_ifs <;> constructor <;> linarith

noncomputable def apm_t00a05_squareOfPerimeter (s : ℝ) : ℝ × ℝ :=
  if s ≤ 2 then (s - 1, -1)
  else if s ≤ 4 then (1, s - 3)
  else if s ≤ 6 then (5 - s, 1)
  else (-1, 7 - s)

/-- A continuous unwrapped polar angle along one counterclockwise traversal
of the square perimeter.  Its endpoint increase is exactly `2π`. -/
noncomputable def apm_t00a05_squareAngle (s : ℝ) : ℝ :=
  if s ≤ 2 then Real.arctan (s - 1) + 3 * Real.pi / 2
  else if s ≤ 4 then Real.arctan (s - 3) + 2 * Real.pi
  else if s ≤ 6 then -Real.arctan (5 - s) + 5 * Real.pi / 2
  else Real.arctan (s - 7) + 3 * Real.pi

lemma apm_t00a05_squareAngle_continuous :
    Continuous apm_t00a05_squareAngle := by
  unfold apm_t00a05_squareAngle
  have h6 : Continuous (fun s : ℝ =>
      if s ≤ 6 then -Real.arctan (5 - s) + 5 * Real.pi / 2
      else Real.arctan (s - 7) + 3 * Real.pi) := by
    apply continuous_if_le (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop)
    intro x hx
    subst x
    norm_num [Real.arctan_neg, Real.arctan_one]
    ring
  have h4 : Continuous (fun s : ℝ =>
      if s ≤ 4 then Real.arctan (s - 3) + 2 * Real.pi
      else if s ≤ 6 then -Real.arctan (5 - s) + 5 * Real.pi / 2
      else Real.arctan (s - 7) + 3 * Real.pi) := by
    apply continuous_if_le (by fun_prop) (by fun_prop)
        (by fun_prop) h6.continuousOn
    intro x hx
    subst x
    norm_num [Real.arctan_neg, Real.arctan_one]
    ring
  apply continuous_if_le (by fun_prop) (by fun_prop)
      (by fun_prop) h4.continuousOn
  intro x hx
  subst x
  norm_num [Real.arctan_neg, Real.arctan_one]
  ring

lemma apm_t00a05_squareAngle_endpoints :
    apm_t00a05_squareAngle 8 - apm_t00a05_squareAngle 0 =
      2 * Real.pi := by
  norm_num [apm_t00a05_squareAngle, Real.arctan_neg, Real.arctan_one]
  ring

/-- The genuinely unwrapped angle after cutting the square perimeter at `β`.
Unlike the direct periodic composite, the second branch carries the explicit
`2π` seam correction. -/
noncomputable def apm_t00a05_squareAngleFrom (β u : ℝ) : ℝ :=
  if u ≤ 8 - β then apm_t00a05_squareAngle (u + β)
  else apm_t00a05_squareAngle (u + β - 8) + 2 * Real.pi

lemma apm_t00a05_squareAngleFrom_continuous (β : ℝ) :
    Continuous (apm_t00a05_squareAngleFrom β) := by
  unfold apm_t00a05_squareAngleFrom
  apply continuous_if_le (by fun_prop) (by fun_prop)
      (show Continuous (fun u : ℝ => apm_t00a05_squareAngle (u + β)) by
        simpa [Function.comp_def] using
          apm_t00a05_squareAngle_continuous.comp
            (continuous_id.add continuous_const)).continuousOn
      (show Continuous (fun u : ℝ =>
          apm_t00a05_squareAngle (u + β - 8) + 2 * Real.pi) by
        exact (by
          simpa [Function.comp_def] using
            (apm_t00a05_squareAngle_continuous.comp
              ((continuous_id.add continuous_const).sub continuous_const)).add
                continuous_const)).continuousOn
  intro x hx
  subst x
  have hend := apm_t00a05_squareAngle_endpoints
  convert (show apm_t00a05_squareAngle 8 =
      apm_t00a05_squareAngle 0 + 2 * Real.pi by linarith) using 1 <;> ring

lemma apm_t00a05_squareAngle_strictMonoOn :
    StrictMonoOn apm_t00a05_squareAngle (Set.Icc (0 : ℝ) 8) := by
  have heq24 {s : ℝ} (hs : s ∈ Set.Icc (2 : ℝ) 4) :
      apm_t00a05_squareAngle s = Real.arctan (s - 3) + 2 * Real.pi := by
    by_cases hs2 : s = 2
    · subst s
      norm_num [apm_t00a05_squareAngle, Real.arctan_neg, Real.arctan_one]
      ring
    · simp [apm_t00a05_squareAngle, not_le.mpr (lt_of_le_of_ne hs.1 (Ne.symm hs2)), hs.2]
  have heq46 {s : ℝ} (hs : s ∈ Set.Icc (4 : ℝ) 6) :
      apm_t00a05_squareAngle s =
        -Real.arctan (5 - s) + 5 * Real.pi / 2 := by
    by_cases hs4 : s = 4
    · subst s
      norm_num [apm_t00a05_squareAngle, Real.arctan_one]
      ring
    · have h4s : 4 < s := lt_of_le_of_ne hs.1 (Ne.symm hs4)
      simp [apm_t00a05_squareAngle, not_le.mpr (by linarith : 2 < s),
        not_le.mpr h4s, hs.2]
  have heq68 {s : ℝ} (hs : s ∈ Set.Icc (6 : ℝ) 8) :
      apm_t00a05_squareAngle s = Real.arctan (s - 7) + 3 * Real.pi := by
    by_cases hs6 : s = 6
    · subst s
      norm_num [apm_t00a05_squareAngle, Real.arctan_neg, Real.arctan_one]
      ring
    · have h6s : 6 < s := lt_of_le_of_ne hs.1 (Ne.symm hs6)
      simp [apm_t00a05_squareAngle, not_le.mpr (by linarith : 2 < s),
        not_le.mpr (by linarith : 4 < s), not_le.mpr h6s]
  have h02 : StrictMonoOn apm_t00a05_squareAngle (Set.Icc (0 : ℝ) 2) := by
    intro x hx y hy hxy
    simp only [apm_t00a05_squareAngle, if_pos hx.2, if_pos hy.2]
    have := Real.arctan_strictMono (sub_lt_sub_right hxy 1)
    linarith
  have h24 : StrictMonoOn apm_t00a05_squareAngle (Set.Icc (2 : ℝ) 4) := by
    intro x hx y hy hxy
    rw [heq24 hx, heq24 hy]
    have := Real.arctan_strictMono (sub_lt_sub_right hxy 3)
    linarith
  have h46 : StrictMonoOn apm_t00a05_squareAngle (Set.Icc (4 : ℝ) 6) := by
    intro x hx y hy hxy
    rw [heq46 hx, heq46 hy]
    have := neg_lt_neg (Real.arctan_strictMono (sub_lt_sub_left hxy 5))
    linarith
  have h68 : StrictMonoOn apm_t00a05_squareAngle (Set.Icc (6 : ℝ) 8) := by
    intro x hx y hy hxy
    rw [heq68 hx, heq68 hy]
    have := Real.arctan_strictMono (sub_lt_sub_right hxy 7)
    linarith
  have h04 : StrictMonoOn apm_t00a05_squareAngle (Set.Icc (0 : ℝ) 4) := by
    rw [show Set.Icc (0 : ℝ) 4 = Set.Icc 0 2 ∪ Set.Icc 2 4 by
      ext x; simp only [Set.mem_Icc, Set.mem_union]; constructor
      · intro hx
        by_cases h : x ≤ 2
        · exact Or.inl ⟨hx.1, h⟩
        · exact Or.inr ⟨le_of_not_ge h, hx.2⟩
      · rintro (hx | hx) <;> constructor <;> linarith]
    exact h02.union h24
      (show IsGreatest (Set.Icc (0 : ℝ) 2) 2 from
        ⟨⟨by norm_num, le_rfl⟩, fun _ h => h.2⟩)
      (show IsLeast (Set.Icc (2 : ℝ) 4) 2 from
        ⟨⟨le_rfl, by norm_num⟩, fun _ h => h.1⟩)
  have h06 : StrictMonoOn apm_t00a05_squareAngle (Set.Icc (0 : ℝ) 6) := by
    rw [show Set.Icc (0 : ℝ) 6 = Set.Icc 0 4 ∪ Set.Icc 4 6 by
      ext x; simp only [Set.mem_Icc, Set.mem_union]; constructor
      · intro hx
        by_cases h : x ≤ 4
        · exact Or.inl ⟨hx.1, h⟩
        · exact Or.inr ⟨le_of_not_ge h, hx.2⟩
      · rintro (hx | hx) <;> constructor <;> linarith]
    exact h04.union h46
      (show IsGreatest (Set.Icc (0 : ℝ) 4) 4 from
        ⟨⟨by norm_num, le_rfl⟩, fun _ h => h.2⟩)
      (show IsLeast (Set.Icc (4 : ℝ) 6) 4 from
        ⟨⟨le_rfl, by norm_num⟩, fun _ h => h.1⟩)
  rw [show Set.Icc (0 : ℝ) 8 = Set.Icc 0 6 ∪ Set.Icc 6 8 by
    ext x; simp only [Set.mem_Icc, Set.mem_union]; constructor
    · intro hx
      by_cases h : x ≤ 6
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨le_of_not_ge h, hx.2⟩
    · rintro (hx | hx) <;> constructor <;> linarith]
  exact h06.union h68
    (show IsGreatest (Set.Icc (0 : ℝ) 6) 6 from
      ⟨⟨by norm_num, le_rfl⟩, fun _ h => h.2⟩)
    (show IsLeast (Set.Icc (6 : ℝ) 8) 6 from
      ⟨⟨le_rfl, by norm_num⟩, fun _ h => h.1⟩)

lemma apm_t00a05_squareAngleFrom_strictMonoOn {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ8 : β ≤ 8) :
    StrictMonoOn (apm_t00a05_squareAngleFrom β) (Set.Icc (0 : ℝ) 8) := by
  let c := 8 - β
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hc8 : c ≤ 8 := by dsimp [c]; linarith
  have hleft : StrictMonoOn (apm_t00a05_squareAngleFrom β)
      (Set.Icc (0 : ℝ) c) := by
    intro x hx y hy hxy
    rcases hx with ⟨hx0, hxc⟩
    rcases hy with ⟨hy0, hyc⟩
    dsimp [c] at hxc hyc
    simp only [apm_t00a05_squareAngleFrom, if_pos hxc, if_pos hyc]
    apply apm_t00a05_squareAngle_strictMonoOn
    · constructor <;> linarith
    · constructor <;> linarith
    · linarith
  have hright_formula {u : ℝ} (hu : u ∈ Set.Icc c 8) :
      apm_t00a05_squareAngleFrom β u =
        apm_t00a05_squareAngle (u + β - 8) + 2 * Real.pi := by
    by_cases huc : u = c
    · subst u
      dsimp [c]
      simp only [apm_t00a05_squareAngleFrom, if_pos le_rfl]
      have hend := apm_t00a05_squareAngle_endpoints
      convert (show apm_t00a05_squareAngle 8 =
          apm_t00a05_squareAngle 0 + 2 * Real.pi by linarith) using 1 <;> ring
    · have hgt : 8 - β < u := by
        dsimp [c] at hu huc
        exact lt_of_le_of_ne hu.1 (Ne.symm huc)
      simp [apm_t00a05_squareAngleFrom, not_le.mpr hgt]
  have hright : StrictMonoOn (apm_t00a05_squareAngleFrom β)
      (Set.Icc c 8) := by
    intro x hx y hy hxy
    rw [hright_formula hx, hright_formula hy]
    rcases hx with ⟨hcx, hx8'⟩
    rcases hy with ⟨hcy, hy8'⟩
    dsimp [c] at hcx hcy
    have hxm : 0 ≤ x + β - 8 := by linarith
    have hym : 0 ≤ y + β - 8 := by linarith
    have hx8 : x + β - 8 ≤ 8 := by linarith
    have hy8 : y + β - 8 ≤ 8 := by linarith
    have := apm_t00a05_squareAngle_strictMonoOn
      ⟨hxm, hx8⟩ ⟨hym, hy8⟩ (by linarith)
    linarith
  rw [show Set.Icc (0 : ℝ) 8 = Set.Icc 0 c ∪ Set.Icc c 8 by
    ext x; simp only [Set.mem_Icc, Set.mem_union]; constructor
    · intro hx
      by_cases h : x ≤ c
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨le_of_not_ge h, hx.2⟩
    · rintro (hx | hx) <;> constructor <;> linarith]
  exact hleft.union hright
    (show IsGreatest (Set.Icc (0 : ℝ) c) c from
      ⟨⟨hc0, le_rfl⟩, fun _ h => h.2⟩)
    (show IsLeast (Set.Icc c 8) c from
      ⟨⟨le_rfl, hc8⟩, fun _ h => h.1⟩)

lemma apm_t00a05_squareAngleFrom_endpoints {β : ℝ}
    (hβ0 : 0 < β) (hβ8 : β ≤ 8) :
    apm_t00a05_squareAngleFrom β 8 -
      apm_t00a05_squareAngleFrom β 0 = 2 * Real.pi := by
  have h0 : (0 : ℝ) ≤ 8 - β := by linarith
  have h8 : ¬(8 : ℝ) ≤ 8 - β := by linarith
  simp only [apm_t00a05_squareAngleFrom, if_pos h0, if_neg h8]
  ring_nf

lemma apm_t00a05_squareAngle_perimeter_right_open {q : ℝ × ℝ}
    (hx : q.1 = 1) (hy0 : -1 < q.2) (hy1 : q.2 < 1) :
    apm_t00a05_squareAngle (apm_t00a05_squarePerimeter q) =
      Real.arctan (q.2 / q.1) + 2 * Real.pi := by
  rw [apm_t00a05_squarePerimeter_right (by linarith) hx]
  have h2 : ¬q.2 + 3 ≤ 2 := not_le.mpr (by linarith)
  have h4 : q.2 + 3 ≤ 4 := by linarith
  simp only [apm_t00a05_squareAngle, if_neg h2, if_pos h4, hx, div_one]
  ring

lemma apm_t00a05_squareAngle_perimeter_left_open {q : ℝ × ℝ}
    (hx : q.1 = -1) (hy0 : -1 < q.2) (hy1 : q.2 < 1) :
    apm_t00a05_squareAngle (apm_t00a05_squarePerimeter q) =
      Real.arctan (q.2 / q.1) + 3 * Real.pi := by
  rw [apm_t00a05_squarePerimeter_left (by linarith) (by linarith) (by linarith)]
  simp only [apm_t00a05_squareAngle, not_le.mpr (by linarith : 2 < 7 - q.2),
    not_le.mpr (by linarith : 4 < 7 - q.2),
    not_le.mpr (by linarith : 6 < 7 - q.2), hx, div_neg, div_one,
    if_false]
  congr 2 <;> ring

lemma apm_t00a05_squareAngle_perimeter_bottom_open {q : ℝ × ℝ}
    (hy : q.2 = -1) (hx0 : -1 < q.1) (hx1 : q.1 < 1) :
    apm_t00a05_squareAngle (apm_t00a05_squarePerimeter q) =
      -Real.arctan (q.1 / q.2) + 3 * Real.pi / 2 := by
  rw [apm_t00a05_squarePerimeter_bottom hy]
  have h2 : q.1 + 1 ≤ 2 := by linarith
  simp only [apm_t00a05_squareAngle, if_pos h2, hy, div_neg, div_one,
    Real.arctan_neg, neg_neg]
  congr 2 <;> ring

lemma apm_t00a05_squareAngle_perimeter_top_open {q : ℝ × ℝ}
    (hy : q.2 = 1) (hx0 : -1 < q.1) (hx1 : q.1 < 1) :
    apm_t00a05_squareAngle (apm_t00a05_squarePerimeter q) =
      -Real.arctan (q.1 / q.2) + 5 * Real.pi / 2 := by
  rw [apm_t00a05_squarePerimeter_top (by linarith) (by linarith) hy]
  have h2 : ¬5 - q.1 ≤ 2 := not_le.mpr (by linarith)
  have h4 : ¬5 - q.1 ≤ 4 := not_le.mpr (by linarith)
  have h6 : 5 - q.1 ≤ 6 := by linarith
  simp only [apm_t00a05_squareAngle, if_neg h2, if_neg h4, if_pos h6,
    hy, div_one]
  ring

/-- The four affine sides of the square perimeter decoder glue continuously
at the three corners. -/
lemma apm_t00a05_squareOfPerimeter_continuous :
    Continuous apm_t00a05_squareOfPerimeter := by
  unfold apm_t00a05_squareOfPerimeter
  have h6 : Continuous (fun s : ℝ =>
      if s ≤ 6 then (5 - s, 1) else (-1, 7 - s)) := by
    apply continuous_if_le (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop)
    intro x hx
    subst x
    norm_num
  have h4 : Continuous (fun s : ℝ =>
      if s ≤ 4 then (1, s - 3)
      else if s ≤ 6 then (5 - s, 1) else (-1, 7 - s)) := by
    apply continuous_if_le (by fun_prop) (by fun_prop)
        (by fun_prop) h6.continuousOn
    intro x hx
    subst x
    norm_num
  apply continuous_if_le (by fun_prop) (by fun_prop)
      (by fun_prop) h4.continuousOn
  intro x hx
  subst x
  norm_num

lemma apm_t00a05_squareOfPerimeter_mem_sphere {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 8) :
    apm_t00a05_squareOfPerimeter s ∈ Metric.sphere (0 : ℝ × ℝ) 1 := by
  rcases hs with ⟨hs0, hs8⟩
  rw [apm_t00a05_mem_supSphere_iff]
  unfold apm_t00a05_squareOfPerimeter
  split_ifs with h2 h4 h6
  · simp only [Prod.fst, Prod.snd, abs_neg, abs_one, max_eq_right_iff]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · simp only [Prod.fst, Prod.snd, abs_one, max_eq_left_iff]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · simp only [Prod.fst, Prod.snd, abs_one, max_eq_right_iff]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · simp only [Prod.fst, Prod.snd, abs_neg, abs_one, max_eq_left_iff]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

noncomputable def apm_t00a05_squareDecoder :
    Set.Icc (0 : ℝ) 8 → Metric.sphere (0 : ℝ × ℝ) 1 :=
  fun s => ⟨apm_t00a05_squareOfPerimeter s,
    apm_t00a05_squareOfPerimeter_mem_sphere s.2⟩

lemma apm_t00a05_squareOfPerimeter_squarePerimeter {q : ℝ × ℝ}
    (hq : q ∈ Metric.sphere 0 1) :
    apm_t00a05_squareOfPerimeter (apm_t00a05_squarePerimeter q) = q := by
  rcases apm_t00a05_supSphere_coordinate_bounds hq with ⟨hx0, hx1, hy0, hy1⟩
  have hedge := apm_t00a05_supSphere_on_edge hq
  unfold apm_t00a05_squarePerimeter
  split_ifs with hb hr ht
  · unfold apm_t00a05_squareOfPerimeter
    rw [if_pos (by linarith : q.1 + 1 ≤ 2)]
    ext <;> simp [hb]
  · unfold apm_t00a05_squareOfPerimeter
    have hygt : -1 < q.2 := lt_of_le_of_ne hy0 (Ne.symm hb)
    rw [if_neg (by linarith : ¬ q.2 + 3 ≤ 2),
      if_pos (by linarith : q.2 + 3 ≤ 4)]
    ext <;> simp [hr]
  · unfold apm_t00a05_squareOfPerimeter
    have hxlt : q.1 < 1 := lt_of_le_of_ne hx1 hr
    rw [if_neg (by linarith : ¬ 5 - q.1 ≤ 2),
      if_neg (by linarith : ¬ 5 - q.1 ≤ 4),
      if_pos (by linarith : 5 - q.1 ≤ 6)]
    ext <;> simp [ht]
  · have hxneg : q.1 = -1 := by
      rcases hedge with hxneg | hxpos | hyneg | hypos
      · exact hxneg
      · exact False.elim (hr hxpos)
      · exact False.elim (hb hyneg)
      · exact False.elim (ht hypos)
    have hygt : -1 < q.2 := lt_of_le_of_ne hy0 (Ne.symm hb)
    have hylt : q.2 < 1 := lt_of_le_of_ne hy1 ht
    unfold apm_t00a05_squareOfPerimeter
    rw [if_neg (by linarith : ¬ 7 - q.2 ≤ 2),
      if_neg (by linarith : ¬ 7 - q.2 ≤ 4),
      if_neg (by linarith : ¬ 7 - q.2 ≤ 6)]
    ext <;> simp [hxneg]

/-- The closed perimeter interval is a quotient presentation of the square
sphere, with its two endpoints identified at the lower-left corner. -/
lemma apm_t00a05_squareDecoder_isQuotientMap :
    Topology.IsQuotientMap apm_t00a05_squareDecoder := by
  apply IsQuotientMap.of_surjective_continuous
  · intro q
    let s : Set.Icc (0 : ℝ) 8 :=
      ⟨apm_t00a05_squarePerimeter q,
        apm_t00a05_squarePerimeter_mem_Icc q.2⟩
    refine ⟨s, ?_⟩
    apply Subtype.ext
    exact apm_t00a05_squareOfPerimeter_squarePerimeter q.2
  · exact Continuous.subtype_mk
      (apm_t00a05_squareOfPerimeter_continuous.comp continuous_subtype_val) _

lemma apm_t00a05_squarePerimeter_injOn :
    Set.InjOn apm_t00a05_squarePerimeter (Metric.sphere (0 : ℝ × ℝ) 1) := by
  intro p hp q hq hpq
  rw [← apm_t00a05_squareOfPerimeter_squarePerimeter hp,
    ← apm_t00a05_squareOfPerimeter_squarePerimeter hq, hpq]

lemma apm_t00a05_segment_origin_subset_region {q : ℝ × ℝ}
    (hq : q ∈ apm_t00a05_region) :
    segment ℝ (0, 0) q ⊆ apm_t00a05_region :=
  apm_t00a05_region_convex.segment_subset apm_t00a05_origin_mem_region hq

lemma apm_t00a05_C2_projected_level {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht2pi : t ≤ 2 * Real.pi) :
    apm_t00a05_level ((γ t).1, (γ t).2.1) = 10 := by
  rcases hγ.2.2.2.1 t ht0 ht2pi with ⟨hellipsoid, hgraph⟩
  unfold apm_t00a05_level
  rw [← hgraph]
  exact hellipsoid

lemma apm_t00a05_C2_avoids_axis {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht2pi : t ≤ 2 * Real.pi) :
    (γ t).1 ≠ 0 ∨ (γ t).2.1 ≠ 0 := by
  by_contra haxis
  push_neg at haxis
  rcases hγ.2.2.2.1 t ht0 ht2pi with ⟨hellipsoid, hgraph⟩
  have hz : (γ t).2.2 = 1 := by
    simpa [haxis.1, haxis.2] using hgraph
  rw [haxis.1, haxis.2, hz] at hellipsoid
  norm_num at hellipsoid

lemma apm_t00a05_C2_projection_injOn {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) :
    Set.InjOn (fun t ↦ ((γ t).1, (γ t).2.1))
      (Set.Ico (0 : ℝ) (2 * Real.pi)) := by
  intro s hs t ht hst
  have hx : (γ s).1 = (γ t).1 :=
    congrArg (fun q : ℝ × ℝ ↦ q.1) hst
  have hy : (γ s).2.1 = (γ t).2.1 :=
    congrArg (fun q : ℝ × ℝ ↦ q.2) hst
  have hsgraph := (hγ.2.2.2.1 s hs.1 hs.2.le).2
  have htgraph := (hγ.2.2.2.1 t ht.1 ht.2.le).2
  have hz : (γ s).2.2 = (γ t).2.2 := by
    rw [hsgraph, htgraph, hx, hy]
  exact hγ.2.2.1 hs ht (Prod.ext hx (Prod.ext hy hz))

lemma apm_t00a05_C2_projection_contDiff {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) :
    ContDiff ℝ 1 (fun t ↦ ((γ t).1, (γ t).2.1)) := by
  exact hγ.1.fst.prodMk hγ.1.snd.fst

lemma apm_t00a05_C2_projection_closed {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) :
    ((γ 0).1, (γ 0).2.1) =
      ((γ (2 * Real.pi)).1, (γ (2 * Real.pi)).2.1) := by
  exact congrArg (fun p : ℝ × ℝ × ℝ ↦ (p.1, p.2.1)) hγ.2.1

lemma apm_t00a05_C2_projection_mem_frontier {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht2pi : t ≤ 2 * Real.pi) :
    ((γ t).1, (γ t).2.1) ∈ frontier apm_t00a05_region :=
  apm_t00a05_level_eq_ten_mem_frontier
    (apm_t00a05_C2_projected_level hγ ht0 ht2pi)

lemma apm_t00a05_C2_radialized_mem_sphere {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht2pi : t ≤ 2 * Real.pi) :
    apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1) ∈
      Metric.sphere 0 1 := by
  rw [← apm_t00a05_radialHomeomorph_image_frontier]
  exact ⟨_, apm_t00a05_C2_projection_mem_frontier hγ ht0 ht2pi, rfl⟩

lemma apm_t00a05_C2_radialized_continuous {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) :
    Continuous (fun t ↦
      apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)) := by
  exact apm_t00a05_radialHomeomorph.continuous.comp
    (apm_t00a05_C2_projection_contDiff hγ).continuous

lemma apm_t00a05_C2_radialized_injOn {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) :
    Set.InjOn (fun t ↦
      apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1))
      (Set.Ico (0 : ℝ) (2 * Real.pi)) :=
  apm_t00a05_radialHomeomorph.injective.injOn.comp
    (apm_t00a05_C2_projection_injOn hγ) (Set.mapsTo_image _ _)

lemma apm_t00a05_C2_radialized_closed {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) :
    apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1) =
      apm_t00a05_radialHomeomorph
        ((γ (2 * Real.pi)).1, (γ (2 * Real.pi)).2.1) := by
  rw [apm_t00a05_C2_projection_closed hγ]

lemma apm_t00a05_no_continuous_real_simple_loop {f : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T) (hf : Continuous f) (hinj : Set.InjOn f (Set.Ico 0 T))
    (hclosed : f 0 = f T) : False := by
  have hmono := hf.continuousOn.strictMonoOn_of_injOn_Ioo hT
    (hinj.mono Set.Ioo_subset_Ico_self)
  let m := T / 3
  let n := 2 * T / 3
  have hm : 0 < m := by dsimp [m]; positivity
  have hmn : m < n := by dsimp [m, n]; linarith
  have hn : n < T := by dsimp [n]; linarith
  have hmT : m ∈ Set.Ioo (0 : ℝ) T := ⟨hm, hmn.trans hn⟩
  have hnT : n ∈ Set.Ioo (0 : ℝ) T := ⟨hm.trans hmn, hn⟩
  rcases hmono with hinc | hdec
  · have h0m : f 0 ≤ f m := by
      apply le_of_tendsto (x := nhdsWithin 0 (Set.Ioi 0))
        (hf.continuousAt.tendsto.mono_left inf_le_left)
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hm).filter_mono inf_le_left] with x hx hxm
      exact (hinc ⟨hx, hxm.trans (hmn.trans hn)⟩ hmT hxm).le
    have hnT' : f n ≤ f T := by
      apply ge_of_tendsto (x := nhdsWithin T (Set.Iio T))
        (hf.continuousAt.tendsto.mono_left inf_le_left)
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds hn).filter_mono inf_le_left] with x hx hnx
      exact (hinc hnT ⟨(hm.trans hmn).trans hnx, hx⟩ hnx).le
    have := h0m.trans_lt (hinc hmT hnT hmn) |>.trans_le hnT'
    exact this.ne hclosed
  · have h0m : f m ≤ f 0 := by
      apply ge_of_tendsto (x := nhdsWithin 0 (Set.Ioi 0))
        (hf.continuousAt.tendsto.mono_left inf_le_left)
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hm).filter_mono inf_le_left] with x hx hxm
      exact (hdec ⟨hx, hxm.trans (hmn.trans hn)⟩ hmT hxm).le
    have hnT' : f T ≤ f n := by
      apply le_of_tendsto (x := nhdsWithin T (Set.Iio T))
        (hf.continuousAt.tendsto.mono_left inf_le_left)
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds hn).filter_mono inf_le_left] with x hx hnx
      exact (hdec hnT ⟨(hm.trans hmn).trans hnx, hx⟩ hnx).le
    have := hnT'.trans_lt (hdec hmT hnT hmn) |>.trans_le h0m
    exact this.ne hclosed.symm

lemma apm_t00a05_C2_exact_part_zero {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) :
    ∫ t in Set.Icc (0 : ℝ) (2 * Real.pi),
      Real.cos ((γ t).2.2) * deriv (fun s ↦ (γ s).2.2) t = 0 := by
  have hz : ContDiff ℝ 1 (fun t ↦ (γ t).2.2) := hγ.1.snd.snd
  have hderiv (t : ℝ) :
      deriv (fun s ↦ Real.sin ((γ s).2.2)) t =
        Real.cos ((γ t).2.2) * deriv (fun s ↦ (γ s).2.2) t :=
    (hz.differentiable_one.differentiableAt.hasDerivAt.sin).deriv
  have hle : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  calc
    ∫ t in (0 : ℝ)..2 * Real.pi,
        Real.cos ((γ t).2.2) * deriv (fun s ↦ (γ s).2.2) t =
        ∫ t in (0 : ℝ)..2 * Real.pi,
          deriv (fun s ↦ Real.sin ((γ s).2.2)) t := by
            apply intervalIntegral.integral_congr
            intro t _
            exact (hderiv t).symm
    _ = Real.sin ((γ (2 * Real.pi)).2.2) - Real.sin ((γ 0).2.2) :=
      intervalIntegral.integral_deriv_of_contDiffOn_Icc hz.sin.contDiffOn hle
    _ = 0 := by
      have hzend : (γ 0).2.2 = (γ (2 * Real.pi)).2.2 :=
        congrArg (fun p : ℝ × ℝ × ℝ ↦ p.2.2) hγ.2.1
      rw [← hzend]
      ring

noncomputable def apm_t00a05_angularDensity
    (γ : ℝ → ℝ × ℝ × ℝ) (t : ℝ) : ℝ :=
  ((γ t).1 * deriv (fun s ↦ (γ s).2.1) t -
    (γ t).2.1 * deriv (fun s ↦ (γ s).1) t) /
    ((γ t).1 ^ 2 + (γ t).2.1 ^ 2)

lemma apm_t00a05_angularDensity_continuousOn {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) :
    ContinuousOn (apm_t00a05_angularDensity γ)
      (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
  have hx : ContDiff ℝ 1 (fun t => (γ t).1) := hγ.1.fst
  have hy : ContDiff ℝ 1 (fun t => (γ t).2.1) := hγ.1.snd.fst
  apply ContinuousOn.div
  · exact ((hx.continuous.mul hy.continuous_deriv_one).sub
      (hy.continuous.mul hx.continuous_deriv_one)).continuousOn
  · exact ((hx.continuous.pow 2).add (hy.continuous.pow 2)).continuousOn
  · intro t ht hzero
    have hsquares : (γ t).1 = 0 ∧ (γ t).2.1 = 0 := by
      have hx2 : 0 ≤ (γ t).1 ^ 2 := sq_nonneg _
      have hy2 : 0 ≤ (γ t).2.1 ^ 2 := sq_nonneg _
      constructor <;> nlinarith
    rcases apm_t00a05_C2_avoids_axis hγ ht.1 ht.2 with hx0 | hy0
    · exact hx0 hsquares.1
    · exact hy0 hsquares.2

lemma apm_t00a05_projected_radius_sq_pos {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    0 < (γ t).1 ^ 2 + (γ t).2.1 ^ 2 := by
  rcases apm_t00a05_C2_avoids_axis hγ ht.1 ht.2 with hx | hy
  · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg (γ t).2.1]
  · nlinarith [sq_nonneg (γ t).1, sq_pos_of_ne_zero hy]

/-- The signed-area density is the positive squared radius times angular
density.  This is the algebraic bridge used to rule out clockwise order from
the orientation hypothesis. -/
lemma apm_t00a05_signedAreaDensity_eq_radius_sq_mul_angularDensity
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    (γ t).1 * deriv (fun s => (γ s).2.1) t -
        (γ t).2.1 * deriv (fun s => (γ s).1) t =
      ((γ t).1 ^ 2 + (γ t).2.1 ^ 2) *
        apm_t00a05_angularDensity γ t := by
  have hne : (γ t).1 ^ 2 + (γ t).2.1 ^ 2 ≠ 0 :=
    ne_of_gt (apm_t00a05_projected_radius_sq_pos hγ ht)
  simp only [apm_t00a05_angularDensity]
  field_simp

/-- The registered positive signed area rules out an everywhere nonpositive
angular density.  Later, clockwise chart order only has to establish that
pointwise sign statement. -/
lemma apm_t00a05_not_angularDensity_nonpos
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :
    ¬(∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      apm_t00a05_angularDensity γ t ≤ 0) := by
  intro hnonpos
  have harea_nonpos :
      ∫ t in Set.Icc (0 : ℝ) (2 * Real.pi),
          (γ t).1 * deriv (fun s => (γ s).2.1) t -
            (γ t).2.1 * deriv (fun s => (γ s).1) t ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [apm_t00a05_signedAreaDensity_eq_radius_sq_mul_angularDensity hγ ht]
    exact mul_nonpos_of_nonneg_of_nonpos
      (apm_t00a05_projected_radius_sq_pos hγ ht).le (hnonpos t ht)
  exact (not_lt_of_ge harea_nonpos) hγ.2.2.2.2

lemma apm_t00a05_exists_angularDensity_pos
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :
    ∃ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      0 < apm_t00a05_angularDensity γ t := by
  by_contra h
  apply apm_t00a05_not_angularDensity_nonpos hγ
  intro t ht
  exact le_of_not_gt (fun hpos => h ⟨t, ht, hpos⟩)

lemma apm_t00a05_exists_angularDensity_pos_Ioo
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :
    ∃ t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi),
      0 < apm_t00a05_angularDensity γ t := by
  by_contra h
  have hnonpos : ∀ t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi),
      apm_t00a05_angularDensity γ t ≤ 0 := by
    intro t ht
    exact le_of_not_gt (fun hpos => h ⟨t, ht, hpos⟩)
  have harea_nonpos :
      ∫ t in Set.Icc (0 : ℝ) (2 * Real.pi),
          (γ t).1 * deriv (fun s => (γ s).2.1) t -
            (γ t).2.1 * deriv (fun s => (γ s).1) t ≤ 0 := by
    rw [integral_Icc_eq_integral_Ioo]
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨ht.1.le, ht.2.le⟩
    rw [apm_t00a05_signedAreaDensity_eq_radius_sq_mul_angularDensity hγ ht']
    exact mul_nonpos_of_nonneg_of_nonpos
      (apm_t00a05_projected_radius_sq_pos hγ ht').le (hnonpos t ht)
  exact (not_lt_of_ge harea_nonpos) hγ.2.2.2.2

/-- The frozen line-integral encoding reduces exactly to the negative angular
density: its `z` contribution is the already-proved exact term. -/
lemma apm_t00a05_lineIntegral_eq_neg_angular {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) :
    apm_t00a05_lineIntegral γ 0 (2 * Real.pi) =
      -(∫ t in Set.Icc (0 : ℝ) (2 * Real.pi),
        apm_t00a05_angularDensity γ t) := by
  have hAint : IntegrableOn (apm_t00a05_angularDensity γ)
      (Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    (apm_t00a05_angularDensity_continuousOn hγ).integrableOn_Icc
  let zterm : ℝ → ℝ := fun t =>
    Real.cos ((γ t).2.2) * deriv (fun s ↦ (γ s).2.2) t
  have hz : ContDiff ℝ 1 (fun t => (γ t).2.2) := hγ.1.snd.snd
  have hzint : IntegrableOn zterm (Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    ((Real.continuous_cos.comp hz.continuous).mul
      hz.continuous_deriv_one).continuousOn.integrableOn_Icc
  unfold apm_t00a05_lineIntegral
  calc
    (∫ t in Set.Icc (0 : ℝ) (2 * Real.pi),
        let v := apm_t00a05_omega (γ t)
        v.1 * deriv (fun s => (γ s).1) t +
          v.2.1 * deriv (fun s => (γ s).2.1) t +
          v.2.2 * deriv (fun s => (γ s).2.2) t) =
      ∫ t in Set.Icc (0 : ℝ) (2 * Real.pi),
        -apm_t00a05_angularDensity γ t + zterm t := by
          apply integral_congr_ae
          filter_upwards with t
          simp only [apm_t00a05_omega, apm_t00a05_angularDensity,
            zterm, Prod.fst, Prod.snd]
          ring
    _ = (∫ t in Set.Icc (0 : ℝ) (2 * Real.pi),
          -apm_t00a05_angularDensity γ t) +
        ∫ t in Set.Icc (0 : ℝ) (2 * Real.pi), zterm t := by
          exact integral_add hAint.neg hzint
    _ = -(∫ t in Set.Icc (0 : ℝ) (2 * Real.pi),
          apm_t00a05_angularDensity γ t) := by
          rw [integral_neg, apm_t00a05_C2_exact_part_zero hγ]
          simp [zterm]

lemma apm_t00a05_angle_primitive_deriv {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : ContDiff ℝ 1 γ) {t : ℝ} (hx0 : (γ t).1 ≠ 0) :
    deriv (fun s ↦ Real.arctan ((γ s).2.1 / (γ s).1)) t =
      ((γ t).1 * deriv (fun s ↦ (γ s).2.1) t -
        (γ t).2.1 * deriv (fun s ↦ (γ s).1) t) /
        ((γ t).1 ^ 2 + (γ t).2.1 ^ 2) := by
  have hx : HasDerivAt (fun s ↦ (γ s).1)
      (deriv (fun s ↦ (γ s).1) t) t :=
    hγ.fst.differentiable_one.differentiableAt.hasDerivAt
  have hy : HasDerivAt (fun s ↦ (γ s).2.1)
      (deriv (fun s ↦ (γ s).2.1) t) t :=
    hγ.snd.fst.differentiable_one.differentiableAt.hasDerivAt
  have hquot := hy.div hx hx0
  have hatan := (Real.hasDerivAt_arctan ((γ t).2.1 / (γ t).1)).comp t hquot
  change deriv (Real.arctan ∘ ((fun s ↦ (γ s).2.1) / (fun s ↦ (γ s).1))) t = _
  rw [hatan.deriv]
  field_simp

lemma apm_t00a05_angle_primitive_deriv_y {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : ContDiff ℝ 1 γ) {t : ℝ} (hy0 : (γ t).2.1 ≠ 0) :
    deriv (fun s ↦ -Real.arctan ((γ s).1 / (γ s).2.1)) t =
      ((γ t).1 * deriv (fun s ↦ (γ s).2.1) t -
        (γ t).2.1 * deriv (fun s ↦ (γ s).1) t) /
        ((γ t).1 ^ 2 + (γ t).2.1 ^ 2) := by
  have hx : HasDerivAt (fun s ↦ (γ s).1)
      (deriv (fun s ↦ (γ s).1) t) t :=
    hγ.fst.differentiable_one.differentiableAt.hasDerivAt
  have hy : HasDerivAt (fun s ↦ (γ s).2.1)
      (deriv (fun s ↦ (γ s).2.1) t) t :=
    hγ.snd.fst.differentiable_one.differentiableAt.hasDerivAt
  have hquot := hx.div hy hy0
  have hatan := (Real.hasDerivAt_arctan ((γ t).1 / (γ t).2.1)).comp t hquot
  have hneg := hatan.neg
  change deriv ((-Real.arctan) ∘
    ((fun u ↦ (γ u).1) / (fun u ↦ (γ u).2.1))) t = _
  convert hneg.deriv using 1 <;> field_simp <;> ring

/-- FTC for one arc contained in an `x ≠ 0` half-plane. -/
lemma apm_t00a05_angularDensity_integral_of_x_ne_zero
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    {a b : ℝ} (hab : a ≤ b)
    (hx0 : ∀ t ∈ Set.Icc a b, (γ t).1 ≠ 0) :
    ∫ t in Set.Icc a b, apm_t00a05_angularDensity γ t =
      Real.arctan ((γ b).2.1 / (γ b).1) -
        Real.arctan ((γ a).2.1 / (γ a).1) := by
  let F : ℝ → ℝ := fun t => Real.arctan ((γ t).2.1 / (γ t).1)
  have hF : ContDiffOn ℝ 1 F (Set.Icc a b) := by
    exact ((hγ.1.snd.fst.contDiffOn.div hγ.1.fst.contDiffOn hx0).arctan)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  calc
    ∫ t in a..b, apm_t00a05_angularDensity γ t =
        ∫ t in a..b, deriv F t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using ht
      exact (apm_t00a05_angle_primitive_deriv hγ.1
        (hx0 t ht')).symm
    _ = F b - F a := intervalIntegral.integral_deriv_of_contDiffOn_Icc hF hab
    _ = _ := rfl

/-- FTC for one arc contained in a `y ≠ 0` half-plane. -/
lemma apm_t00a05_angularDensity_integral_of_y_ne_zero
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    {a b : ℝ} (hab : a ≤ b)
    (hy0 : ∀ t ∈ Set.Icc a b, (γ t).2.1 ≠ 0) :
    ∫ t in Set.Icc a b, apm_t00a05_angularDensity γ t =
      -Real.arctan ((γ b).1 / (γ b).2.1) -
        -Real.arctan ((γ a).1 / (γ a).2.1) := by
  let F : ℝ → ℝ := fun t => -Real.arctan ((γ t).1 / (γ t).2.1)
  have hF : ContDiffOn ℝ 1 F (Set.Icc a b) := by
    exact ((hγ.1.fst.contDiffOn.div hγ.1.snd.fst.contDiffOn hy0).arctan).neg
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  calc
    ∫ t in a..b, apm_t00a05_angularDensity γ t =
        ∫ t in a..b, deriv F t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using ht
      exact (apm_t00a05_angle_primitive_deriv_y hγ.1
        (hy0 t ht')).symm
    _ = F b - F a := intervalIntegral.integral_deriv_of_contDiffOn_Icc hF hab
    _ = _ := rfl

/-- Positive orientation is witnessed by a positive derivative of one of the
two local angle primitives at an interior time. -/
lemma apm_t00a05_exists_local_angle_deriv_pos
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :
    ∃ t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi),
      (((γ t).1 ≠ 0 ∧
          0 < deriv (fun u => Real.arctan ((γ u).2.1 / (γ u).1)) t) ∨
       ((γ t).2.1 ≠ 0 ∧
          0 < deriv (fun u => -Real.arctan ((γ u).1 / (γ u).2.1)) t)) := by
  rcases apm_t00a05_exists_angularDensity_pos_Ioo hγ with ⟨t, ht, hpos⟩
  refine ⟨t, ht, ?_⟩
  rcases apm_t00a05_C2_avoids_axis hγ ht.1.le ht.2.le with hx | hy
  · left
    exact ⟨hx, by
      rw [apm_t00a05_angle_primitive_deriv hγ.1 hx]
      exact hpos⟩
  · right
    exact ⟨hy, by
      rw [apm_t00a05_angle_primitive_deriv_y hγ.1 hy]
      exact hpos⟩

lemma apm_t00a05_dOmega_eq_zero (p : apm_t00a05_U) :
    apm_t00a05_dOmega p.1 = 0 := by
  rcases p with ⟨⟨x, y, z⟩, hxy⟩
  have hden : x ^ 2 + y ^ 2 ≠ 0 := by
    rcases hxy with hx | hy
    · nlinarith [sq_pos_of_ne_zero hx]
    · nlinarith [sq_pos_of_ne_zero hy]
  ext <;>
    simp only [apm_t00a05_dOmega, apm_t00a05_omega, Prod.fst,
      Prod.snd, deriv_const, sub_zero]
  · have hxden : HasDerivAt (fun u : ℝ ↦ u ^ 2 + y ^ 2) (2 * x) x := by
      convert ((hasDerivAt_id x).pow 2).add_const (y ^ 2) using 1 <;> simp [id] <;> ring
    have hyden : HasDerivAt (fun v : ℝ ↦ x ^ 2 + v ^ 2) (2 * y) y := by
      convert (hasDerivAt_const y (x ^ 2)).add ((hasDerivAt_id y).pow 2) using 1 <;>
        simp [id] <;> ring
    have hxnum : HasDerivAt (fun u : ℝ ↦ -u) (-1) x := by
      simpa using (hasDerivAt_id x).neg
    have hynum : HasDerivAt (fun v : ℝ ↦ v) 1 y := hasDerivAt_id y
    have hxquot := hxnum.div hxden hden
    have hyquot := hynum.div hyden hden
    have hxder := hxquot.deriv
    have hyder := hyquot.deriv
    simp only [Pi.div_apply] at hxder hyder
    change deriv ((fun u : ℝ ↦ -u) / (fun u ↦ u ^ 2 + y ^ 2)) x -
      deriv ((fun v : ℝ ↦ v) / (fun v ↦ x ^ 2 + v ^ 2)) y = 0
    rw [hxder, hyder]
    field_simp
    ring
  · simp
  · simp

lemma apm_t00a05_lineIntegral_C1 :
    apm_t00a05_lineIntegral apm_t00a05_C1 0 (2 * Real.pi) =
      -2 * Real.pi := by
  unfold apm_t00a05_lineIntegral
  calc
    _ = ∫ _t in Set.Icc (0 : ℝ) (2 * Real.pi), (-1 : ℝ) := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [apm_t00a05_C1, apm_t00a05_omega, Prod.fst, Prod.snd]
      rw [Real.hasDerivAt_cos t |>.deriv, Real.hasDerivAt_sin t |>.deriv]
      rw [Real.cos_sq_add_sin_sq]
      simp
      nlinarith [Real.sin_sq_add_cos_sq t]
    _ = -2 * Real.pi := by
      rw [setIntegral_const]
      simp [Real.volume_Icc, Real.pi_pos.le]

/-- Route step 9 (memory e-1f2d3d6d, formula verified in trial 1): rotate the
perimeter coordinate so the cut sits at `β`. -/
noncomputable def apm_t00a05_rot (β s : ℝ) : ℝ :=
  if s < β then s + 8 - β else s - β

/-- `rot β` is continuous away from its cut `s = β`: on each side it is
eventually affine, since the branch condition `s < β` is eventually constant. -/
lemma apm_t00a05_rot_continuousAt {β s : ℝ} (hs : s ≠ β) :
    ContinuousAt (apm_t00a05_rot β) s := by
  unfold apm_t00a05_rot
  rcases lt_or_gt_of_ne hs with h | h
  · have hopen : {t : ℝ | t < β} ∈ nhds s :=
      (isOpen_lt (continuous_id (X := ℝ))
        (continuous_const (X := ℝ) (y := β))).mem_nhds h
    refine (show ContinuousAt (fun t : ℝ => t + 8 - β) s by fun_prop).congr ?_
    filter_upwards [hopen] with t ht
    exact (if_pos ht).symm
  · have hopen : {t : ℝ | β < t} ∈ nhds s :=
      (isOpen_lt (continuous_const (X := ℝ) (y := β))
        (continuous_id (X := ℝ))).mem_nhds h
    refine (show ContinuousAt (fun t : ℝ => t - β) s by fun_prop).congr ?_
    filter_upwards [hopen] with t ht
    exact (if_neg (not_lt.2 ht.le)).symm

lemma apm_t00a05_rot_lt_rot_iff_of_same_side {β s t : ℝ}
    (hside : (s < β ∧ t < β) ∨ (β ≤ s ∧ β ≤ t)) :
    apm_t00a05_rot β s < apm_t00a05_rot β t ↔ s < t := by
  rcases hside with h | h
  · simp [apm_t00a05_rot, h.1, h.2]
  · simp [apm_t00a05_rot, not_lt.mpr h.1, not_lt.mpr h.2]

lemma apm_t00a05_rot_le_rot_iff_of_same_side {β s t : ℝ}
    (hside : (s < β ∧ t < β) ∨ (β ≤ s ∧ β ≤ t)) :
    apm_t00a05_rot β s ≤ apm_t00a05_rot β t ↔ s ≤ t := by
  rcases hside with h | h
  · simp [apm_t00a05_rot, h.1, h.2]
  · simp [apm_t00a05_rot, not_lt.mpr h.1, not_lt.mpr h.2]

lemma apm_t00a05_rot_mem_Icc {β s : ℝ} (hβ0 : 0 ≤ β) (hβ8 : β ≤ 8)
    (hs : s ∈ Set.Icc (0 : ℝ) 8) :
    apm_t00a05_rot β s ∈ Set.Icc (0 : ℝ) 8 := by
  unfold apm_t00a05_rot
  split_ifs with h
  · constructor <;> linarith [hs.1, hs.2]
  · constructor <;> linarith [hs.1, hs.2, not_lt.mp h]

lemma apm_t00a05_squareAngleFrom_rot {β s : ℝ}
    (hβ0 : 0 < β) (hβ8 : β ≤ 8) (hs : s ∈ Set.Icc (0 : ℝ) 8) :
    apm_t00a05_squareAngleFrom β (apm_t00a05_rot β s) =
      if s < β then apm_t00a05_squareAngle s + 2 * Real.pi
      else apm_t00a05_squareAngle s := by
  unfold apm_t00a05_rot
  split_ifs with h
  · by_cases hs0 : s = 0
    · subst s
      have hend := apm_t00a05_squareAngle_endpoints
      simp [apm_t00a05_squareAngleFrom]
      linarith
    · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      have hcut : ¬s + 8 - β ≤ 8 - β := by linarith
      simp [apm_t00a05_squareAngleFrom, hcut]
  · have hcut : s - β ≤ 8 - β := by linarith [hs.2]
    simp [apm_t00a05_squareAngleFrom, hcut]

lemma apm_t00a05_squareAngleFrom_strictAntiOn_comp_rot
    {D : Set ℝ} {p : ℝ → ℝ} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ8 : β ≤ 8)
    (hpIcc : Set.MapsTo p D (Set.Icc (0 : ℝ) 8))
    (hanti : StrictAntiOn (fun x => apm_t00a05_rot β (p x)) D) :
    StrictAntiOn
      (fun x => apm_t00a05_squareAngleFrom β (apm_t00a05_rot β (p x))) D := by
  intro x hx y hy hxy
  apply apm_t00a05_squareAngleFrom_strictMonoOn hβ0 hβ8
  · exact apm_t00a05_rot_mem_Icc hβ0 hβ8 (hpIcc hy)
  · exact apm_t00a05_rot_mem_Icc hβ0 hβ8 (hpIcc hx)
  · exact hanti hx hy hxy

lemma apm_t00a05_squareAngle_strictAntiOn_of_rot_strictAntiOn
    {D : Set ℝ} {p : ℝ → ℝ} {β : ℝ}
    (hpIcc : Set.MapsTo p D (Set.Icc (0 : ℝ) 8))
    (hside : (∀ x ∈ D, p x < β) ∨ (∀ x ∈ D, β ≤ p x))
    (hanti : StrictAntiOn (fun x => apm_t00a05_rot β (p x)) D) :
    StrictAntiOn (fun x => apm_t00a05_squareAngle (p x)) D := by
  intro x hx y hy hxy
  have hrot := hanti hx hy hxy
  have hpyx : p y < p x := by
    apply (apm_t00a05_rot_lt_rot_iff_of_same_side
      (show (p y < β ∧ p x < β) ∨ (β ≤ p y ∧ β ≤ p x) by
        rcases hside with h | h
        · exact Or.inl ⟨h y hy, h x hx⟩
        · exact Or.inr ⟨h y hy, h x hx⟩)).mp
    exact hrot
  exact apm_t00a05_squareAngle_strictMonoOn (hpIcc hy) (hpIcc hx) hpyx

/-- Route step 9 seam: the perimeter chart inverts the decoder on `[0, 8]`
with the `0`/`8` seam — `8` decodes to the corner `(-1, -1)`, whose
perimeter coordinate is `0`, and every other `s ∈ [0, 8]` is reproduced
exactly. -/
lemma apm_t00a05_squarePerimeter_squareOfPerimeter {s : ℝ}
    (hs0 : 0 ≤ s) (hs8 : s ≤ 8) :
    apm_t00a05_squarePerimeter (apm_t00a05_squareOfPerimeter s) =
      if s = 8 then 0 else s := by
  by_cases h8 : s = 8
  · subst h8
    norm_num [apm_t00a05_squareOfPerimeter, apm_t00a05_squarePerimeter]
  · have hres : apm_t00a05_squarePerimeter (apm_t00a05_squareOfPerimeter s) = s := by
      unfold apm_t00a05_squareOfPerimeter
      split_ifs with h1 h2 h3
      all_goals simp only [apm_t00a05_squarePerimeter]
      all_goals split_ifs <;> first
        | linarith
        | exact absurd (by linarith : s = 8) h8
    rw [hres, if_neg h8]

/-- The seam cancels under rotation: `rot β` takes the same value at `0` and
`8` whenever the cut `β` lies in `(0, 8]` — this is what makes the composite
`rot β ∘ squarePerimeter ∘ squareOfPerimeter` continuous across the corner. -/
lemma apm_t00a05_rot_seam_cancel {β : ℝ} (hβ0 : 0 < β) (hβ8 : β ≤ 8) :
    apm_t00a05_rot β 0 = apm_t00a05_rot β 8 := by
  simp only [apm_t00a05_rot]
  rw [if_pos hβ0, if_neg (by linarith : ¬ 8 < β)]
  ring

/-- On the closed perimeter parameter interval the decoder/encoder seam is
invisible after rotation, so the composite is continuous everywhere except at
the deliberately removed cut `β`. -/
lemma apm_t00a05_rot_square_chart_continuousWithinAt
    {β u : ℝ} (hβ0 : 0 < β) (hβ8 : β ≤ 8)
    (hu : u ∈ Set.Icc (0 : ℝ) 8) (huβ : u ≠ β) :
    ContinuousWithinAt
      (fun t ↦ apm_t00a05_rot β
        (apm_t00a05_squarePerimeter (apm_t00a05_squareOfPerimeter t)))
      (Set.Icc (0 : ℝ) 8) u := by
  have heq (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 8) :
      apm_t00a05_rot β
          (apm_t00a05_squarePerimeter (apm_t00a05_squareOfPerimeter t)) =
        apm_t00a05_rot β t := by
    rw [apm_t00a05_squarePerimeter_squareOfPerimeter ht.1 ht.2]
    by_cases ht8 : t = 8
    · rw [if_pos ht8, ht8]
      exact apm_t00a05_rot_seam_cancel hβ0 hβ8
    · rw [if_neg ht8]
  exact (apm_t00a05_rot_continuousAt huβ).continuousWithinAt.congr
    heq (heq u hu)

/-- Removing one decoded point opens the square sphere into a real chart.
Continuity is descended through the compact quotient presentation, rather
than reproved separately at all four corners. -/
lemma apm_t00a05_rot_square_chart_continuous {β : ℝ}
    (hβ0 : 0 < β) (hβ8 : β ≤ 8) :
    Continuous (fun q :
      {q : Metric.sphere (0 : ℝ × ℝ) 1 |
        q.1 ≠ apm_t00a05_squareOfPerimeter β} =>
      apm_t00a05_rot β (apm_t00a05_squarePerimeter q.1.1)) := by
  let b : Metric.sphere (0 : ℝ × ℝ) 1 :=
    ⟨apm_t00a05_squareOfPerimeter β,
      apm_t00a05_squareOfPerimeter_mem_sphere ⟨hβ0.le, hβ8⟩⟩
  let S : Set (Metric.sphere (0 : ℝ × ℝ) 1) :=
    {q | q.1 ≠ apm_t00a05_squareOfPerimeter β}
  let D : Set (Set.Icc (0 : ℝ) 8) := apm_t00a05_squareDecoder ⁻¹' S
  let f := S.restrictPreimage apm_t00a05_squareDecoder
  let g : S → ℝ := fun q =>
    apm_t00a05_rot β (apm_t00a05_squarePerimeter q.1.1)
  have hSopen : IsOpen S := by
    have hSb : S = {b}ᶜ := by
      ext q
      simp [S, b, Subtype.ext_iff]
    rw [hSb]
    exact isOpen_compl_singleton
  have hquot : Topology.IsQuotientMap f :=
    apm_t00a05_squareDecoder_isQuotientMap.restrictPreimage_isOpen
      hSopen
  have hK : ContinuousOn
      (fun u : ℝ => apm_t00a05_rot β
        (apm_t00a05_squarePerimeter (apm_t00a05_squareOfPerimeter u)))
      (Set.Icc (0 : ℝ) 8 \ {β}) := by
    intro u hu
    exact (apm_t00a05_rot_square_chart_continuousWithinAt hβ0 hβ8 hu.1
      (by simpa using hu.2)).mono Set.diff_subset
  have hj : Continuous (fun u : D =>
      (⟨u.1.1, ⟨u.1.2, by
        intro huβ
        apply u.2
        change apm_t00a05_squareOfPerimeter u.1.1 =
          apm_t00a05_squareOfPerimeter β
        rw [huβ]⟩⟩ : ↥(Set.Icc (0 : ℝ) 8 \ {β}))) := by
    fun_prop
  have hcomp : Continuous (g ∘ f) := by
    have := hK.restrict.comp hj
    simpa [Function.comp_def, f, g, D, S, b, apm_t00a05_squareDecoder] using this
  simpa [g, S] using hquot.continuous_iff.mpr hcomp

lemma apm_t00a05_squareOfPerimeter_eq_of_rot_eq {β s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 8) (ht : t ∈ Set.Icc (0 : ℝ) 8)
    (hst : apm_t00a05_rot β s = apm_t00a05_rot β t) :
    apm_t00a05_squareOfPerimeter s =
      apm_t00a05_squareOfPerimeter t := by
  rcases hs with ⟨hs0, hs8⟩
  rcases ht with ⟨ht0, ht8⟩
  unfold apm_t00a05_rot at hst
  split_ifs at hst with hsβ htβ
  · rw [show s = t by linarith]
  · have hs0 : s = 0 := by linarith
    have ht8 : t = 8 := by linarith
    rw [hs0, ht8]
    norm_num [apm_t00a05_squareOfPerimeter]
  · have hs8 : s = 8 := by linarith
    have ht0 : t = 0 := by linarith
    rw [hs8, ht0]
    norm_num [apm_t00a05_squareOfPerimeter]
  · rw [show s = t by linarith]

lemma apm_t00a05_rot_square_chart_injective {β : ℝ} :
    Set.InjOn
      (fun q : ℝ × ℝ =>
        apm_t00a05_rot β (apm_t00a05_squarePerimeter q))
      (Metric.sphere (0 : ℝ × ℝ) 1) := by
  intro p hp q hq hpq
  have hdecoder := apm_t00a05_squareOfPerimeter_eq_of_rot_eq
    (apm_t00a05_squarePerimeter_mem_Icc hp)
    (apm_t00a05_squarePerimeter_mem_Icc hq) hpq
  simpa [apm_t00a05_squareOfPerimeter_squarePerimeter hp,
    apm_t00a05_squareOfPerimeter_squarePerimeter hq] using hdecoder

/-- A continuous simple closed traversal of the square sphere cannot miss a
point: puncturing at a hypothetical missed point puts the whole loop in the
real chart above, contradicting monotonicity of an injective real path. -/
lemma apm_t00a05_simple_loop_surj_square {c : ℝ → ℝ × ℝ} {T : ℝ}
    (hT : 0 < T) (hc : Continuous c)
    (hsphere : ∀ t ∈ Set.Icc (0 : ℝ) T,
      c t ∈ Metric.sphere (0 : ℝ × ℝ) 1)
    (hinj : Set.InjOn c (Set.Ico (0 : ℝ) T))
    (hclosed : c 0 = c T) :
    Set.SurjOn c (Set.Icc (0 : ℝ) T)
      (Metric.sphere (0 : ℝ × ℝ) 1) := by
  classical
  by_contra hsurj
  rw [Set.SurjOn, Set.not_subset] at hsurj
  obtain ⟨b, hb, hnotimage⟩ := hsurj
  have hmiss (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) : c t ≠ b := by
    intro htb
    exact hnotimage ⟨t, ht, htb⟩
  let s := apm_t00a05_squarePerimeter b
  have hsIcc : s ∈ Set.Icc (0 : ℝ) 8 :=
    apm_t00a05_squarePerimeter_mem_Icc hb
  let β : ℝ := if s = 0 then 8 else s
  have hβ0 : 0 < β := by
    dsimp [β]
    split_ifs with hs0
    · norm_num
    · exact lt_of_le_of_ne hsIcc.1 (Ne.symm hs0)
  have hβ8 : β ≤ 8 := by
    dsimp [β]
    split_ifs
    · norm_num
    · exact hsIcc.2
  have hdecode : apm_t00a05_squareOfPerimeter β = b := by
    dsimp [β]
    split_ifs with hs0
    · have h0 : apm_t00a05_squareOfPerimeter 0 = b := by
        change apm_t00a05_squarePerimeter b = 0 at hs0
        rw [← apm_t00a05_squareOfPerimeter_squarePerimeter hb, hs0]
      rw [← h0]
      norm_num [apm_t00a05_squareOfPerimeter]
    · exact apm_t00a05_squareOfPerimeter_squarePerimeter hb
  let r : ℝ → ℝ := fun t => max 0 (min T t)
  have hrcont : Continuous r := by
    dsimp [r]
    fun_prop
  have hrmem (t : ℝ) : r t ∈ Set.Icc (0 : ℝ) T := by
    dsimp [r]
    constructor
    · exact le_max_left _ _
    · rw [max_le_iff]
      exact ⟨hT.le, min_le_left _ _⟩
  have hr_eq {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) : r t = t := by
    simp [r, ht.1, ht.2]
  let q : ℝ → Metric.sphere (0 : ℝ × ℝ) 1 := fun t =>
    ⟨c (r t), hsphere (r t) (hrmem t)⟩
  have hqcont : Continuous q := by
    exact Continuous.subtype_mk (hc.comp hrcont) _
  have hqmiss (t : ℝ) : q t ≠
      (⟨apm_t00a05_squareOfPerimeter β,
        apm_t00a05_squareOfPerimeter_mem_sphere ⟨hβ0.le, hβ8⟩⟩ :
          Metric.sphere (0 : ℝ × ℝ) 1) := by
    intro heq
    apply hmiss (r t) (hrmem t)
    rw [← hdecode]
    exact congrArg Subtype.val heq
  let q' : ℝ → {z : Metric.sphere (0 : ℝ × ℝ) 1 |
      z.1 ≠ apm_t00a05_squareOfPerimeter β} := fun t =>
    ⟨q t, by
      intro heq
      exact hqmiss t (Subtype.ext heq)⟩
  have hq'cont : Continuous q' := Continuous.subtype_mk hqcont _
  let f : ℝ → ℝ := fun t =>
    apm_t00a05_rot β (apm_t00a05_squarePerimeter (q t).1)
  have hfcont : Continuous f := by
    exact (apm_t00a05_rot_square_chart_continuous hβ0 hβ8).comp hq'cont
  have hfinj : Set.InjOn f (Set.Ico (0 : ℝ) T) := by
    intro u hu v hv huv
    have hquv : (q u).1 = (q v).1 :=
      apm_t00a05_rot_square_chart_injective
        (hsphere (r u) (hrmem u)) (hsphere (r v) (hrmem v)) huv
    apply hinj hu hv
    simpa [q, hr_eq ⟨hu.1, hu.2.le⟩, hr_eq ⟨hv.1, hv.2.le⟩] using hquv
  have hfclosed : f 0 = f T := by
    simp only [f, q]
    rw [hr_eq ⟨le_rfl, hT.le⟩, hr_eq ⟨hT.le, le_rfl⟩, hclosed]
  exact apm_t00a05_no_continuous_real_simple_loop hT hfcont hfinj hfclosed

lemma apm_t00a05_C2_radialized_surjOn {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) :
    Set.SurjOn
      (fun t => apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1))
      (Set.Icc (0 : ℝ) (2 * Real.pi))
      (Metric.sphere (0 : ℝ × ℝ) 1) := by
  apply apm_t00a05_simple_loop_surj_square Real.two_pi_pos
    (apm_t00a05_C2_radialized_continuous hγ)
  · intro t ht
    exact apm_t00a05_C2_radialized_mem_sphere hγ ht.1 ht.2
  · exact apm_t00a05_C2_radialized_injOn hγ
  · exact apm_t00a05_C2_radialized_closed hγ

/-- Every point of the square sphere has one canonical preimage in the
half-open parameter period.  Moving a possible endpoint witness from `2π` to
`0` removes the sole duplication of the closed parametrization. -/
lemma apm_t00a05_C2_radialized_unique_on_Ico
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    {r : ℝ × ℝ} (hr : r ∈ Metric.sphere (0 : ℝ × ℝ) 1) :
    ∃! t : {t : ℝ // t ∈ Set.Ico (0 : ℝ) (2 * Real.pi)},
      apm_t00a05_radialHomeomorph ((γ t.1).1, (γ t.1).2.1) = r := by
  rcases apm_t00a05_C2_radialized_surjOn hγ hr with ⟨t, ht, htr⟩
  let u : ℝ := if t = 2 * Real.pi then 0 else t
  have hu : u ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    dsimp [u]
    split_ifs with heq
    · exact ⟨le_rfl, Real.two_pi_pos⟩
    · exact ⟨ht.1, lt_of_le_of_ne ht.2 heq⟩
  have hur : apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1) = r := by
    dsimp [u]
    split_ifs with heq
    · rw [apm_t00a05_C2_radialized_closed hγ, ← heq]
      exact htr
    · exact htr
  refine ⟨⟨u, hu⟩, hur, ?_⟩
  intro v hvr
  apply Subtype.ext
  exact (apm_t00a05_C2_radialized_injOn hγ hu v.2
    (hur.trans hvr.symm)).symm

/-- The canonical half-open-period time at which the radialized curve reaches
a prescribed square-sphere point. -/
noncomputable def apm_t00a05_radializedTime
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    (r : ℝ × ℝ) (hr : r ∈ Metric.sphere (0 : ℝ × ℝ) 1) :
    {t : ℝ // t ∈ Set.Ico (0 : ℝ) (2 * Real.pi)} :=
  Classical.choose (apm_t00a05_C2_radialized_unique_on_Ico hγ hr)

lemma apm_t00a05_radializedTime_spec
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    (r : ℝ × ℝ) (hr : r ∈ Metric.sphere (0 : ℝ × ℝ) 1) :
    apm_t00a05_radialHomeomorph
        ((γ (apm_t00a05_radializedTime hγ r hr).1).1,
          (γ (apm_t00a05_radializedTime hγ r hr).1).2.1) = r :=
  Classical.choose_spec
    (apm_t00a05_C2_radialized_unique_on_Ico hγ hr) |>.1

lemma apm_t00a05_radializedTime_perimeter
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    (r : ℝ × ℝ) (hr : r ∈ Metric.sphere (0 : ℝ × ℝ) 1) :
    apm_t00a05_squarePerimeter
        (apm_t00a05_radialHomeomorph
          ((γ (apm_t00a05_radializedTime hγ r hr).1).1,
            (γ (apm_t00a05_radializedTime hγ r hr).1).2.1)) =
      apm_t00a05_squarePerimeter r := by
  rw [apm_t00a05_radializedTime_spec hγ r hr]

lemma apm_t00a05_radializedTime_eq_iff
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    (r : ℝ × ℝ) (hr : r ∈ Metric.sphere (0 : ℝ × ℝ) 1)
    (t : {t : ℝ // t ∈ Set.Ico (0 : ℝ) (2 * Real.pi)}) :
    t = apm_t00a05_radializedTime hγ r hr ↔
      apm_t00a05_radialHomeomorph ((γ t.1).1, (γ t.1).2.1) = r := by
  constructor
  · rintro rfl
    exact apm_t00a05_radializedTime_spec hγ r hr
  · intro ht
    exact Classical.choose_spec
      (apm_t00a05_C2_radialized_unique_on_Ico hγ hr) |>.2 t ht

lemma apm_t00a05_radializedTime_ne_of_ne
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    {r s : ℝ × ℝ} (hr : r ∈ Metric.sphere (0 : ℝ × ℝ) 1)
    (hs : s ∈ Metric.sphere (0 : ℝ × ℝ) 1) (hrs : r ≠ s) :
    apm_t00a05_radializedTime hγ r hr ≠
      apm_t00a05_radializedTime hγ s hs := by
  intro htime
  apply hrs
  rw [← apm_t00a05_radializedTime_spec hγ r hr,
    ← apm_t00a05_radializedTime_spec hγ s hs, htime]

lemma apm_t00a05_cornerBR_mem_sphere :
    ((1, -1) : ℝ × ℝ) ∈ Metric.sphere (0 : ℝ × ℝ) 1 := by
  rw [apm_t00a05_mem_supSphere_iff]
  norm_num

lemma apm_t00a05_cornerTR_mem_sphere :
    ((1, 1) : ℝ × ℝ) ∈ Metric.sphere (0 : ℝ × ℝ) 1 := by
  rw [apm_t00a05_mem_supSphere_iff]
  norm_num

lemma apm_t00a05_cornerTL_mem_sphere :
    ((-1, 1) : ℝ × ℝ) ∈ Metric.sphere (0 : ℝ × ℝ) 1 := by
  rw [apm_t00a05_mem_supSphere_iff]
  norm_num

lemma apm_t00a05_cornerBL_mem_sphere :
    ((-1, -1) : ℝ × ℝ) ∈ Metric.sphere (0 : ℝ × ℝ) 1 := by
  rw [apm_t00a05_mem_supSphere_iff]
  norm_num

noncomputable def apm_t00a05_cornerBRTime
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :=
  apm_t00a05_radializedTime hγ (1, -1) apm_t00a05_cornerBR_mem_sphere

noncomputable def apm_t00a05_cornerTRTime
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :=
  apm_t00a05_radializedTime hγ (1, 1) apm_t00a05_cornerTR_mem_sphere

noncomputable def apm_t00a05_cornerTLTime
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :=
  apm_t00a05_radializedTime hγ (-1, 1) apm_t00a05_cornerTL_mem_sphere

noncomputable def apm_t00a05_cornerBLTime
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :=
  apm_t00a05_radializedTime hγ (-1, -1) apm_t00a05_cornerBL_mem_sphere

lemma apm_t00a05_cornerTimes_pairwise_ne
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :
    apm_t00a05_cornerBRTime hγ ≠ apm_t00a05_cornerTRTime hγ ∧
    apm_t00a05_cornerBRTime hγ ≠ apm_t00a05_cornerTLTime hγ ∧
    apm_t00a05_cornerBRTime hγ ≠ apm_t00a05_cornerBLTime hγ ∧
    apm_t00a05_cornerTRTime hγ ≠ apm_t00a05_cornerTLTime hγ ∧
    apm_t00a05_cornerTRTime hγ ≠ apm_t00a05_cornerBLTime hγ ∧
    apm_t00a05_cornerTLTime hγ ≠ apm_t00a05_cornerBLTime hγ := by
  unfold apm_t00a05_cornerBRTime apm_t00a05_cornerTRTime
    apm_t00a05_cornerTLTime apm_t00a05_cornerBLTime
  repeat' apply And.intro
  all_goals
    apply apm_t00a05_radializedTime_ne_of_ne hγ <;> norm_num

lemma apm_t00a05_cornerTimes_perimeter_coordinates
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :
    apm_t00a05_squarePerimeter
        (apm_t00a05_radialHomeomorph
          ((γ (apm_t00a05_cornerBRTime hγ).1).1,
            (γ (apm_t00a05_cornerBRTime hγ).1).2.1)) = 2 ∧
    apm_t00a05_squarePerimeter
        (apm_t00a05_radialHomeomorph
          ((γ (apm_t00a05_cornerTRTime hγ).1).1,
            (γ (apm_t00a05_cornerTRTime hγ).1).2.1)) = 4 ∧
    apm_t00a05_squarePerimeter
        (apm_t00a05_radialHomeomorph
          ((γ (apm_t00a05_cornerTLTime hγ).1).1,
            (γ (apm_t00a05_cornerTLTime hγ).1).2.1)) = 6 ∧
    apm_t00a05_squarePerimeter
        (apm_t00a05_radialHomeomorph
          ((γ (apm_t00a05_cornerBLTime hγ).1).1,
            (γ (apm_t00a05_cornerBLTime hγ).1).2.1)) = 0 := by
  unfold apm_t00a05_cornerBRTime apm_t00a05_cornerTRTime
    apm_t00a05_cornerTLTime apm_t00a05_cornerBLTime
  rw [apm_t00a05_radializedTime_perimeter,
    apm_t00a05_radializedTime_perimeter,
    apm_t00a05_radializedTime_perimeter,
    apm_t00a05_radializedTime_perimeter]
  norm_num [apm_t00a05_squarePerimeter]

/-- Positive orientation has a witness away from all four square corners.
Those four canonical times are null sets, so they cannot account for a
positive signed-area integral. -/
lemma apm_t00a05_exists_angularDensity_pos_off_corners
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :
    ∃ t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi),
      t ≠ (apm_t00a05_cornerBRTime hγ).1 ∧
      t ≠ (apm_t00a05_cornerTRTime hγ).1 ∧
      t ≠ (apm_t00a05_cornerTLTime hγ).1 ∧
      t ≠ (apm_t00a05_cornerBLTime hγ).1 ∧
      0 < apm_t00a05_angularDensity γ t := by
  let corners : Set ℝ :=
    {(apm_t00a05_cornerBRTime hγ).1,
     (apm_t00a05_cornerTRTime hγ).1,
     (apm_t00a05_cornerTLTime hγ).1,
     (apm_t00a05_cornerBLTime hγ).1}
  have hcorners : volume corners = 0 := by
    have hfinite : corners.Finite := by simp [corners]
    exact hfinite.measure_zero volume
  by_contra h
  have hnonpos {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi))
      (htc : t ∉ corners) : apm_t00a05_angularDensity γ t ≤ 0 := by
    apply le_of_not_gt
    intro hpos
    apply h
    simp only [corners, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or, not_false_eq_true] at htc
    exact ⟨t, ht, htc.1, htc.2.1, htc.2.2.1, htc.2.2.2, hpos⟩
  have harea_nonpos :
      ∫ t in Set.Icc (0 : ℝ) (2 * Real.pi),
          (γ t).1 * deriv (fun s => (γ s).2.1) t -
            (γ t).2.1 * deriv (fun s => (γ s).1) t ≤ 0 := by
    rw [integral_Icc_eq_integral_Ioo]
    apply integral_nonpos_of_ae
    have hae_corners : ∀ᵐ t ∂volume.restrict
        (Set.Ioo (0 : ℝ) (2 * Real.pi)), t ∉ corners := by
      rw [ae_iff]
      have hmeas : MeasurableSet corners := by
        simp [corners]
      rw [show {t : ℝ | ¬t ∉ corners} = corners by ext t; simp,
        Measure.restrict_apply hmeas]
      exact measure_mono_null Set.inter_subset_left hcorners
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hae_corners] with t ht htc
    have ht' : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨ht.1.le, ht.2.le⟩
    rw [apm_t00a05_signedAreaDensity_eq_radius_sq_mul_angularDensity hγ ht']
    exact mul_nonpos_of_nonneg_of_nonpos
      (apm_t00a05_projected_radius_sq_pos hγ ht').le (hnonpos ht htc)
  exact (not_lt_of_ge harea_nonpos) hγ.2.2.2.2

lemma apm_t00a05_exists_angularDensity_pos_on_open_edge
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :
    ∃ t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi),
      let q := apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)
      ((q.2 = -1 ∧ -1 < q.1 ∧ q.1 < 1) ∨
       (q.1 = 1 ∧ -1 < q.2 ∧ q.2 < 1) ∨
       (q.2 = 1 ∧ -1 < q.1 ∧ q.1 < 1) ∨
       (q.1 = -1 ∧ -1 < q.2 ∧ q.2 < 1)) ∧
      0 < apm_t00a05_angularDensity γ t := by
  rcases apm_t00a05_exists_angularDensity_pos_off_corners hγ with
    ⟨t, ht, hbr, htr, htl, hbl, hpos⟩
  let q := apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)
  have qt_ne (r : ℝ × ℝ) (hr : r ∈ Metric.sphere (0 : ℝ × ℝ) 1)
      (htime : t ≠ (apm_t00a05_radializedTime hγ r hr).1) : q ≠ r := by
    intro hqr
    apply htime
    have heq : (⟨t, ⟨ht.1.le, ht.2⟩⟩ :
        {u : ℝ // u ∈ Set.Ico (0 : ℝ) (2 * Real.pi)}) =
        apm_t00a05_radializedTime hγ r hr :=
      (apm_t00a05_radializedTime_eq_iff hγ r hr _).mpr hqr
    exact congrArg Subtype.val heq
  have hqcorners : q ≠ (1, -1) ∧ q ≠ (1, 1) ∧
      q ≠ (-1, 1) ∧ q ≠ (-1, -1) := by
    unfold apm_t00a05_cornerBRTime at hbr
    unfold apm_t00a05_cornerTRTime at htr
    unfold apm_t00a05_cornerTLTime at htl
    unfold apm_t00a05_cornerBLTime at hbl
    exact ⟨qt_ne _ apm_t00a05_cornerBR_mem_sphere hbr,
      qt_ne _ apm_t00a05_cornerTR_mem_sphere htr,
      qt_ne _ apm_t00a05_cornerTL_mem_sphere htl,
      qt_ne _ apm_t00a05_cornerBL_mem_sphere hbl⟩
  refine ⟨t, ht, ?_, hpos⟩
  exact apm_t00a05_supSphere_open_edge_of_not_corner
    (apm_t00a05_C2_radialized_mem_sphere hγ ht.1.le ht.2.le) hqcorners

lemma apm_t00a05_radialHomeomorph_eq_axis {p r : ℝ × ℝ}
    (h : apm_t00a05_radialHomeomorph p = r) :
    (r.1 ≠ 0 → r.2 = 0 → p.2 = 0) ∧
      (r.2 ≠ 0 → r.1 = 0 → p.1 = 0) := by
  rw [apm_t00a05_radialHomeomorph_apply] at h
  let a := gauge apm_t00a05_region p /
    gauge (Metric.ball (0 : ℝ × ℝ) 1) p
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  change a * p.1 = r.1 at hx
  change a * p.2 = r.2 at hy
  constructor
  · intro hrx hry
    have ha : a ≠ 0 := by
      intro ha
      rw [ha, zero_mul] at hx
      exact hrx hx.symm
    rw [hry] at hy
    exact (mul_eq_zero.mp hy).resolve_left ha
  · intro hry hrx
    have ha : a ≠ 0 := by
      intro ha
      rw [ha, zero_mul] at hy
      exact hry hy.symm
    rw [hrx] at hx
    exact (mul_eq_zero.mp hx).resolve_left ha

lemma apm_t00a05_radialHomeomorph_scale_pos {p : ℝ × ℝ}
    (hp : p ∈ frontier apm_t00a05_region) :
    0 < gauge apm_t00a05_region p /
      gauge (Metric.ball (0 : ℝ × ℝ) 1) p := by
  have hpne : p ≠ 0 := by
    intro hp0
    have := apm_t00a05_mem_frontier_level_eq_ten hp
    rw [hp0] at this
    norm_num [apm_t00a05_level] at this
  apply div_pos
  · exact (gauge_pos (absorbent_nhds_zero apm_t00a05_region_mem_nhds_zero)
      (NormedSpace.isVonNBounded_of_isBounded ℝ
        apm_t00a05_region_isBounded)).2 hpne
  · exact (gauge_pos
      (absorbent_nhds_zero
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one)))
      (NormedSpace.isVonNBounded_ball ℝ (ℝ × ℝ) 1)).2 hpne

lemma apm_t00a05_radialHomeomorph_ratio_yx {p : ℝ × ℝ}
    (hp : p ∈ frontier apm_t00a05_region) (hx : p.1 ≠ 0) :
    (apm_t00a05_radialHomeomorph p).2 /
        (apm_t00a05_radialHomeomorph p).1 = p.2 / p.1 := by
  have ha := (apm_t00a05_radialHomeomorph_scale_pos hp).ne'
  rw [apm_t00a05_radialHomeomorph_apply]
  change ((gauge apm_t00a05_region p / gauge (Metric.ball 0 1) p) * p.2) /
      ((gauge apm_t00a05_region p / gauge (Metric.ball 0 1) p) * p.1) = p.2 / p.1
  exact mul_div_mul_left _ _ ha

lemma apm_t00a05_radialHomeomorph_ratio_xy {p : ℝ × ℝ}
    (hp : p ∈ frontier apm_t00a05_region) (hy : p.2 ≠ 0) :
    (apm_t00a05_radialHomeomorph p).1 /
        (apm_t00a05_radialHomeomorph p).2 = p.1 / p.2 := by
  have ha := (apm_t00a05_radialHomeomorph_scale_pos hp).ne'
  rw [apm_t00a05_radialHomeomorph_apply]
  change ((gauge apm_t00a05_region p / gauge (Metric.ball 0 1) p) * p.1) /
      ((gauge apm_t00a05_region p / gauge (Metric.ball 0 1) p) * p.2) = p.1 / p.2
  exact mul_div_mul_left _ _ ha

lemma apm_t00a05_radialHomeomorph_fst_ne_zero_iff {p : ℝ × ℝ}
    (hp : p ∈ frontier apm_t00a05_region) :
    (apm_t00a05_radialHomeomorph p).1 ≠ 0 ↔ p.1 ≠ 0 := by
  rw [apm_t00a05_radialHomeomorph_apply]
  change (gauge apm_t00a05_region p / gauge (Metric.ball 0 1) p) * p.1 ≠ 0 ↔ _
  rw [mul_ne_zero_iff]
  simp [(apm_t00a05_radialHomeomorph_scale_pos hp).ne']

lemma apm_t00a05_radialHomeomorph_snd_ne_zero_iff {p : ℝ × ℝ}
    (hp : p ∈ frontier apm_t00a05_region) :
    (apm_t00a05_radialHomeomorph p).2 ≠ 0 ↔ p.2 ≠ 0 := by
  rw [apm_t00a05_radialHomeomorph_apply]
  change (gauge apm_t00a05_region p / gauge (Metric.ball 0 1) p) * p.2 ≠ 0 ↔ _
  rw [mul_ne_zero_iff]
  simp [(apm_t00a05_radialHomeomorph_scale_pos hp).ne']

lemma apm_t00a05_squareAngle_radialized_right_open {p : ℝ × ℝ}
    (hp : p ∈ frontier apm_t00a05_region)
    (hx : (apm_t00a05_radialHomeomorph p).1 = 1)
    (hy0 : -1 < (apm_t00a05_radialHomeomorph p).2)
    (hy1 : (apm_t00a05_radialHomeomorph p).2 < 1) :
    apm_t00a05_squareAngle
        (apm_t00a05_squarePerimeter (apm_t00a05_radialHomeomorph p)) =
      Real.arctan (p.2 / p.1) + 2 * Real.pi := by
  rw [apm_t00a05_squareAngle_perimeter_right_open hx hy0 hy1]
  rw [apm_t00a05_radialHomeomorph_ratio_yx hp
    ((apm_t00a05_radialHomeomorph_fst_ne_zero_iff hp).mp (by simp [hx]))]

lemma apm_t00a05_squareAngle_radialized_left_open {p : ℝ × ℝ}
    (hp : p ∈ frontier apm_t00a05_region)
    (hx : (apm_t00a05_radialHomeomorph p).1 = -1)
    (hy0 : -1 < (apm_t00a05_radialHomeomorph p).2)
    (hy1 : (apm_t00a05_radialHomeomorph p).2 < 1) :
    apm_t00a05_squareAngle
        (apm_t00a05_squarePerimeter (apm_t00a05_radialHomeomorph p)) =
      Real.arctan (p.2 / p.1) + 3 * Real.pi := by
  rw [apm_t00a05_squareAngle_perimeter_left_open hx hy0 hy1]
  rw [apm_t00a05_radialHomeomorph_ratio_yx hp
    ((apm_t00a05_radialHomeomorph_fst_ne_zero_iff hp).mp (by simp [hx]))]

lemma apm_t00a05_squareAngle_radialized_bottom_open {p : ℝ × ℝ}
    (hp : p ∈ frontier apm_t00a05_region)
    (hy : (apm_t00a05_radialHomeomorph p).2 = -1)
    (hx0 : -1 < (apm_t00a05_radialHomeomorph p).1)
    (hx1 : (apm_t00a05_radialHomeomorph p).1 < 1) :
    apm_t00a05_squareAngle
        (apm_t00a05_squarePerimeter (apm_t00a05_radialHomeomorph p)) =
      -Real.arctan (p.1 / p.2) + 3 * Real.pi / 2 := by
  rw [apm_t00a05_squareAngle_perimeter_bottom_open hy hx0 hx1]
  rw [apm_t00a05_radialHomeomorph_ratio_xy hp
    ((apm_t00a05_radialHomeomorph_snd_ne_zero_iff hp).mp (by simp [hy]))]

lemma apm_t00a05_squareAngle_radialized_top_open {p : ℝ × ℝ}
    (hp : p ∈ frontier apm_t00a05_region)
    (hy : (apm_t00a05_radialHomeomorph p).2 = 1)
    (hx0 : -1 < (apm_t00a05_radialHomeomorph p).1)
    (hx1 : (apm_t00a05_radialHomeomorph p).1 < 1) :
    apm_t00a05_squareAngle
        (apm_t00a05_squarePerimeter (apm_t00a05_radialHomeomorph p)) =
      -Real.arctan (p.1 / p.2) + 5 * Real.pi / 2 := by
  rw [apm_t00a05_squareAngle_perimeter_top_open hy hx0 hx1]
  rw [apm_t00a05_radialHomeomorph_ratio_xy hp
    ((apm_t00a05_radialHomeomorph_snd_ne_zero_iff hp).mp (by simp [hy]))]

lemma apm_t00a05_radialized_eventually_right_open
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi))
    (hx : (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).1 = 1)
    (hy0 : -1 < (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).2)
    (hy1 : (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).2 < 1) :
    ∀ᶠ u in nhds t,
      (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)).1 = 1 ∧
      -1 < (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)).2 ∧
      (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)).2 < 1 := by
  let q : ℝ → ℝ × ℝ := fun u =>
    apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)
  have hqc : Continuous q := apm_t00a05_C2_radialized_continuous hγ
  have hpos : {u | 0 < (q u).1} ∈ nhds t :=
    (isOpen_lt continuous_const hqc.fst).mem_nhds (by simpa [q, hx])
  have hlo : {u | -1 < (q u).2} ∈ nhds t :=
    (isOpen_lt continuous_const hqc.snd).mem_nhds (by simpa [q] using hy0)
  have hhi : {u | (q u).2 < 1} ∈ nhds t :=
    (isOpen_lt hqc.snd continuous_const).mem_nhds (by simpa [q] using hy1)
  have hperiod : Set.Ioo (0 : ℝ) (2 * Real.pi) ∈ nhds t :=
    isOpen_Ioo.mem_nhds ht
  filter_upwards [hpos, hlo, hhi, hperiod] with u hux huy0 huy1 hu
  have hs := apm_t00a05_C2_radialized_mem_sphere hγ hu.1.le hu.2.le
  rcases apm_t00a05_supSphere_on_edge hs with hxm | hxp | hym | hyp
  · exfalso; linarith
  · exact ⟨hxp, huy0, huy1⟩
  · exfalso; linarith
  · exfalso; linarith

lemma apm_t00a05_radialized_eventually_left_open
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi))
    (hx : (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).1 = -1)
    (hy0 : -1 < (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).2)
    (hy1 : (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).2 < 1) :
    ∀ᶠ u in nhds t,
      (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)).1 = -1 ∧
      -1 < (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)).2 ∧
      (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)).2 < 1 := by
  let q : ℝ → ℝ × ℝ := fun u =>
    apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)
  have hqc : Continuous q := apm_t00a05_C2_radialized_continuous hγ
  have hneg : {u | (q u).1 < 0} ∈ nhds t :=
    (isOpen_lt hqc.fst continuous_const).mem_nhds (by simpa [q, hx])
  have hlo : {u | -1 < (q u).2} ∈ nhds t :=
    (isOpen_lt continuous_const hqc.snd).mem_nhds (by simpa [q] using hy0)
  have hhi : {u | (q u).2 < 1} ∈ nhds t :=
    (isOpen_lt hqc.snd continuous_const).mem_nhds (by simpa [q] using hy1)
  have hperiod : Set.Ioo (0 : ℝ) (2 * Real.pi) ∈ nhds t :=
    isOpen_Ioo.mem_nhds ht
  filter_upwards [hneg, hlo, hhi, hperiod] with u hux huy0 huy1 hu
  have hs := apm_t00a05_C2_radialized_mem_sphere hγ hu.1.le hu.2.le
  rcases apm_t00a05_supSphere_on_edge hs with hxm | hxp | hym | hyp
  · exact ⟨hxm, huy0, huy1⟩
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith

lemma apm_t00a05_radialized_eventually_bottom_open
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi))
    (hy : (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).2 = -1)
    (hx0 : -1 < (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).1)
    (hx1 : (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).1 < 1) :
    ∀ᶠ u in nhds t,
      (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)).2 = -1 ∧
      -1 < (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)).1 ∧
      (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)).1 < 1 := by
  let q : ℝ → ℝ × ℝ := fun u =>
    apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)
  have hqc : Continuous q := apm_t00a05_C2_radialized_continuous hγ
  have hneg : {u | (q u).2 < 0} ∈ nhds t :=
    (isOpen_lt hqc.snd continuous_const).mem_nhds (by simpa [q, hy])
  have hlo : {u | -1 < (q u).1} ∈ nhds t :=
    (isOpen_lt continuous_const hqc.fst).mem_nhds (by simpa [q] using hx0)
  have hhi : {u | (q u).1 < 1} ∈ nhds t :=
    (isOpen_lt hqc.fst continuous_const).mem_nhds (by simpa [q] using hx1)
  have hperiod : Set.Ioo (0 : ℝ) (2 * Real.pi) ∈ nhds t :=
    isOpen_Ioo.mem_nhds ht
  filter_upwards [hneg, hlo, hhi, hperiod] with u huy hux0 hux1 hu
  have hs := apm_t00a05_C2_radialized_mem_sphere hγ hu.1.le hu.2.le
  rcases apm_t00a05_supSphere_on_edge hs with hxm | hxp | hym | hyp
  · exfalso; linarith
  · exfalso; linarith
  · exact ⟨hym, hux0, hux1⟩
  · exfalso; linarith

lemma apm_t00a05_radialized_eventually_top_open
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi))
    (hy : (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).2 = 1)
    (hx0 : -1 < (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).1)
    (hx1 : (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).1 < 1) :
    ∀ᶠ u in nhds t,
      (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)).2 = 1 ∧
      -1 < (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)).1 ∧
      (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)).1 < 1 := by
  let q : ℝ → ℝ × ℝ := fun u =>
    apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)
  have hqc : Continuous q := apm_t00a05_C2_radialized_continuous hγ
  have hpos : {u | 0 < (q u).2} ∈ nhds t :=
    (isOpen_lt continuous_const hqc.snd).mem_nhds (by simpa [q, hy])
  have hlo : {u | -1 < (q u).1} ∈ nhds t :=
    (isOpen_lt continuous_const hqc.fst).mem_nhds (by simpa [q] using hx0)
  have hhi : {u | (q u).1 < 1} ∈ nhds t :=
    (isOpen_lt hqc.fst continuous_const).mem_nhds (by simpa [q] using hx1)
  have hperiod : Set.Ioo (0 : ℝ) (2 * Real.pi) ∈ nhds t :=
    isOpen_Ioo.mem_nhds ht
  filter_upwards [hpos, hlo, hhi, hperiod] with u huy hux0 hux1 hu
  have hs := apm_t00a05_C2_radialized_mem_sphere hγ hu.1.le hu.2.le
  rcases apm_t00a05_supSphere_on_edge hs with hxm | hxp | hym | hyp
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
  · exact ⟨hyp, hux0, hux1⟩

lemma apm_t00a05_raw_radial_angle_deriv_of_right_open
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi))
    (hx : (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).1 = 1)
    (hy0 : -1 < (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).2)
    (hy1 : (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).2 < 1) :
    deriv (fun u => apm_t00a05_squareAngle
      (apm_t00a05_squarePerimeter
        (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)))) t =
      apm_t00a05_angularDensity γ t := by
  have hedge := apm_t00a05_radialized_eventually_right_open hγ ht hx hy0 hy1
  have hperiod : Set.Ioo (0 : ℝ) (2 * Real.pi) ∈ nhds t :=
    isOpen_Ioo.mem_nhds ht
  have hev :
      (fun u => apm_t00a05_squareAngle
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)))) =ᶠ[nhds t]
      (fun u => Real.arctan ((γ u).2.1 / (γ u).1) + 2 * Real.pi) := by
    filter_upwards [hedge, hperiod] with u hu hup
    exact apm_t00a05_squareAngle_radialized_right_open
      (apm_t00a05_C2_projection_mem_frontier hγ hup.1.le hup.2.le)
      hu.1 hu.2.1 hu.2.2
  rw [hev.deriv_eq, deriv_add_const,
    apm_t00a05_angle_primitive_deriv hγ.1]
  · rfl
  · exact (apm_t00a05_radialHomeomorph_fst_ne_zero_iff
      (apm_t00a05_C2_projection_mem_frontier hγ ht.1.le ht.2.le)).mp
        (by simp [hx])

lemma apm_t00a05_raw_radial_angle_deriv_of_left_open
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi))
    (hx : (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).1 = -1)
    (hy0 : -1 < (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).2)
    (hy1 : (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).2 < 1) :
    deriv (fun u => apm_t00a05_squareAngle
      (apm_t00a05_squarePerimeter
        (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)))) t =
      apm_t00a05_angularDensity γ t := by
  have hedge := apm_t00a05_radialized_eventually_left_open hγ ht hx hy0 hy1
  have hperiod : Set.Ioo (0 : ℝ) (2 * Real.pi) ∈ nhds t :=
    isOpen_Ioo.mem_nhds ht
  have hev :
      (fun u => apm_t00a05_squareAngle
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)))) =ᶠ[nhds t]
      (fun u => Real.arctan ((γ u).2.1 / (γ u).1) + 3 * Real.pi) := by
    filter_upwards [hedge, hperiod] with u hu hup
    exact apm_t00a05_squareAngle_radialized_left_open
      (apm_t00a05_C2_projection_mem_frontier hγ hup.1.le hup.2.le)
      hu.1 hu.2.1 hu.2.2
  rw [hev.deriv_eq, deriv_add_const,
    apm_t00a05_angle_primitive_deriv hγ.1]
  · rfl
  · exact (apm_t00a05_radialHomeomorph_fst_ne_zero_iff
      (apm_t00a05_C2_projection_mem_frontier hγ ht.1.le ht.2.le)).mp
        (by simp [hx])

lemma apm_t00a05_raw_radial_angle_deriv_of_bottom_open
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi))
    (hy : (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).2 = -1)
    (hx0 : -1 < (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).1)
    (hx1 : (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).1 < 1) :
    deriv (fun u => apm_t00a05_squareAngle
      (apm_t00a05_squarePerimeter
        (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)))) t =
      apm_t00a05_angularDensity γ t := by
  have hedge := apm_t00a05_radialized_eventually_bottom_open hγ ht hy hx0 hx1
  have hperiod : Set.Ioo (0 : ℝ) (2 * Real.pi) ∈ nhds t :=
    isOpen_Ioo.mem_nhds ht
  have hev :
      (fun u => apm_t00a05_squareAngle
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)))) =ᶠ[nhds t]
      (fun u => -Real.arctan ((γ u).1 / (γ u).2.1) + 3 * Real.pi / 2) := by
    filter_upwards [hedge, hperiod] with u hu hup
    exact apm_t00a05_squareAngle_radialized_bottom_open
      (apm_t00a05_C2_projection_mem_frontier hγ hup.1.le hup.2.le)
      hu.1 hu.2.1 hu.2.2
  rw [hev.deriv_eq, deriv_add_const,
    apm_t00a05_angle_primitive_deriv_y hγ.1]
  · rfl
  · exact (apm_t00a05_radialHomeomorph_snd_ne_zero_iff
      (apm_t00a05_C2_projection_mem_frontier hγ ht.1.le ht.2.le)).mp
        (by simp [hy])

lemma apm_t00a05_raw_radial_angle_deriv_of_top_open
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi))
    (hy : (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).2 = 1)
    (hx0 : -1 < (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).1)
    (hx1 : (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)).1 < 1) :
    deriv (fun u => apm_t00a05_squareAngle
      (apm_t00a05_squarePerimeter
        (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)))) t =
      apm_t00a05_angularDensity γ t := by
  have hedge := apm_t00a05_radialized_eventually_top_open hγ ht hy hx0 hx1
  have hperiod : Set.Ioo (0 : ℝ) (2 * Real.pi) ∈ nhds t :=
    isOpen_Ioo.mem_nhds ht
  have hev :
      (fun u => apm_t00a05_squareAngle
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)))) =ᶠ[nhds t]
      (fun u => -Real.arctan ((γ u).1 / (γ u).2.1) + 5 * Real.pi / 2) := by
    filter_upwards [hedge, hperiod] with u hu hup
    exact apm_t00a05_squareAngle_radialized_top_open
      (apm_t00a05_C2_projection_mem_frontier hγ hup.1.le hup.2.le)
      hu.1 hu.2.1 hu.2.2
  rw [hev.deriv_eq, deriv_add_const,
    apm_t00a05_angle_primitive_deriv_y hγ.1]
  · rfl
  · exact (apm_t00a05_radialHomeomorph_snd_ne_zero_iff
      (apm_t00a05_C2_projection_mem_frontier hγ ht.1.le ht.2.le)).mp
        (by simp [hy])

lemma apm_t00a05_exists_raw_radial_angle_deriv_pos
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :
    ∃ t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi),
      0 < deriv (fun u => apm_t00a05_squareAngle
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)))) t := by
  rcases apm_t00a05_exists_angularDensity_pos_on_open_edge hγ with
    ⟨t, ht, hedge, hpos⟩
  refine ⟨t, ht, ?_⟩
  rcases hedge with hbottom | hright | htop | hleft
  · rw [apm_t00a05_raw_radial_angle_deriv_of_bottom_open hγ ht
      hbottom.1 hbottom.2.1 hbottom.2.2]
    exact hpos
  · rw [apm_t00a05_raw_radial_angle_deriv_of_right_open hγ ht
      hright.1 hright.2.1 hright.2.2]
    exact hpos
  · rw [apm_t00a05_raw_radial_angle_deriv_of_top_open hγ ht
      htop.1 htop.2.1 htop.2.2]
    exact hpos
  · rw [apm_t00a05_raw_radial_angle_deriv_of_left_open hγ ht
      hleft.1 hleft.2.1 hleft.2.2]
    exact hpos

lemma apm_t00a05_corrected_lift_deriv_eq_raw_of_raw_deriv_pos
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    {β t : ℝ} (hβ0 : 0 < β) (hβ8 : β ≤ 8)
    (hdecode : apm_t00a05_squareOfPerimeter β =
      apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1))
    (ht : t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi))
    (hpos : 0 < deriv (fun u => apm_t00a05_squareAngle
      (apm_t00a05_squarePerimeter
        (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)))) t) :
    deriv (fun u => apm_t00a05_squareAngleFrom β
      (apm_t00a05_rot β
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1))))) t =
    deriv (fun u => apm_t00a05_squareAngle
      (apm_t00a05_squarePerimeter
        (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)))) t := by
  let p : ℝ → ℝ := fun u => apm_t00a05_squarePerimeter
    (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1))
  let raw : ℝ → ℝ := fun u => apm_t00a05_squareAngle (p u)
  let lift : ℝ → ℝ := fun u =>
    apm_t00a05_squareAngleFrom β (apm_t00a05_rot β (p u))
  have hpIcc (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
      p u ∈ Set.Icc (0 : ℝ) 8 :=
    apm_t00a05_squarePerimeter_mem_Icc
      (apm_t00a05_C2_radialized_mem_sphere hγ hu.1 hu.2)
  have hpne : p t ≠ β := by
    intro hper
    have hsphere := apm_t00a05_C2_radialized_mem_sphere hγ ht.1.le ht.2.le
    have hpoint :
        apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1) =
          apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1) := by
      rw [← hdecode, ← hper]
      exact (apm_t00a05_squareOfPerimeter_squarePerimeter hsphere).symm
    have ht0 := apm_t00a05_C2_radialized_injOn hγ
      ⟨ht.1.le, ht.2⟩ ⟨le_rfl, Real.two_pi_pos⟩ hpoint
    exact ht.1.ne' ht0
  have hrawdiff : DifferentiableAt ℝ raw t := by
    apply differentiableAt_of_deriv_ne_zero
    simpa [raw, p] using hpos.ne'
  have hperiod : Set.Ioo (0 : ℝ) (2 * Real.pi) ∈ nhds t :=
    isOpen_Ioo.mem_nhds ht
  rcases lt_or_gt_of_ne hpne with hlt | hgt
  · have hrawlt : raw t < apm_t00a05_squareAngle β :=
      apm_t00a05_squareAngle_strictMonoOn
        (hpIcc t ⟨ht.1.le, ht.2.le⟩) ⟨hβ0.le, hβ8⟩ hlt
    have hevent : {u | raw u < apm_t00a05_squareAngle β} ∈ nhds t :=
      hrawdiff.continuousAt.eventually_lt_const hrawlt
    have hev : lift =ᶠ[nhds t] (fun u => raw u + 2 * Real.pi) := by
      filter_upwards [hevent, hperiod] with u hru hu
      have hpu : p u < β := by
        by_contra hn
        have hle : β ≤ p u := le_of_not_gt hn
        have hang := apm_t00a05_squareAngle_strictMonoOn.monotoneOn
          ⟨hβ0.le, hβ8⟩ (hpIcc u ⟨hu.1.le, hu.2.le⟩) hle
        exact (not_lt_of_ge hang) hru
      simpa [lift, raw] using
        apm_t00a05_squareAngleFrom_rot hβ0 hβ8
          (hpIcc u ⟨hu.1.le, hu.2.le⟩) |>.trans (if_pos hpu)
    simpa [lift, raw, p, deriv_add_const] using hev.deriv_eq
  · have hrawgt : apm_t00a05_squareAngle β < raw t :=
      apm_t00a05_squareAngle_strictMonoOn
        ⟨hβ0.le, hβ8⟩ (hpIcc t ⟨ht.1.le, ht.2.le⟩) hgt
    have hevent : {u | apm_t00a05_squareAngle β < raw u} ∈ nhds t :=
      hrawdiff.continuousAt.eventually_const_lt hrawgt
    have hev : lift =ᶠ[nhds t] raw := by
      filter_upwards [hevent, hperiod] with u hru hu
      have hpu : ¬p u < β := by
        intro h
        have hang := apm_t00a05_squareAngle_strictMonoOn.monotoneOn
          (hpIcc u ⟨hu.1.le, hu.2.le⟩) ⟨hβ0.le, hβ8⟩ h.le
        exact (not_lt_of_ge hang) hru
      simpa [lift, raw] using
        apm_t00a05_squareAngleFrom_rot hβ0 hβ8
          (hpIcc u ⟨hu.1.le, hu.2.le⟩) |>.trans (if_neg hpu)
    simpa [lift, raw, p] using hev.deriv_eq

/-- Positive radial rescaling transfers both coordinate signs from a square
sphere point to its canonical preimage on the original level-set curve. -/
lemma apm_t00a05_radializedTime_coordinate_signs
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    (r : ℝ × ℝ) (hr : r ∈ Metric.sphere (0 : ℝ × ℝ) 1) :
    let t := (apm_t00a05_radializedTime hγ r hr).1
    ((0 < r.1 → 0 < (γ t).1) ∧ (r.1 < 0 → (γ t).1 < 0)) ∧
      ((0 < r.2 → 0 < (γ t).2.1) ∧ (r.2 < 0 → (γ t).2.1 < 0)) := by
  let t := (apm_t00a05_radializedTime hγ r hr).1
  have ht := (apm_t00a05_radializedTime hγ r hr).2
  have ha := apm_t00a05_radialHomeomorph_scale_pos
    (apm_t00a05_C2_projection_mem_frontier hγ ht.1 ht.2.le)
  have hscaled := apm_t00a05_radializedTime_spec hγ r hr
  rw [apm_t00a05_radialHomeomorph_apply] at hscaled
  have hx := congrArg Prod.fst hscaled
  have hy := congrArg Prod.snd hscaled
  change (gauge apm_t00a05_region ((γ t).1, (γ t).2.1) /
    gauge (Metric.ball (0 : ℝ × ℝ) 1) ((γ t).1, (γ t).2.1)) * (γ t).1 = r.1 at hx
  change (gauge apm_t00a05_region ((γ t).1, (γ t).2.1) /
    gauge (Metric.ball (0 : ℝ × ℝ) 1) ((γ t).1, (γ t).2.1)) * (γ t).2.1 = r.2 at hy
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro hrsign <;> nlinarith

/-- Surjectivity of the radialized loop supplies all four half-axis crossing
parameters of the original projected curve. -/
lemma apm_t00a05_C2_has_four_axis_crossings {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) :
    (∃ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1) = (1, 0) ∧
      0 < (γ t).1 ∧ (γ t).2.1 = 0) ∧
    (∃ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1) = (0, 1) ∧
      (γ t).1 = 0 ∧ 0 < (γ t).2.1) ∧
    (∃ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1) = (-1, 0) ∧
      (γ t).1 < 0 ∧ (γ t).2.1 = 0) ∧
    (∃ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1) = (0, -1) ∧
      (γ t).1 = 0 ∧ (γ t).2.1 < 0) := by
  have hsurj := apm_t00a05_C2_radialized_surjOn hγ
  have hright : (1, 0) ∈ Metric.sphere (0 : ℝ × ℝ) 1 := by
    rw [apm_t00a05_mem_supSphere_iff]
    norm_num
  have htop : (0, 1) ∈ Metric.sphere (0 : ℝ × ℝ) 1 := by
    rw [apm_t00a05_mem_supSphere_iff]
    norm_num
  have hleft : (-1, 0) ∈ Metric.sphere (0 : ℝ × ℝ) 1 := by
    rw [apm_t00a05_mem_supSphere_iff]
    norm_num
  have hbottom : (0, -1) ∈ Metric.sphere (0 : ℝ × ℝ) 1 := by
    rw [apm_t00a05_mem_supSphere_iff]
    norm_num
  rcases hsurj hright with ⟨tr, htr, hr⟩
  rcases hsurj htop with ⟨tt, htt, ht⟩
  rcases hsurj hleft with ⟨tl, htl, hl⟩
  rcases hsurj hbottom with ⟨tb, htb, hb⟩
  have scale_pos (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    apm_t00a05_radialHomeomorph_scale_pos
      (apm_t00a05_C2_projection_mem_frontier hγ ht.1 ht.2)
  refine ⟨⟨tr, htr, hr, ?_, ?_⟩, ⟨tt, htt, ht, ?_, ?_⟩,
    ⟨tl, htl, hl, ?_, ?_⟩, ⟨tb, htb, hb, ?_, ?_⟩⟩
  · change apm_t00a05_radialHomeomorph ((γ tr).1, (γ tr).2.1) = (1, 0) at hr
    rw [apm_t00a05_radialHomeomorph_apply] at hr
    have hx := congrArg Prod.fst hr
    change (gauge apm_t00a05_region ((γ tr).1, (γ tr).2.1) /
      gauge (Metric.ball (0 : ℝ × ℝ) 1) ((γ tr).1, (γ tr).2.1)) * (γ tr).1 = 1 at hx
    nlinarith [scale_pos tr htr]
  · exact (apm_t00a05_radialHomeomorph_eq_axis hr).1 one_ne_zero rfl
  · exact (apm_t00a05_radialHomeomorph_eq_axis ht).2 one_ne_zero rfl
  · change apm_t00a05_radialHomeomorph ((γ tt).1, (γ tt).2.1) = (0, 1) at ht
    rw [apm_t00a05_radialHomeomorph_apply] at ht
    have hy := congrArg Prod.snd ht
    change (gauge apm_t00a05_region ((γ tt).1, (γ tt).2.1) /
      gauge (Metric.ball (0 : ℝ × ℝ) 1) ((γ tt).1, (γ tt).2.1)) * (γ tt).2.1 = 1 at hy
    nlinarith [scale_pos tt htt]
  · change apm_t00a05_radialHomeomorph ((γ tl).1, (γ tl).2.1) = (-1, 0) at hl
    rw [apm_t00a05_radialHomeomorph_apply] at hl
    have hx := congrArg Prod.fst hl
    change (gauge apm_t00a05_region ((γ tl).1, (γ tl).2.1) /
      gauge (Metric.ball (0 : ℝ × ℝ) 1) ((γ tl).1, (γ tl).2.1)) * (γ tl).1 = -1 at hx
    nlinarith [scale_pos tl htl]
  · exact (apm_t00a05_radialHomeomorph_eq_axis hl).1 (by norm_num) rfl
  · exact (apm_t00a05_radialHomeomorph_eq_axis hb).2 (by norm_num) rfl
  · change apm_t00a05_radialHomeomorph ((γ tb).1, (γ tb).2.1) = (0, -1) at hb
    rw [apm_t00a05_radialHomeomorph_apply] at hb
    have hy := congrArg Prod.snd hb
    change (gauge apm_t00a05_region ((γ tb).1, (γ tb).2.1) /
      gauge (Metric.ball (0 : ℝ × ℝ) 1) ((γ tb).1, (γ tb).2.1)) * (γ tb).2.1 = -1 at hy
    nlinarith [scale_pos tb htb]

/-- The four square corners give a second, FTC-adapted set of crossings: on
each corner-to-corner arc one of `x` and `y` stays nonzero. -/
lemma apm_t00a05_C2_has_four_corner_crossings {γ : ℝ → ℝ × ℝ × ℝ}
    (hγ : apm_t00a05_IsC2 γ) :
    ∀ r : ℝ × ℝ, r ∈ ({(1, -1), (1, 1), (-1, 1), (-1, -1)} : Set (ℝ × ℝ)) →
      ∃ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1) = r ∧
        ((0 < r.1 → 0 < (γ t).1) ∧ (r.1 < 0 → (γ t).1 < 0)) ∧
        ((0 < r.2 → 0 < (γ t).2.1) ∧ (r.2 < 0 → (γ t).2.1 < 0)) := by
  intro r hr
  have hrsphere : r ∈ Metric.sphere (0 : ℝ × ℝ) 1 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [apm_t00a05_mem_supSphere_iff] <;> norm_num
  rcases apm_t00a05_C2_radialized_surjOn hγ hrsphere with ⟨t, ht, htr⟩
  have ha := apm_t00a05_radialHomeomorph_scale_pos
    (apm_t00a05_C2_projection_mem_frontier hγ ht.1 ht.2)
  change apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1) = r at htr
  have hscaled := htr
  rw [apm_t00a05_radialHomeomorph_apply] at hscaled
  have hx := congrArg Prod.fst hscaled
  have hy := congrArg Prod.snd hscaled
  change (gauge apm_t00a05_region ((γ t).1, (γ t).2.1) /
    gauge (Metric.ball (0 : ℝ × ℝ) 1) ((γ t).1, (γ t).2.1)) * (γ t).1 = r.1 at hx
  change (gauge apm_t00a05_region ((γ t).1, (γ t).2.1) /
    gauge (Metric.ball (0 : ℝ × ℝ) 1) ((γ t).1, (γ t).2.1)) * (γ t).2.1 = r.2 at hy
  refine ⟨t, ht, htr, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro hrsgn <;> nlinarith

lemma apm_t00a05_corner_time_ratios
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :
    let tBR := (apm_t00a05_cornerBRTime hγ).1
    let tTR := (apm_t00a05_cornerTRTime hγ).1
    let tTL := (apm_t00a05_cornerTLTime hγ).1
    let tBL := (apm_t00a05_cornerBLTime hγ).1
    (γ tBR).2.1 / (γ tBR).1 = -1 ∧
    (γ tTR).1 / (γ tTR).2.1 = 1 ∧
    (γ tTL).2.1 / (γ tTL).1 = -1 ∧
    (γ tBL).1 / (γ tBL).2.1 = 1 := by
  dsimp only
  have ratio_yx (r : ℝ × ℝ) (hr : r ∈ Metric.sphere (0 : ℝ × ℝ) 1)
      (hrx : r.1 ≠ 0) :
      let t := (apm_t00a05_radializedTime hγ r hr).1
      (γ t).2.1 / (γ t).1 = r.2 / r.1 := by
    dsimp only
    have ht := (apm_t00a05_radializedTime hγ r hr).2
    have hp := apm_t00a05_C2_projection_mem_frontier hγ ht.1 ht.2.le
    have hx : (γ (apm_t00a05_radializedTime hγ r hr).1).1 ≠ 0 :=
      (apm_t00a05_radialHomeomorph_fst_ne_zero_iff hp).mp (by
        rw [apm_t00a05_radializedTime_spec hγ r hr]
        exact hrx)
    rw [← apm_t00a05_radialHomeomorph_ratio_yx hp hx]
    rw [apm_t00a05_radializedTime_spec hγ r hr]
  have ratio_xy (r : ℝ × ℝ) (hr : r ∈ Metric.sphere (0 : ℝ × ℝ) 1)
      (hry : r.2 ≠ 0) :
      let t := (apm_t00a05_radializedTime hγ r hr).1
      (γ t).1 / (γ t).2.1 = r.1 / r.2 := by
    dsimp only
    have ht := (apm_t00a05_radializedTime hγ r hr).2
    have hp := apm_t00a05_C2_projection_mem_frontier hγ ht.1 ht.2.le
    have hy : (γ (apm_t00a05_radializedTime hγ r hr).1).2.1 ≠ 0 :=
      (apm_t00a05_radialHomeomorph_snd_ne_zero_iff hp).mp (by
        rw [apm_t00a05_radializedTime_spec hγ r hr]
        exact hry)
    rw [← apm_t00a05_radialHomeomorph_ratio_xy hp hy]
    rw [apm_t00a05_radializedTime_spec hγ r hr]
  unfold apm_t00a05_cornerBRTime apm_t00a05_cornerTRTime
    apm_t00a05_cornerTLTime apm_t00a05_cornerBLTime
  constructor
  · simpa using ratio_yx (1, -1) apm_t00a05_cornerBR_mem_sphere (by norm_num)
  constructor
  · simpa using ratio_xy (1, 1) apm_t00a05_cornerTR_mem_sphere (by norm_num)
  constructor
  · simpa using ratio_yx (-1, 1) apm_t00a05_cornerTL_mem_sphere (by norm_num)
  · simpa using ratio_xy (-1, -1) apm_t00a05_cornerBL_mem_sphere (by norm_num)

lemma apm_t00a05_radialized_coordinate_ne_zero_of_perimeter_range
    {p : ℝ × ℝ} (hp : p ∈ frontier apm_t00a05_region) :
    let q := apm_t00a05_radialHomeomorph p
    let s := apm_t00a05_squarePerimeter q
    ((0 < s ∧ s < 2) → p.2 ≠ 0) ∧
    ((2 < s ∧ s < 4) → p.1 ≠ 0) ∧
    ((4 < s ∧ s < 6) → p.2 ≠ 0) ∧
    ((6 < s ∧ s < 8) → p.1 ≠ 0) := by
  dsimp only
  have hq : apm_t00a05_radialHomeomorph p ∈
      Metric.sphere (0 : ℝ × ℝ) 1 :=
    (by rw [← apm_t00a05_radialHomeomorph_image_frontier]
        exact ⟨p, hp, rfl⟩)
  have hinv := apm_t00a05_squareOfPerimeter_squarePerimeter hq
  let s := apm_t00a05_squarePerimeter (apm_t00a05_radialHomeomorph p)
  have hcoord (hs : s ∈ Set.Icc (0 : ℝ) 8) :
      apm_t00a05_squareOfPerimeter s = apm_t00a05_radialHomeomorph p := by
    exact hinv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨hs0, hs2⟩
    change 0 < s at hs0
    change s < 2 at hs2
    have heq := hcoord ⟨hs0.le, by linarith⟩
    have hqy : (apm_t00a05_radialHomeomorph p).2 = -1 := by
      rw [← heq]
      unfold apm_t00a05_squareOfPerimeter
      split_ifs <;> simp_all <;> linarith
    exact (apm_t00a05_radialHomeomorph_snd_ne_zero_iff hp).mp (by
      rw [hqy]
      norm_num)
  · rintro ⟨hs2, hs4⟩
    change 2 < s at hs2
    change s < 4 at hs4
    have heq := hcoord ⟨by linarith, by linarith⟩
    have hqx : (apm_t00a05_radialHomeomorph p).1 = 1 := by
      rw [← heq]
      unfold apm_t00a05_squareOfPerimeter
      split_ifs <;> simp_all <;> linarith
    exact (apm_t00a05_radialHomeomorph_fst_ne_zero_iff hp).mp (by
      rw [hqx]
      norm_num)

  · rintro ⟨hs4, hs6⟩
    change 4 < s at hs4
    change s < 6 at hs6
    have heq := hcoord ⟨by linarith, by linarith⟩
    have hqy : (apm_t00a05_radialHomeomorph p).2 = 1 := by
      rw [← heq]
      unfold apm_t00a05_squareOfPerimeter
      split_ifs <;> simp_all <;> linarith
    exact (apm_t00a05_radialHomeomorph_snd_ne_zero_iff hp).mp (by
      rw [hqy]
      norm_num)
  · rintro ⟨hs6, hs8⟩
    change 6 < s at hs6
    change s < 8 at hs8
    have heq := hcoord ⟨by linarith, hs8.le⟩
    have hqx : (apm_t00a05_radialHomeomorph p).1 = -1 := by
      rw [← heq]
      unfold apm_t00a05_squareOfPerimeter
      split_ifs <;> simp_all <;> linarith
    exact (apm_t00a05_radialHomeomorph_fst_ne_zero_iff hp).mp (by
      rw [hqx]
      norm_num)

lemma apm_t00a05_radialized_coordinate_ne_zero_of_closed_perimeter_range
    {p : ℝ × ℝ} (hp : p ∈ frontier apm_t00a05_region) :
    let q := apm_t00a05_radialHomeomorph p
    let s := apm_t00a05_squarePerimeter q
    (s ∈ Set.Icc (0 : ℝ) 2 → p.2 ≠ 0) ∧
    (s ∈ Set.Icc (2 : ℝ) 4 → p.1 ≠ 0) ∧
    (s ∈ Set.Icc (4 : ℝ) 6 → p.2 ≠ 0) ∧
    (s ∈ Set.Icc (6 : ℝ) 8 → p.1 ≠ 0) := by
  dsimp only
  have hq : apm_t00a05_radialHomeomorph p ∈
      Metric.sphere (0 : ℝ × ℝ) 1 := by
    rw [← apm_t00a05_radialHomeomorph_image_frontier]
    exact ⟨p, hp, rfl⟩
  have hinv := apm_t00a05_squareOfPerimeter_squarePerimeter hq
  let s := apm_t00a05_squarePerimeter (apm_t00a05_radialHomeomorph p)
  have hcoord : apm_t00a05_squareOfPerimeter s =
      apm_t00a05_radialHomeomorph p := hinv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hs
    change s ∈ Set.Icc (0 : ℝ) 2 at hs
    have hqy : (apm_t00a05_radialHomeomorph p).2 = -1 := by
      rw [← hcoord]
      unfold apm_t00a05_squareOfPerimeter
      split_ifs <;> simp_all <;> linarith
    exact (apm_t00a05_radialHomeomorph_snd_ne_zero_iff hp).mp (by
      rw [hqy]; norm_num)
  · intro hs
    change s ∈ Set.Icc (2 : ℝ) 4 at hs
    have hqx : (apm_t00a05_radialHomeomorph p).1 = 1 := by
      rw [← hcoord]
      unfold apm_t00a05_squareOfPerimeter
      split_ifs <;> simp_all <;> linarith
    exact (apm_t00a05_radialHomeomorph_fst_ne_zero_iff hp).mp (by
      rw [hqx]; norm_num)
  · intro hs
    change s ∈ Set.Icc (4 : ℝ) 6 at hs
    have hqy : (apm_t00a05_radialHomeomorph p).2 = 1 := by
      rw [← hcoord]
      unfold apm_t00a05_squareOfPerimeter
      split_ifs <;> simp_all <;> linarith
    exact (apm_t00a05_radialHomeomorph_snd_ne_zero_iff hp).mp (by
      rw [hqy]; norm_num)
  · intro hs
    change s ∈ Set.Icc (6 : ℝ) 8 at hs
    have hqx : (apm_t00a05_radialHomeomorph p).1 = -1 := by
      rw [← hcoord]
      unfold apm_t00a05_squareOfPerimeter
      split_ifs <;> simp_all <;> linarith
    exact (apm_t00a05_radialHomeomorph_fst_ne_zero_iff hp).mp (by
      rw [hqx]; norm_num)

lemma apm_t00a05_radializedTime_lt_of_rot_perimeter_lt
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    {β : ℝ}
    (hmono : StrictMonoOn
      (fun t => apm_t00a05_rot β
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1))))
      (Set.Ioo (0 : ℝ) (2 * Real.pi)))
    {r s : ℝ × ℝ} (hr : r ∈ Metric.sphere (0 : ℝ × ℝ) 1)
    (hs : s ∈ Metric.sphere (0 : ℝ × ℝ) 1)
    (htr0 : (apm_t00a05_radializedTime hγ r hr).1 ≠ 0)
    (hts0 : (apm_t00a05_radializedTime hγ s hs).1 ≠ 0)
    (hrot : apm_t00a05_rot β (apm_t00a05_squarePerimeter r) <
      apm_t00a05_rot β (apm_t00a05_squarePerimeter s)) :
    (apm_t00a05_radializedTime hγ r hr).1 <
      (apm_t00a05_radializedTime hγ s hs).1 := by
  let tr := (apm_t00a05_radializedTime hγ r hr).1
  let ts := (apm_t00a05_radializedTime hγ s hs).1
  have htr := (apm_t00a05_radializedTime hγ r hr).2
  have hts := (apm_t00a05_radializedTime hγ s hs).2
  have htrIoo : tr ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) :=
    ⟨lt_of_le_of_ne htr.1 (Ne.symm htr0), htr.2⟩
  have htsIoo : ts ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) :=
    ⟨lt_of_le_of_ne hts.1 (Ne.symm hts0), hts.2⟩
  rcases lt_or_gt_of_ne
      (apm_t00a05_radializedTime_ne_of_ne hγ hr hs (by
        intro hrs
        subst s
        exact hrot.false)) with hlt | hgt
  · exact hlt
  · have hback := hmono htsIoo htrIoo hgt
    change apm_t00a05_rot β
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph
            ((γ (apm_t00a05_radializedTime hγ s hs).1).1,
              (γ (apm_t00a05_radializedTime hγ s hs).1).2.1))) <
      apm_t00a05_rot β
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph
            ((γ (apm_t00a05_radializedTime hγ r hr).1).1,
              (γ (apm_t00a05_radializedTime hγ r hr).1).2.1))) at hback
    rw [apm_t00a05_radializedTime_perimeter,
      apm_t00a05_radializedTime_perimeter] at hback
    exact False.elim ((not_lt_of_ge hback.le) hrot)

lemma apm_t00a05_radializedTime_eq_zero_iff_perimeter_eq_cut
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    {β : ℝ} (hβ : β ∈ Set.Icc (0 : ℝ) 8)
    (hdecode : apm_t00a05_squareOfPerimeter β =
      apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1))
    {r : ℝ × ℝ} (hr : r ∈ Metric.sphere (0 : ℝ × ℝ) 1) :
    (apm_t00a05_radializedTime hγ r hr).1 = 0 ↔
      apm_t00a05_squarePerimeter r = if β = 8 then 0 else β := by
  constructor
  · intro ht0
    have hspec := apm_t00a05_radializedTime_spec hγ r hr
    rw [ht0] at hspec
    have hrq : r = apm_t00a05_squareOfPerimeter β := by
      rw [hdecode]
      exact hspec.symm
    rw [hrq]
    exact apm_t00a05_squarePerimeter_squareOfPerimeter hβ.1 hβ.2
  · intro hper
    have hpoint : apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1) = r := by
      rw [← hdecode, ← apm_t00a05_squareOfPerimeter_squarePerimeter hr, hper]
      by_cases hb : β = 8
      · subst β
        norm_num [apm_t00a05_squareOfPerimeter]
      · simp [hb]
    have hz := (apm_t00a05_radializedTime_eq_iff hγ r hr
      ⟨0, le_rfl, Real.two_pi_pos⟩).mpr hpoint
    exact congrArg Subtype.val hz |>.symm

lemma apm_t00a05_corner_order_of_six_lt_cut
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    {β : ℝ} (hβ6 : 6 < β) (hβ8 : β ≤ 8)
    (hdecode : apm_t00a05_squareOfPerimeter β =
      apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1))
    (hmono : StrictMonoOn
      (fun t => apm_t00a05_rot β
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1))))
      (Set.Ioo (0 : ℝ) (2 * Real.pi))) :
    let tBL := (apm_t00a05_cornerBLTime hγ).1
    let tBR := (apm_t00a05_cornerBRTime hγ).1
    let tTR := (apm_t00a05_cornerTRTime hγ).1
    let tTL := (apm_t00a05_cornerTLTime hγ).1
    tBL ≤ tBR ∧ tBR < tTR ∧ tTR < tTL := by
  dsimp only
  have hβIcc : β ∈ Set.Icc (0 : ℝ) 8 := ⟨by linarith, hβ8⟩
  have hBR0 : (apm_t00a05_cornerBRTime hγ).1 ≠ 0 := by
    intro hz
    unfold apm_t00a05_cornerBRTime at hz
    have hp := (apm_t00a05_radializedTime_eq_zero_iff_perimeter_eq_cut
      hγ hβIcc hdecode apm_t00a05_cornerBR_mem_sphere).mp hz
    rw [apm_t00a05_squarePerimeter_corners.2.1] at hp
    split_ifs at hp <;> linarith
  have hTR0 : (apm_t00a05_cornerTRTime hγ).1 ≠ 0 := by
    intro hz
    unfold apm_t00a05_cornerTRTime at hz
    have hp := (apm_t00a05_radializedTime_eq_zero_iff_perimeter_eq_cut
      hγ hβIcc hdecode apm_t00a05_cornerTR_mem_sphere).mp hz
    rw [apm_t00a05_squarePerimeter_corners.2.2.1] at hp
    split_ifs at hp <;> linarith
  have hTL0 : (apm_t00a05_cornerTLTime hγ).1 ≠ 0 := by
    intro hz
    unfold apm_t00a05_cornerTLTime at hz
    have hp := (apm_t00a05_radializedTime_eq_zero_iff_perimeter_eq_cut
      hγ hβIcc hdecode apm_t00a05_cornerTL_mem_sphere).mp hz
    rw [apm_t00a05_squarePerimeter_corners.2.2.2] at hp
    split_ifs at hp <;> linarith
  have hBLle : (apm_t00a05_cornerBLTime hγ).1 ≤
      (apm_t00a05_cornerBRTime hγ).1 := by
    by_cases hBL0 : (apm_t00a05_cornerBLTime hγ).1 = 0
    · rw [hBL0]
      exact (apm_t00a05_cornerBRTime hγ).2.1
    · exact (apm_t00a05_radializedTime_lt_of_rot_perimeter_lt hγ hmono
        apm_t00a05_cornerBL_mem_sphere apm_t00a05_cornerBR_mem_sphere
        hBL0 hBR0 (by
          rw [apm_t00a05_squarePerimeter_corners.1,
            apm_t00a05_squarePerimeter_corners.2.1]
          simp [apm_t00a05_rot, show (0 : ℝ) < β by linarith,
            show (2 : ℝ) < β by linarith])) |>.le
  have hBRTR : (apm_t00a05_cornerBRTime hγ).1 <
      (apm_t00a05_cornerTRTime hγ).1 := by
    apply apm_t00a05_radializedTime_lt_of_rot_perimeter_lt hγ hmono
      apm_t00a05_cornerBR_mem_sphere apm_t00a05_cornerTR_mem_sphere hBR0 hTR0
    rw [apm_t00a05_squarePerimeter_corners.2.1,
      apm_t00a05_squarePerimeter_corners.2.2.1]
    simp [apm_t00a05_rot, show (2 : ℝ) < β by linarith,
      show (4 : ℝ) < β by linarith]
    norm_num
  have hTRTL : (apm_t00a05_cornerTRTime hγ).1 <
      (apm_t00a05_cornerTLTime hγ).1 := by
    apply apm_t00a05_radializedTime_lt_of_rot_perimeter_lt hγ hmono
      apm_t00a05_cornerTR_mem_sphere apm_t00a05_cornerTL_mem_sphere hTR0 hTL0
    rw [apm_t00a05_squarePerimeter_corners.2.2.1,
      apm_t00a05_squarePerimeter_corners.2.2.2]
    simp [apm_t00a05_rot, show (4 : ℝ) < β by linarith,
      show (6 : ℝ) < β by linarith]
    norm_num
  exact ⟨hBLle, hBRTR, hTRTL⟩

lemma apm_t00a05_corner_order_of_cut_le_two
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    {β : ℝ} (hβ0 : 0 < β) (hβ2 : β ≤ 2)
    (hdecode : apm_t00a05_squareOfPerimeter β =
      apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1))
    (hmono : StrictMonoOn
      (fun t => apm_t00a05_rot β
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1))))
      (Set.Ioo (0 : ℝ) (2 * Real.pi))) :
    let tBR := (apm_t00a05_cornerBRTime hγ).1
    let tTR := (apm_t00a05_cornerTRTime hγ).1
    let tTL := (apm_t00a05_cornerTLTime hγ).1
    let tBL := (apm_t00a05_cornerBLTime hγ).1
    tBR ≤ tTR ∧ tTR < tTL ∧ tTL < tBL := by
  dsimp only
  have hβIcc : β ∈ Set.Icc (0 : ℝ) 8 := ⟨hβ0.le, by linarith⟩
  have nonzero (r : ℝ × ℝ) (hr : r ∈ Metric.sphere (0 : ℝ × ℝ) 1)
      (hp : apm_t00a05_squarePerimeter r ≠ β) :
      (apm_t00a05_radializedTime hγ r hr).1 ≠ 0 := by
    intro hz
    have heq := (apm_t00a05_radializedTime_eq_zero_iff_perimeter_eq_cut
      hγ hβIcc hdecode hr).mp hz
    simp [show β ≠ 8 by linarith] at heq
    exact hp heq
  have hTR0 := nonzero (1, 1) apm_t00a05_cornerTR_mem_sphere (by
    rw [apm_t00a05_squarePerimeter_corners.2.2.1]; linarith)
  have hTL0 := nonzero (-1, 1) apm_t00a05_cornerTL_mem_sphere (by
    rw [apm_t00a05_squarePerimeter_corners.2.2.2]; linarith)
  have hBL0 := nonzero (-1, -1) apm_t00a05_cornerBL_mem_sphere (by
    rw [apm_t00a05_squarePerimeter_corners.1]; linarith)
  have hBRTR : (apm_t00a05_cornerBRTime hγ).1 ≤
      (apm_t00a05_cornerTRTime hγ).1 := by
    by_cases hBR0 : (apm_t00a05_cornerBRTime hγ).1 = 0
    · rw [hBR0]; exact (apm_t00a05_cornerTRTime hγ).2.1
    · exact (apm_t00a05_radializedTime_lt_of_rot_perimeter_lt hγ hmono
        apm_t00a05_cornerBR_mem_sphere apm_t00a05_cornerTR_mem_sphere
        hBR0 hTR0 (by
          rw [apm_t00a05_squarePerimeter_corners.2.1,
            apm_t00a05_squarePerimeter_corners.2.2.1]
          simp [apm_t00a05_rot, show ¬(2 : ℝ) < β by linarith,
            show ¬(4 : ℝ) < β by linarith]
          norm_num)) |>.le
  have hTRTL : (apm_t00a05_cornerTRTime hγ).1 <
      (apm_t00a05_cornerTLTime hγ).1 := by
    apply apm_t00a05_radializedTime_lt_of_rot_perimeter_lt hγ hmono
      apm_t00a05_cornerTR_mem_sphere apm_t00a05_cornerTL_mem_sphere hTR0 hTL0
    rw [apm_t00a05_squarePerimeter_corners.2.2.1,
      apm_t00a05_squarePerimeter_corners.2.2.2]
    simp [apm_t00a05_rot, show ¬(4 : ℝ) < β by linarith,
      show ¬(6 : ℝ) < β by linarith]
    norm_num
  have hTLBL : (apm_t00a05_cornerTLTime hγ).1 <
      (apm_t00a05_cornerBLTime hγ).1 := by
    apply apm_t00a05_radializedTime_lt_of_rot_perimeter_lt hγ hmono
      apm_t00a05_cornerTL_mem_sphere apm_t00a05_cornerBL_mem_sphere hTL0 hBL0
    rw [apm_t00a05_squarePerimeter_corners.2.2.2,
      apm_t00a05_squarePerimeter_corners.1]
    simp [apm_t00a05_rot, show ¬(6 : ℝ) < β by linarith,
      show (0 : ℝ) < β by linarith]
    linarith
  exact ⟨hBRTR, hTRTL, hTLBL⟩

lemma apm_t00a05_corner_order_of_two_lt_cut_le_four
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    {β : ℝ} (hβ2 : 2 < β) (hβ4 : β ≤ 4)
    (hdecode : apm_t00a05_squareOfPerimeter β =
      apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1))
    (hmono : StrictMonoOn
      (fun t => apm_t00a05_rot β
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1))))
      (Set.Ioo (0 : ℝ) (2 * Real.pi))) :
    let tTR := (apm_t00a05_cornerTRTime hγ).1
    let tTL := (apm_t00a05_cornerTLTime hγ).1
    let tBL := (apm_t00a05_cornerBLTime hγ).1
    let tBR := (apm_t00a05_cornerBRTime hγ).1
    tTR ≤ tTL ∧ tTL < tBL ∧ tBL < tBR := by
  dsimp only
  have hβIcc : β ∈ Set.Icc (0 : ℝ) 8 := ⟨by linarith, by linarith⟩
  have nonzero (r : ℝ × ℝ) (hr : r ∈ Metric.sphere (0 : ℝ × ℝ) 1)
      (hp : apm_t00a05_squarePerimeter r ≠ β) :
      (apm_t00a05_radializedTime hγ r hr).1 ≠ 0 := by
    intro hz
    have heq := (apm_t00a05_radializedTime_eq_zero_iff_perimeter_eq_cut
      hγ hβIcc hdecode hr).mp hz
    simp [show β ≠ 8 by linarith] at heq
    exact hp heq
  have hTL0 := nonzero (-1, 1) apm_t00a05_cornerTL_mem_sphere (by
    rw [apm_t00a05_squarePerimeter_corners.2.2.2]; linarith)
  have hBL0 := nonzero (-1, -1) apm_t00a05_cornerBL_mem_sphere (by
    rw [apm_t00a05_squarePerimeter_corners.1]; linarith)
  have hBR0 := nonzero (1, -1) apm_t00a05_cornerBR_mem_sphere (by
    rw [apm_t00a05_squarePerimeter_corners.2.1]; linarith)
  have hTRTL : (apm_t00a05_cornerTRTime hγ).1 ≤
      (apm_t00a05_cornerTLTime hγ).1 := by
    by_cases hTR0 : (apm_t00a05_cornerTRTime hγ).1 = 0
    · rw [hTR0]; exact (apm_t00a05_cornerTLTime hγ).2.1
    · exact (apm_t00a05_radializedTime_lt_of_rot_perimeter_lt hγ hmono
        apm_t00a05_cornerTR_mem_sphere apm_t00a05_cornerTL_mem_sphere
        hTR0 hTL0 (by
          rw [apm_t00a05_squarePerimeter_corners.2.2.1,
            apm_t00a05_squarePerimeter_corners.2.2.2]
          simp [apm_t00a05_rot, show ¬(4 : ℝ) < β by linarith,
            show ¬(6 : ℝ) < β by linarith]
          norm_num)) |>.le
  have hTLBL : (apm_t00a05_cornerTLTime hγ).1 <
      (apm_t00a05_cornerBLTime hγ).1 := by
    apply apm_t00a05_radializedTime_lt_of_rot_perimeter_lt hγ hmono
      apm_t00a05_cornerTL_mem_sphere apm_t00a05_cornerBL_mem_sphere hTL0 hBL0
    rw [apm_t00a05_squarePerimeter_corners.2.2.2,
      apm_t00a05_squarePerimeter_corners.1]
    simp [apm_t00a05_rot, show ¬(6 : ℝ) < β by linarith,
      show (0 : ℝ) < β by linarith]
    linarith
  have hBLBR : (apm_t00a05_cornerBLTime hγ).1 <
      (apm_t00a05_cornerBRTime hγ).1 := by
    apply apm_t00a05_radializedTime_lt_of_rot_perimeter_lt hγ hmono
      apm_t00a05_cornerBL_mem_sphere apm_t00a05_cornerBR_mem_sphere hBL0 hBR0
    rw [apm_t00a05_squarePerimeter_corners.1,
      apm_t00a05_squarePerimeter_corners.2.1]
    simp [apm_t00a05_rot, show (0 : ℝ) < β by linarith,
      show (2 : ℝ) < β by linarith]
  exact ⟨hTRTL, hTLBL, hBLBR⟩

lemma apm_t00a05_corner_order_of_four_lt_cut_le_six
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    {β : ℝ} (hβ4 : 4 < β) (hβ6 : β ≤ 6)
    (hdecode : apm_t00a05_squareOfPerimeter β =
      apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1))
    (hmono : StrictMonoOn
      (fun t => apm_t00a05_rot β
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1))))
      (Set.Ioo (0 : ℝ) (2 * Real.pi))) :
    let tTL := (apm_t00a05_cornerTLTime hγ).1
    let tBL := (apm_t00a05_cornerBLTime hγ).1
    let tBR := (apm_t00a05_cornerBRTime hγ).1
    let tTR := (apm_t00a05_cornerTRTime hγ).1
    tTL ≤ tBL ∧ tBL < tBR ∧ tBR < tTR := by
  dsimp only
  have hβIcc : β ∈ Set.Icc (0 : ℝ) 8 := ⟨by linarith, by linarith⟩
  have nonzero (r : ℝ × ℝ) (hr : r ∈ Metric.sphere (0 : ℝ × ℝ) 1)
      (hp : apm_t00a05_squarePerimeter r ≠ β) :
      (apm_t00a05_radializedTime hγ r hr).1 ≠ 0 := by
    intro hz
    have heq := (apm_t00a05_radializedTime_eq_zero_iff_perimeter_eq_cut
      hγ hβIcc hdecode hr).mp hz
    simp [show β ≠ 8 by linarith] at heq
    exact hp heq
  have hBL0 := nonzero (-1, -1) apm_t00a05_cornerBL_mem_sphere (by
    rw [apm_t00a05_squarePerimeter_corners.1]; linarith)
  have hBR0 := nonzero (1, -1) apm_t00a05_cornerBR_mem_sphere (by
    rw [apm_t00a05_squarePerimeter_corners.2.1]; linarith)
  have hTR0 := nonzero (1, 1) apm_t00a05_cornerTR_mem_sphere (by
    rw [apm_t00a05_squarePerimeter_corners.2.2.1]; linarith)
  have hTLBL : (apm_t00a05_cornerTLTime hγ).1 ≤
      (apm_t00a05_cornerBLTime hγ).1 := by
    by_cases hTL0 : (apm_t00a05_cornerTLTime hγ).1 = 0
    · rw [hTL0]; exact (apm_t00a05_cornerBLTime hγ).2.1
    · exact (apm_t00a05_radializedTime_lt_of_rot_perimeter_lt hγ hmono
        apm_t00a05_cornerTL_mem_sphere apm_t00a05_cornerBL_mem_sphere
        hTL0 hBL0 (by
          rw [apm_t00a05_squarePerimeter_corners.2.2.2,
            apm_t00a05_squarePerimeter_corners.1]
          simp [apm_t00a05_rot, show ¬(6 : ℝ) < β by linarith,
            show (0 : ℝ) < β by linarith]
          linarith)) |>.le
  have hBLBR : (apm_t00a05_cornerBLTime hγ).1 <
      (apm_t00a05_cornerBRTime hγ).1 := by
    apply apm_t00a05_radializedTime_lt_of_rot_perimeter_lt hγ hmono
      apm_t00a05_cornerBL_mem_sphere apm_t00a05_cornerBR_mem_sphere hBL0 hBR0
    rw [apm_t00a05_squarePerimeter_corners.1,
      apm_t00a05_squarePerimeter_corners.2.1]
    simp [apm_t00a05_rot, show (0 : ℝ) < β by linarith,
      show (2 : ℝ) < β by linarith]
  have hBRTR : (apm_t00a05_cornerBRTime hγ).1 <
      (apm_t00a05_cornerTRTime hγ).1 := by
    apply apm_t00a05_radializedTime_lt_of_rot_perimeter_lt hγ hmono
      apm_t00a05_cornerBR_mem_sphere apm_t00a05_cornerTR_mem_sphere hBR0 hTR0
    rw [apm_t00a05_squarePerimeter_corners.2.1,
      apm_t00a05_squarePerimeter_corners.2.2.1]
    simp [apm_t00a05_rot, show (2 : ℝ) < β by linarith,
      show (4 : ℝ) < β by linarith]
    norm_num
  exact ⟨hTLBL, hBLBR, hBRTR⟩

lemma apm_t00a05_perimeter_mem_Icc_between_times_same_side
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    {β a b u : ℝ}
    (hmono : StrictMonoOn
      (fun t => apm_t00a05_rot β
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1))))
      (Set.Ioo (0 : ℝ) (2 * Real.pi)))
    (ha : a ∈ Set.Ioo (0 : ℝ) (2 * Real.pi))
    (hb : b ∈ Set.Ioo (0 : ℝ) (2 * Real.pi))
    (hu : u ∈ Set.Icc a b)
    (hab : a < b)
    (hpa : apm_t00a05_squarePerimeter
      (apm_t00a05_radialHomeomorph ((γ a).1, (γ a).2.1)) = A)
    (hpb : apm_t00a05_squarePerimeter
      (apm_t00a05_radialHomeomorph ((γ b).1, (γ b).2.1)) = B)
    (hAB : A ≤ B)
    (hside : (A < β ∧ B < β) ∨ (β ≤ A ∧ β ≤ B)) :
    apm_t00a05_squarePerimeter
      (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)) ∈
      Set.Icc A B := by
  let p : ℝ → ℝ := fun t => apm_t00a05_squarePerimeter
    (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1))
  have huPeriod : u ∈ Set.Icc (0 : ℝ) (2 * Real.pi) :=
    ⟨ha.1.le.trans hu.1, hu.2.trans hb.2.le⟩
  have hpuIcc : p u ∈ Set.Icc (0 : ℝ) 8 :=
    apm_t00a05_squarePerimeter_mem_Icc
      (apm_t00a05_C2_radialized_mem_sphere hγ huPeriod.1 huPeriod.2)
  by_cases hua : u = a
  · subst u; simp [p, hpa, hAB]
  by_cases hub : u = b
  · subst u; simp [p, hpb, hAB]
  have huIoo : u ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) :=
    ⟨lt_of_lt_of_le ha.1 hu.1, lt_of_le_of_lt hu.2 hb.2⟩
  have hau : a < u := lt_of_le_of_ne hu.1 (Ne.symm hua)
  have hub' : u < b := lt_of_le_of_ne hu.2 hub
  have hlo := hmono ha huIoo hau
  have hhi := hmono huIoo hb hub'
  change apm_t00a05_rot β (p a) < apm_t00a05_rot β (p u) at hlo
  change apm_t00a05_rot β (p u) < apm_t00a05_rot β (p b) at hhi
  change p a = A at hpa
  change p b = B at hpb
  have hAIcc : A ∈ Set.Icc (0 : ℝ) 8 := by
    rw [← hpa]
    exact apm_t00a05_squarePerimeter_mem_Icc
      (apm_t00a05_C2_radialized_mem_sphere hγ ha.1.le ha.2.le)
  have hBIcc : B ∈ Set.Icc (0 : ℝ) 8 := by
    rw [← hpb]
    exact apm_t00a05_squarePerimeter_mem_Icc
      (apm_t00a05_C2_radialized_mem_sphere hγ hb.1.le hb.2.le)
  rw [hpa] at hlo
  rw [hpb] at hhi
  rcases hside with hleft | hright
  · have hpu : p u < β := by
      by_contra hn
      have hge : β ≤ p u := le_of_not_gt hn
      simp [apm_t00a05_rot, hleft.1, hleft.2, not_lt.mpr hge] at hlo hhi
      linarith [hpuIcc.1, hpuIcc.2, hAIcc.1, hBIcc.2]
    simp [apm_t00a05_rot, hleft.1, hleft.2, hpu] at hlo hhi
    exact ⟨by linarith, by linarith⟩

  · have hpu : β ≤ p u := by
      by_contra hn
      have hlt : p u < β := lt_of_not_ge hn
      simp [apm_t00a05_rot, not_lt.mpr hright.1,
        not_lt.mpr hright.2, hlt] at hlo hhi
      linarith [hpuIcc.1, hpuIcc.2, hAIcc.1, hBIcc.2]
    simp [apm_t00a05_rot, not_lt.mpr hright.1,
      not_lt.mpr hright.2, not_lt.mpr hpu] at hlo hhi
    exact ⟨by linarith, by linarith⟩

lemma apm_t00a05_perimeter_mem_Icc_from_zero_to_first
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    {β b B u : ℝ} (hβ0 : 0 < β) (hβ8 : β < 8)
    (hdecode : apm_t00a05_squareOfPerimeter β =
      apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1))
    (hmono : StrictMonoOn
      (fun t => apm_t00a05_rot β
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1))))
      (Set.Ioo (0 : ℝ) (2 * Real.pi)))
    (hb : b ∈ Set.Ioo (0 : ℝ) (2 * Real.pi))
    (hu : u ∈ Set.Icc (0 : ℝ) b)
    (hpb : apm_t00a05_squarePerimeter
      (apm_t00a05_radialHomeomorph ((γ b).1, (γ b).2.1)) = B)
    (hβB : β ≤ B) :
    apm_t00a05_squarePerimeter
      (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)) ∈
      Set.Icc β B := by
  let p : ℝ → ℝ := fun t => apm_t00a05_squarePerimeter
    (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1))
  have hp0 : p 0 = β := by
    change apm_t00a05_squarePerimeter
      (apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1)) = β
    rw [← hdecode, apm_t00a05_squarePerimeter_squareOfPerimeter hβ0.le hβ8.le]
    simp [hβ8.ne]
  by_cases hu0 : u = 0
  · subst u; simp [p, hp0, hβB]
  by_cases hub : u = b
  · subst u; simp [p, hpb, hβB]
  have huIoo : u ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) :=
    ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_lt hu.2 hb.2⟩
  have hub' : u < b := lt_of_le_of_ne hu.2 hub
  have hhi := hmono huIoo hb hub'
  change apm_t00a05_rot β (p u) < apm_t00a05_rot β (p b) at hhi
  change p b = B at hpb
  rw [hpb] at hhi
  have hpuIcc : p u ∈ Set.Icc (0 : ℝ) 8 :=
    apm_t00a05_squarePerimeter_mem_Icc
      (apm_t00a05_C2_radialized_mem_sphere hγ huIoo.1.le huIoo.2.le)
  have hBIcc : B ∈ Set.Icc (0 : ℝ) 8 := by
    rw [← hpb]
    exact apm_t00a05_squarePerimeter_mem_Icc
      (apm_t00a05_C2_radialized_mem_sphere hγ hb.1.le hb.2.le)
  have hpu : β ≤ p u := by
    by_contra hn
    have hlt : p u < β := lt_of_not_ge hn
    simp [apm_t00a05_rot, hlt, not_lt.mpr hβB] at hhi
    linarith [hpuIcc.1, hpuIcc.2, hBIcc.2]
  simp [apm_t00a05_rot, not_lt.mpr hpu, not_lt.mpr hβB] at hhi
  exact ⟨hpu, by linarith⟩

lemma apm_t00a05_perimeter_mem_Icc_from_last_to_end
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    {β a A u : ℝ} (hβ0 : 0 < β) (hβ8 : β < 8)
    (hdecode : apm_t00a05_squareOfPerimeter β =
      apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1))
    (hmono : StrictMonoOn
      (fun t => apm_t00a05_rot β
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1))))
      (Set.Ioo (0 : ℝ) (2 * Real.pi)))
    (ha : a ∈ Set.Ioo (0 : ℝ) (2 * Real.pi))
    (hu : u ∈ Set.Icc a (2 * Real.pi))
    (hpa : apm_t00a05_squarePerimeter
      (apm_t00a05_radialHomeomorph ((γ a).1, (γ a).2.1)) = A)
    (hAβ : A < β) :
    apm_t00a05_squarePerimeter
      (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)) ∈
      Set.Icc A β := by
  let p : ℝ → ℝ := fun t => apm_t00a05_squarePerimeter
    (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1))
  have hp0 : p 0 = β := by
    change apm_t00a05_squarePerimeter
      (apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1)) = β
    rw [← hdecode, apm_t00a05_squarePerimeter_squareOfPerimeter hβ0.le hβ8.le]
    simp [hβ8.ne]
  have hpT : p (2 * Real.pi) = β := by
    rw [show p (2 * Real.pi) = p 0 by
      simp only [p]
      rw [hγ.2.1]]
    exact hp0
  by_cases hua : u = a
  · subst u; simp [p, hpa, hAβ.le]
  by_cases huT : u = 2 * Real.pi
  · subst u; simp [p, hpT, hAβ.le]
  have huIoo : u ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) :=
    ⟨lt_of_lt_of_le ha.1 hu.1, lt_of_le_of_ne hu.2 huT⟩
  have hau : a < u := lt_of_le_of_ne hu.1 (Ne.symm hua)
  have hlo := hmono ha huIoo hau
  change apm_t00a05_rot β (p a) < apm_t00a05_rot β (p u) at hlo
  change p a = A at hpa
  rw [hpa] at hlo
  have hpuIcc : p u ∈ Set.Icc (0 : ℝ) 8 :=
    apm_t00a05_squarePerimeter_mem_Icc
      (apm_t00a05_C2_radialized_mem_sphere hγ huIoo.1.le huIoo.2.le)
  have hAIcc : A ∈ Set.Icc (0 : ℝ) 8 := by
    rw [← hpa]
    exact apm_t00a05_squarePerimeter_mem_Icc
      (apm_t00a05_C2_radialized_mem_sphere hγ ha.1.le ha.2.le)
  have hpu : p u < β := by
    by_contra hn
    have hge : β ≤ p u := le_of_not_gt hn
    simp [apm_t00a05_rot, hAβ, not_lt.mpr hge] at hlo
    linarith [hpuIcc.1, hpuIcc.2, hAIcc.1]
  simp [apm_t00a05_rot, hAβ, hpu] at hlo
  exact ⟨by linarith, hpu.le⟩

/-- Cutting the square chart at the initial point turns the open part of any
simple closed traversal into one strictly monotone real path.  This is the
ordering input for the four FTC arcs. -/
lemma apm_t00a05_simple_loop_chart_monotone {c : ℝ → ℝ × ℝ} {T : ℝ}
    (hT : 0 < T) (hc : Continuous c)
    (hsphere : ∀ t ∈ Set.Icc (0 : ℝ) T,
      c t ∈ Metric.sphere (0 : ℝ × ℝ) 1)
    (hinj : Set.InjOn c (Set.Ico (0 : ℝ) T))
    (hclosed : c 0 = c T) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 8 ∧ apm_t00a05_squareOfPerimeter β = c 0 ∧
      (StrictMonoOn
          (fun t => apm_t00a05_rot β (apm_t00a05_squarePerimeter (c t)))
          (Set.Ioo (0 : ℝ) T) ∨
       StrictAntiOn
          (fun t => apm_t00a05_rot β (apm_t00a05_squarePerimeter (c t)))
          (Set.Ioo (0 : ℝ) T)) := by
  let s := apm_t00a05_squarePerimeter (c 0)
  have hsIcc : s ∈ Set.Icc (0 : ℝ) 8 :=
    apm_t00a05_squarePerimeter_mem_Icc (hsphere 0 ⟨le_rfl, hT.le⟩)
  let β : ℝ := if s = 0 then 8 else s
  have hβ0 : 0 < β := by
    dsimp [β]
    split_ifs with hs0
    · norm_num
    · exact lt_of_le_of_ne hsIcc.1 (Ne.symm hs0)
  have hβ8 : β ≤ 8 := by
    dsimp [β]
    split_ifs
    · norm_num
    · exact hsIcc.2
  have hdecode : apm_t00a05_squareOfPerimeter β = c 0 := by
    dsimp [β]
    split_ifs with hs0
    · change apm_t00a05_squarePerimeter (c 0) = 0 at hs0
      have h0 : apm_t00a05_squareOfPerimeter 0 = c 0 := by
        rw [← apm_t00a05_squareOfPerimeter_squarePerimeter
          (hsphere 0 ⟨le_rfl, hT.le⟩), hs0]
      rw [← h0]
      norm_num [apm_t00a05_squareOfPerimeter]
    · exact apm_t00a05_squareOfPerimeter_squarePerimeter
        (hsphere 0 ⟨le_rfl, hT.le⟩)
  let q' : Set.Ioo (0 : ℝ) T →
      {z : Metric.sphere (0 : ℝ × ℝ) 1 |
        z.1 ≠ apm_t00a05_squareOfPerimeter β} := fun t =>
    ⟨⟨c t, hsphere t ⟨t.2.1.le, t.2.2.le⟩⟩, by
      intro heq
      have hct0 : c t = c 0 := by simpa [hdecode] using heq
      have ht0 : (0 : ℝ) ∈ Set.Ico 0 T := ⟨le_rfl, hT⟩
      have htt : (t : ℝ) ∈ Set.Ico 0 T := ⟨t.2.1.le, t.2.2⟩
      have := hinj htt ht0 hct0
      exact t.2.1.ne' this⟩
  have hq'cont : Continuous q' := by
    exact Continuous.subtype_mk
      (Continuous.subtype_mk (hc.comp continuous_subtype_val) _) _
  let f : ℝ → ℝ := fun t =>
    apm_t00a05_rot β (apm_t00a05_squarePerimeter (c t))
  have hfcont : ContinuousOn f (Set.Ioo (0 : ℝ) T) := by
    rw [continuousOn_iff_continuous_restrict]
    exact (apm_t00a05_rot_square_chart_continuous hβ0 hβ8).comp hq'cont
  have hfinj : Set.InjOn f (Set.Ioo (0 : ℝ) T) := by
    intro u hu v hv huv
    exact hinj ⟨hu.1.le, hu.2⟩ ⟨hv.1.le, hv.2⟩
      (apm_t00a05_rot_square_chart_injective
        (hsphere u ⟨hu.1.le, hu.2.le⟩)
        (hsphere v ⟨hv.1.le, hv.2.le⟩) huv)
  exact ⟨β, hβ0, hβ8, hdecode,
    hfcont.strictMonoOn_of_injOn_Ioo hT hfinj⟩

lemma apm_t00a05_C2_radialized_chart_monotone
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 8 ∧
      apm_t00a05_squareOfPerimeter β =
        apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1) ∧
      (StrictMonoOn
          (fun t => apm_t00a05_rot β
            (apm_t00a05_squarePerimeter
              (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1))))
          (Set.Ioo (0 : ℝ) (2 * Real.pi)) ∨
       StrictAntiOn
          (fun t => apm_t00a05_rot β
            (apm_t00a05_squarePerimeter
              (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1))))
          (Set.Ioo (0 : ℝ) (2 * Real.pi))) := by
  exact apm_t00a05_simple_loop_chart_monotone Real.two_pi_pos
    (apm_t00a05_C2_radialized_continuous hγ)
    (fun _ ht => apm_t00a05_C2_radialized_mem_sphere hγ ht.1 ht.2)
    (apm_t00a05_C2_radialized_injOn hγ)
    (apm_t00a05_C2_radialized_closed hγ)

lemma apm_t00a05_C2_radialized_perimeter_ne_cut
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ)
    {β t : ℝ}
    (hdecode : apm_t00a05_squareOfPerimeter β =
      apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1))
    (ht : t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    apm_t00a05_squarePerimeter
        (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1)) ≠ β := by
  intro hper
  have hsphere := apm_t00a05_C2_radialized_mem_sphere hγ ht.1.le ht.2.le
  have hpoint :
      apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1) =
        apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1) := by
    rw [← hdecode, ← hper]
    exact (apm_t00a05_squareOfPerimeter_squarePerimeter hsphere).symm
  have ht0 := apm_t00a05_C2_radialized_injOn hγ
    ⟨ht.1.le, ht.2⟩ ⟨le_rfl, Real.two_pi_pos⟩ hpoint
  exact ht.1.ne' ht0

lemma apm_t00a05_C2_radialized_chart_strictMono
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 8 ∧
      apm_t00a05_squareOfPerimeter β =
        apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1) ∧
      StrictMonoOn
        (fun t => apm_t00a05_rot β
          (apm_t00a05_squarePerimeter
            (apm_t00a05_radialHomeomorph ((γ t).1, (γ t).2.1))))
        (Set.Ioo (0 : ℝ) (2 * Real.pi)) := by
  rcases apm_t00a05_C2_radialized_chart_monotone hγ with
    ⟨β, hβ0, hβ8, hdecode, hmono | hanti⟩
  · exact ⟨β, hβ0, hβ8, hdecode, hmono⟩
  · exfalso
    rcases apm_t00a05_exists_raw_radial_angle_deriv_pos hγ with
      ⟨t, ht, hpos⟩
    let p : ℝ → ℝ := fun u => apm_t00a05_squarePerimeter
      (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1))
    let lift : ℝ → ℝ := fun u =>
      apm_t00a05_squareAngleFrom β (apm_t00a05_rot β (p u))
    have hpIcc : Set.MapsTo p (Set.Ioo (0 : ℝ) (2 * Real.pi))
        (Set.Icc (0 : ℝ) 8) := by
      intro u hu
      exact apm_t00a05_squarePerimeter_mem_Icc
        (apm_t00a05_C2_radialized_mem_sphere hγ hu.1.le hu.2.le)
    have hliftanti : StrictAntiOn lift (Set.Ioo (0 : ℝ) (2 * Real.pi)) := by
      exact apm_t00a05_squareAngleFrom_strictAntiOn_comp_rot
        hβ0.le hβ8 hpIcc hanti
    have hdeq := apm_t00a05_corrected_lift_deriv_eq_raw_of_raw_deriv_pos
      hγ hβ0 hβ8 hdecode ht hpos
    have hliftpos : 0 < deriv lift t := by
      rw [show deriv lift t = deriv (fun u => apm_t00a05_squareAngle
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph ((γ u).1, (γ u).2.1)))) t by
        simpa [lift, p] using hdeq]
      exact hpos
    have hdiff : DifferentiableAt ℝ lift t :=
      differentiableAt_of_deriv_ne_zero hliftpos.ne'
    have hnon := hliftanti.antitoneOn.derivWithin_nonpos (x := t)
    rw [hdiff.derivWithin (uniqueDiffWithinAt_Ioo ht)] at hnon
    linarith

/-- The direct square-angle composition suggested by the geometric picture is
periodic at the parameter endpoints.  Consequently it is not itself the
unwrapped lift: a seam correction (depending on the traversal direction) is
mathematically necessary before an endpoint-change argument can yield `±2π`. -/
lemma apm_t00a05_direct_squareAngle_endpoint_change_zero
    {γ : ℝ → ℝ × ℝ × ℝ} (hγ : apm_t00a05_IsC2 γ) :
    apm_t00a05_squareAngle
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph
            ((γ (2 * Real.pi)).1, (γ (2 * Real.pi)).2.1))) -
      apm_t00a05_squareAngle
        (apm_t00a05_squarePerimeter
          (apm_t00a05_radialHomeomorph ((γ 0).1, (γ 0).2.1))) = 0 := by
  rw [← apm_t00a05_C2_radialized_closed hγ]
  ring

theorem apm_t00a05 :
    (∀ p : apm_t00a05_U, apm_t00a05_dOmega p.1 = 0) ∧
    apm_t00a05_lineIntegral apm_t00a05_C1 0 (2 * Real.pi) = -2 * Real.pi ∧
    (∀ γ, apm_t00a05_IsC2 γ →
      apm_t00a05_lineIntegral γ 0 (2 * Real.pi) = -2 * Real.pi) := by
  refine ⟨apm_t00a05_dOmega_eq_zero, apm_t00a05_lineIntegral_C1, ?_⟩
  /-
  The problem-local topology bridge is now complete above: the gauge radializes
  the level-set loop to the square sphere; the perimeter decoder is a compact
  quotient; its punctured rotated chart is continuous and injective; hence a
  missed point would produce an impossible continuous simple real loop.  This
  proves surjectivity and supplies four distinct half-axis crossings.

  The punctured chart's increasing orientation is now proved from the positive
  angular-density witness.  All four possible cut locations have proved cyclic
  corner orders, and the perimeter-coordinate range is proved both between
  interior corners and across the two seam pieces.  The remaining formal step
  is the finite four-case assembly: specialize those range lemmas to obtain the
  alternating coordinate-nonvanishing hypotheses, apply the two proved per-arc
  FTC formulas, use interval-integral additivity over the five pieces, and
  telescope the corner endpoint ratios `±1` with `Real.arctan_one` to `2π`.
  `apm_t00a05_C2_exact_part_zero` already removes the `cos z dz` term.
  -/
  intro γ hγ
  rw [apm_t00a05_lineIntegral_eq_neg_angular hγ]
  suffices ∫ t in Set.Icc (0 : ℝ) (2 * Real.pi),
      apm_t00a05_angularDensity γ t = 2 * Real.pi by linarith
  sorry
