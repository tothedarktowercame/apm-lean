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

theorem apm_t00a05 :
    (∀ p : apm_t00a05_U, apm_t00a05_dOmega p.1 = 0) ∧
    apm_t00a05_lineIntegral apm_t00a05_C1 0 (2 * Real.pi) = -2 * Real.pi ∧
    (∀ γ, apm_t00a05_IsC2 γ →
      apm_t00a05_lineIntegral γ 0 (2 * Real.pi) = -2 * Real.pi) := by
  refine ⟨apm_t00a05_dOmega_eq_zero, apm_t00a05_lineIntegral_C1, ?_⟩
  /-
  This pass closes the exterior-derivative computation and the complete `C1`
  period calculation.  The remaining assertion is genuinely global: an
  injective, positively oriented parametrization of the specified connected
  component must have winding number one around the deleted axis, after which
  the exact angular-form integral is `-2π`; the `cos z dz` term is exact.
  Mathlib exposes no theorem connecting these raw coordinate `deriv` integrals
  and the frozen implicit-surface/simple-loop predicate to winding number or a
  change-of-variables formula.
  -/
  intro γ hγ
  sorry
