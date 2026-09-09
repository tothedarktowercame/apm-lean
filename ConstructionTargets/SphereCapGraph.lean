import Mathlib
open Metric Set
open scoped RealInnerProductSpace NNReal ENNReal
noncomputable section
namespace ConstructionTargets.SphereCapGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def height (u : E) : ℝ := Real.sqrt (1 - ‖u‖ ^ 2)
def graph (e u : E) : E := u + height u • e

omit [InnerProductSpace ℝ E] in
lemma height_sq {r : ℝ} (hr : r < 1) (_hr0 : 0 ≤ r) {u : E} (hu : ‖u‖ ≤ r) :
    height u ^ 2 = 1 - ‖u‖ ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [norm_nonneg u]

omit [InnerProductSpace ℝ E] in
lemma height_lower {r a : ℝ} (ha : 0 < a) (hr : r < 1) (hr0 : 0 ≤ r)
    (har : a^2 ≤ 1-r^2) {u : E} (hu : ‖u‖ ≤ r) : a ≤ height u := by
  have hs := height_sq hr hr0 hu
  have hp : 0 ≤ height u := Real.sqrt_nonneg _
  nlinarith [norm_nonneg u]

omit [InnerProductSpace ℝ E] in
lemma height_difference {r a : ℝ} (ha : 0 < a) (hr : r < 1) (hr0 : 0 ≤ r)
    (har : a^2 ≤ 1-r^2) {u v : E} (hu : ‖u‖ ≤ r) (hv : ‖v‖ ≤ r) :
    |height u - height v| ≤ (r/a) * ‖u-v‖ := by
  have hlu := height_lower ha hr hr0 har hu
  have hlv := height_lower ha hr hr0 har hv
  have hsu := height_sq hr hr0 hu
  have hsv := height_sq hr hr0 hv
  have he : |height u-height v| * (height u+height v) = |‖v‖^2-‖u‖^2| := by
    rw [← abs_of_nonneg (show 0 ≤ height u+height v by linarith), ← abs_mul]
    congr 1
    nlinarith
  have hn : |‖v‖^2-‖u‖^2| ≤ ‖u-v‖ * (2*r) := by
    calc
      |‖v‖^2-‖u‖^2| = |‖v‖-‖u‖| * (‖v‖+‖u‖) := by
        rw [← abs_of_nonneg (add_nonneg (norm_nonneg v) (norm_nonneg u)), ← abs_mul]
        congr 1
        ring
      _ ≤ ‖v-u‖ * (2*r) := mul_le_mul (abs_norm_sub_norm_le v u) (by linarith)
        (add_nonneg (norm_nonneg v) (norm_nonneg u)) (norm_nonneg _)
      _ = _ := by rw [norm_sub_rev]
  have hb : a * |height u-height v| ≤ r * ‖u-v‖ := by
    nlinarith [abs_nonneg (height u-height v)]
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ ha).mpr (by nlinarith)

lemma graph_norm {r : ℝ} (hr : r < 1) (hr0 : 0 ≤ r) {e u : E}
    (he : ‖e‖ = 1) (hu : ‖u‖ ≤ r) (hue : inner ℝ u e = 0) : ‖graph e u‖ = 1 := by
  have hs := height_sq hr hr0 hu
  have hp : 0 ≤ height u := Real.sqrt_nonneg _
  have hg : ‖graph e u‖^2 = 1 := by
    simp only [graph, norm_add_sq_real, inner_smul_right, hue, mul_zero,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hp, he, mul_one, add_zero]
    nlinarith
  nlinarith [norm_nonneg (graph e u)]

def graphConstant (r a : ℝ) (hr0 : 0 ≤ r) (ha : 0 < a) : ℝ≥0 :=
  ⟨1+r/a, by positivity⟩

lemma graph_lipschitz {r a : ℝ} (ha : 0 < a) (hr : r < 1) (hr0 : 0 ≤ r)
    (har : a^2 ≤ 1-r^2) {e : E} (he : ‖e‖ = 1) :
    LipschitzOnWith (graphConstant r a hr0 ha) (graph e) (Metric.closedBall 0 r) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro u hu v hv
  have hu' : ‖u‖ ≤ r := by simpa using hu
  have hv' : ‖v‖ ≤ r := by simpa using hv
  have hh := height_difference ha hr hr0 har hu' hv'
  simp only [dist_eq_norm, graphConstant, NNReal.coe_mk]
  calc
    ‖graph e u - graph e v‖ = ‖(u-v)+(height u-height v) • e‖ := by
      congr 1
      simp only [graph, sub_smul]
      abel
    _ ≤ ‖u-v‖ + ‖(height u-height v) • e‖ := norm_add_le _ _
    _ = ‖u-v‖ + |height u-height v| := by simp [norm_smul, he]
    _ ≤ (1+r/a) * ‖u-v‖ := by nlinarith

abbrev capDomain (e : E) (r : ℝ) := {u : E // ‖u‖ ≤ r ∧ inner ℝ u e = 0}
def capMap {r : ℝ} (hr : r < 1) (hr0 : 0 ≤ r) (e : E) (he : ‖e‖ = 1) :
    capDomain e r → Metric.sphere (0 : E) 1 :=
  fun u => ⟨graph e u.val, by simpa [Metric.mem_sphere, dist_zero_right] using
    (graph_norm hr hr0 he u.property.1 u.property.2)⟩

lemma capMap_lipschitz {r a : ℝ} (ha : 0 < a) (hr : r < 1) (hr0 : 0 ≤ r)
    (har : a^2 ≤ 1-r^2) (e : E) (he : ‖e‖ = 1) :
    LipschitzWith (graphConstant r a hr0 ha) (capMap hr hr0 e he) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro u v
  exact (lipschitzOnWith_iff_dist_le_mul.mp (graph_lipschitz ha hr hr0 har he))
    u.val (by simpa using u.property.1) v.val (by simpa using v.property.1)

variable [MeasurableSpace E] [BorelSpace E]

lemma capMap_hausdorff_bound {r a : ℝ} (ha : 0 < a) (hr : r < 1) (hr0 : 0 ≤ r)
    (har : a^2 ≤ 1-r^2) (e : E) (he : ‖e‖ = 1) (d : ℝ) (hd : 0 ≤ d) :
    MeasureTheory.Measure.hausdorffMeasure d (Set.range (capMap hr hr0 e he)) ≤
      (graphConstant r a hr0 ha : ℝ≥0∞)^d *
        (MeasureTheory.Measure.hausdorffMeasure d (Set.univ : Set (capDomain e r))) := by
  simpa using (capMap_lipschitz ha hr hr0 har e he).hausdorffMeasure_image_le hd Set.univ

#print axioms height_difference
#print axioms graph_norm
#print axioms graph_lipschitz
#print axioms capMap
#print axioms capMap_lipschitz
#print axioms capMap_hausdorff_bound
end ConstructionTargets.SphereCapGraph
