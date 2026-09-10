import ConstructionTargets.LinearGraphDensity
noncomputable section
namespace ConstructionTargets.GraphMetricComparison
open LinearGraphMeasure
variable (d : ℕ)
def point (f : E d → ℝ) (x : E d) : Ambient d := WithLp.toLp 2 (x,f x)
def Graph (f : E d → ℝ) (s : Set (E d)) : Set (Ambient d) :=
  {z | z.fst ∈ s ∧ z.snd = f z.fst}
def equivalence (f g : E d → ℝ) (s : Set (E d)) : Graph d f s ≃ Graph d g s where
  toFun z := ⟨point d g z.val.fst, z.property.1, rfl⟩
  invFun z := ⟨point d f z.val.fst, z.property.1, rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    exact Prod.ext rfl z.property.2.symm
  right_inv z := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    exact Prod.ext rfl z.property.2.symm

theorem point_recover (f : E d → ℝ) (s : Set (E d)) (z : Graph d f s) :
    point d f z.val.fst = z.val := by
  apply WithLp.ofLp_injective
  exact Prod.ext rfl z.property.2.symm

theorem first_bound (f : E d → ℝ) (x y : E d) :
    ‖x-y‖ ≤ ‖point d f x-point d f y‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 (point d f x-point d f y)
  change ‖point d f x-point d f y‖^2 = ‖x-y‖^2 + ‖f x-f y‖^2 at h
  nlinarith [norm_nonneg (point d f x-point d f y), norm_nonneg (x-y), sq_nonneg ‖f x-f y‖]

variable (f : E d → ℝ) (ell : E d →L[ℝ] ℝ) (s : Set (E d)) (ε : ℝ)
variable (hε : 0 ≤ ε)
variable (h : ∀ x ∈ s, ∀ y ∈ s, ‖f x-f y-ell (x-y)‖ ≤ ε*‖x-y‖)
theorem difference_error (x y : E d) :
    ‖(point d f x-point d f y)-(point d ell x-point d ell y)‖ =
      ‖f x-f y-ell (x-y)‖ := by
  have he : (point d f x-point d f y)-(point d ell x-point d ell y) =
      WithLp.toLp 2 (0, f x-f y-ell (x-y)) := by
    apply WithLp.ofLp_injective
    simp [point, map_sub]
  rw [he, WithLp.norm_toLp_snd]

include hε h in
theorem upper (x : E d) (hx : x ∈ s) (y : E d) (hy : y ∈ s) :
    ‖point d f x-point d f y‖ ≤ (1+ε)*‖point d ell x-point d ell y‖ := by
  have ht := norm_le_norm_add_norm_sub (point d ell x-point d ell y) (point d f x-point d f y)
  rw [norm_sub_rev (point d ell x-point d ell y) (point d f x-point d f y), difference_error] at ht
  have hb := mul_le_mul_of_nonneg_left (first_bound d ell x y) hε
  nlinarith [h x hx y hy]

include hε h in
theorem lower (x : E d) (hx : x ∈ s) (y : E d) (hy : y ∈ s) :
    (1-ε)*‖point d ell x-point d ell y‖ ≤ ‖point d f x-point d f y‖ := by
  have ht := norm_le_norm_add_norm_sub (point d f x-point d f y) (point d ell x-point d ell y)
  rw [difference_error] at ht
  have hb := mul_le_mul_of_nonneg_left (first_bound d ell x y) hε
  nlinarith [h x hx y hy]

include hε h in
theorem forward_lipschitz :
    LipschitzWith ⟨1+ε, by linarith⟩ (equivalence d ell f s) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖point d f x.val.fst-point d f y.val.fst‖ ≤ (1+ε)*‖x.val-y.val‖
  rw [← point_recover d ell s x, ← point_recover d ell s y]
  exact upper d f ell s ε hε h _ x.property.1 _ y.property.1

include hε h in
theorem inverse_lipschitz (hε1 : ε < 1) :
    LipschitzWith ⟨1/(1-ε), le_of_lt (one_div_pos.mpr (by linarith))⟩ (equivalence d ell f s).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖point d ell x.val.fst-point d ell y.val.fst‖ ≤ (1/(1-ε))*‖x.val-y.val‖
  have hb := lower d f ell s ε hε h _ x.property.1 _ y.property.1
  rw [point_recover d f s x, point_recover d f s y] at hb
  rw [one_div_mul_eq_div]
  apply (le_div_iff₀ (by linarith : 0 < 1-ε)).2
  simpa [mul_comm] using hb

def homeomorphism (hε1 : ε < 1) : Graph d ell s ≃ₜ Graph d f s where
  toEquiv := equivalence d ell f s
  continuous_toFun := (forward_lipschitz d f ell s ε hε h).continuous
  continuous_invFun := (inverse_lipschitz d f ell s ε hε h hε1).continuous


theorem graph_image (g : E d → ℝ) (t : Set (E d)) :
    Graph d g t = point d g '' t := by
  ext z
  constructor
  · intro hz
    exact ⟨z.fst, hz.1, point_recover d g t ⟨z,hz⟩⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨hx,rfl⟩

@[simp] theorem forward_source (z : Graph d ell s) :
    ((equivalence d ell f s z).val).fst = z.val.fst := rfl
@[simp] theorem inverse_source (z : Graph d f s) :
    (((equivalence d ell f s).symm z).val).fst = z.val.fst := rfl

open MeasureTheory
open scoped ENNReal
theorem subtype_measure (g : E d → ℝ) (t : Set (E d)) :
    (Measure.hausdorffMeasure (d : ℝ) : Measure (Graph d g t)) Set.univ =
      (Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d)) (Graph d g t) := by
  have hi := (isometry_subtype_coe : Isometry (fun z : Graph d g t => z.val)).hausdorffMeasure_image
    (Or.inl (Nat.cast_nonneg d)) Set.univ
  simpa using hi.symm

include hε h in
theorem measure_upper :
    (Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d)) (Graph d f s) ≤
      (ENNReal.ofReal (1+ε))^d *
      (Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d)) (Graph d ell s) := by
  have hb := (forward_lipschitz d f ell s ε hε h).hausdorffMeasure_image_le
    (d := (d : ℝ)) (Nat.cast_nonneg d) Set.univ
  rw [Set.image_univ_of_surjective (equivalence d ell f s).surjective, subtype_measure, subtype_measure] at hb
  simpa only [ENNReal.rpow_natCast, ENNReal.coe_nnreal_eq] using hb

include hε h in
theorem measure_inverse (hε1 : ε < 1) :
    (Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d)) (Graph d ell s) ≤
      (ENNReal.ofReal (1/(1-ε)))^d *
      (Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d)) (Graph d f s) := by
  have hb := (inverse_lipschitz d f ell s ε hε h hε1).hausdorffMeasure_image_le
    (d := (d : ℝ)) (Nat.cast_nonneg d) Set.univ
  rw [Set.image_univ_of_surjective (equivalence d ell f s).symm.surjective, subtype_measure, subtype_measure] at hb
  simpa only [ENNReal.rpow_natCast, ENNReal.coe_nnreal_eq] using hb

include hε h in
theorem measure_lower (hε1 : ε < 1) :
    (ENNReal.ofReal (1-ε))^d *
      (Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d)) (Graph d ell s) ≤
    (Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d)) (Graph d f s) := by
  have hb := mul_le_mul_right (measure_inverse d f ell s ε hε h hε1) ((ENNReal.ofReal (1-ε))^d)
  have hc : ENNReal.ofReal (1-ε) * ENNReal.ofReal (1/(1-ε)) = 1 := by
    rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ 1-ε)]
    simp [ne_of_gt (by linarith : 0 < 1-ε)]
  rwa [← mul_assoc, ← mul_pow, hc, one_pow, one_mul] at hb

theorem linear_measure :
    (Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d)) (Graph d ell s) =
    ENNReal.ofReal (Real.sqrt (1+‖ell‖^2)) *
      (Measure.hausdorffMeasure (d : ℝ) : Measure (E d)) s := by
  rw [graph_image]
  exact LinearGraphDensity.image_measure d ell s

include hε h in
theorem bounds (hε1 : ε < 1) :
    ((ENNReal.ofReal (1-ε))^d * ENNReal.ofReal (Real.sqrt (1+‖ell‖^2)) *
      (Measure.hausdorffMeasure (d : ℝ) : Measure (E d)) s ≤
      (Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d)) (Graph d f s)) ∧
    ((Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d)) (Graph d f s) ≤
      (ENNReal.ofReal (1+ε))^d * ENNReal.ofReal (Real.sqrt (1+‖ell‖^2)) *
      (Measure.hausdorffMeasure (d : ℝ) : Measure (E d)) s) := by
  constructor
  · simpa only [linear_measure, mul_assoc] using measure_lower d f ell s ε hε h hε1
  · simpa only [linear_measure, mul_assoc] using measure_upper d f ell s ε hε h

theorem empty_graph (g : E d → ℝ) :
    (Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d)) (Graph d g ∅) = 0 := by
  simp [graph_image]

theorem zero_error (h : ∀ x ∈ s, ∀ y ∈ s, ‖f x-f y-ell (x-y)‖ ≤ 0*‖x-y‖) :
    (Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d)) (Graph d f s) =
      ENNReal.ofReal (Real.sqrt (1+‖ell‖^2)) *
      (Measure.hausdorffMeasure (d : ℝ) : Measure (E d)) s := by
  have hb := bounds d f ell s 0 (by norm_num) h (by norm_num)
  simp only [sub_zero, add_zero, ENNReal.ofReal_one, one_pow, one_mul] at hb
  exact le_antisymm hb.2 hb.1

theorem zero_functional (g : E d → ℝ) (t : Set (E d)) (e : ℝ)
    (he : 0 ≤ e) (he1 : e < 1)
    (hg : ∀ x ∈ t, ∀ y ∈ t, ‖g x-g y‖ ≤ e*‖x-y‖) :
    (ENNReal.ofReal (1-e))^d * (Measure.hausdorffMeasure (d : ℝ) : Measure (E d)) t ≤
      (Measure.hausdorffMeasure (d : ℝ) : Measure (Ambient d)) (Graph d g t) := by
  have hb := (bounds d g 0 t e he (by simpa using hg) he1).1
  simpa using hb

theorem dimension_two (g : E 2 → ℝ) (l : E 2 →L[ℝ] ℝ) (t : Set (E 2))
    (e : ℝ) (he : 0 ≤ e) (he1 : e < 1)
    (hg : ∀ x ∈ t, ∀ y ∈ t, ‖g x-g y-l (x-y)‖ ≤ e*‖x-y‖) :
    (Measure.hausdorffMeasure (2 : ℝ) : Measure (Ambient 2)) (Graph 2 g t) ≤
      (ENNReal.ofReal (1+e))^2 * ENNReal.ofReal (Real.sqrt (1+‖l‖^2)) *
      (Measure.hausdorffMeasure (2 : ℝ) : Measure (E 2)) t :=
  (bounds 2 g l t e he hg he1).2

theorem dimension_three (g : E 3 → ℝ) (l : E 3 →L[ℝ] ℝ) (t : Set (E 3))
    (e : ℝ) (he : 0 ≤ e) (he1 : e < 1)
    (hg : ∀ x ∈ t, ∀ y ∈ t, ‖g x-g y-l (x-y)‖ ≤ e*‖x-y‖) :
    (ENNReal.ofReal (1-e))^3 * ENNReal.ofReal (Real.sqrt (1+‖l‖^2)) *
      (Measure.hausdorffMeasure (3 : ℝ) : Measure (E 3)) t ≤
      (Measure.hausdorffMeasure (3 : ℝ) : Measure (Ambient 3)) (Graph 3 g t) :=
  (bounds 3 g l t e he hg he1).1
end ConstructionTargets.GraphMetricComparison


#print axioms ConstructionTargets.GraphMetricComparison.equivalence
#print axioms ConstructionTargets.GraphMetricComparison.first_bound
#print axioms ConstructionTargets.GraphMetricComparison.difference_error
#print axioms ConstructionTargets.GraphMetricComparison.upper
#print axioms ConstructionTargets.GraphMetricComparison.lower
#print axioms ConstructionTargets.GraphMetricComparison.forward_lipschitz
#print axioms ConstructionTargets.GraphMetricComparison.inverse_lipschitz
#print axioms ConstructionTargets.GraphMetricComparison.homeomorphism
#print axioms ConstructionTargets.GraphMetricComparison.graph_image
#print axioms ConstructionTargets.GraphMetricComparison.subtype_measure
#print axioms ConstructionTargets.GraphMetricComparison.measure_upper
#print axioms ConstructionTargets.GraphMetricComparison.measure_inverse
#print axioms ConstructionTargets.GraphMetricComparison.measure_lower
#print axioms ConstructionTargets.GraphMetricComparison.linear_measure
#print axioms ConstructionTargets.GraphMetricComparison.bounds
#print axioms ConstructionTargets.GraphMetricComparison.empty_graph
#print axioms ConstructionTargets.GraphMetricComparison.zero_error
#print axioms ConstructionTargets.GraphMetricComparison.zero_functional
#print axioms ConstructionTargets.GraphMetricComparison.dimension_two
#print axioms ConstructionTargets.GraphMetricComparison.dimension_three
