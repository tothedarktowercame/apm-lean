import ConstructionTargets.SphereCapFiniteMeasure
open Metric Set MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace ConstructionTargets.IntrinsicSphereFinite
open SphereCapGraph SphereCapFiniteMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma in_cap (e x : E) (he : ‖e‖ = 1) (hx : ‖x‖ = 1)
    (hi : (1/2 : ℝ) ≤ inner ℝ x e) :
    (⟨x, by simpa [Metric.mem_sphere, dist_zero_right] using hx⟩ : Metric.sphere (0:E) 1) ∈
      Set.range (capMap (r := (9/10 : ℝ)) (by norm_num) (by norm_num) e he) := by
  let t := inner ℝ x e
  let u := x - t • e
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have huorth : inner ℝ u e = 0 := by
    simp [u, t, inner_sub_left, inner_smul_left, he]
  have hnorm : ‖u‖^2 = 1-t^2 := by
    dsimp [u]
    rw [norm_sub_sq_real]
    simp [inner_smul_right, he, hx, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ht, t]
    ring
  have hur : ‖u‖ ≤ (9/10 : ℝ) := by nlinarith [norm_nonneg u]
  have hheight : height u = t := by
    have hs := height_sq (by norm_num : (9/10:ℝ)<1) (by norm_num) hur
    have hp : 0 ≤ height u := Real.sqrt_nonneg _
    nlinarith
  refine ⟨⟨u, hur, huorth⟩, ?_⟩
  apply Subtype.ext
  change graph e u = x
  simp [graph, hheight, u]

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin (d+1))
abbrev Sphere (d : ℕ) := Metric.sphere (0 : Ambient d) 1
lemma large_coordinate (d : ℕ) (hd : d ≤ 3) (x : Sphere d) :
    ∃ i : Fin (d+1), (1/2 : ℝ) ≤ |x.val i| := by
  by_contra h
  push_neg at h
  have hs : ∑ i : Fin (d+1), (x.val i)^2 = 1 := by
    have hx : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    have hh := PiLp.norm_sq_eq_of_L2 (fun _ : Fin (d+1) => ℝ) x.val
    rw [hx] at hh
    simpa only [Real.norm_eq_abs, sq_abs, one_pow] using hh.symm
  have hb : (∑ i : Fin (d+1), (x.val i)^2) < ∑ i : Fin (d+1), (1/4 : ℝ) := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty)
    intro i _
    have hi := h i
    nlinarith [sq_abs (x.val i), abs_nonneg (x.val i)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  have hn : (d+1 : ℝ) ≤ 4 := by exact_mod_cast (show d+1 ≤ 4 by omega)
  rw [Nat.cast_add, Nat.cast_one] at hb
  nlinarith

def pole (d : ℕ) (i : Fin (d+1)) (b : Bool) : Ambient d :=
  if b then EuclideanSpace.single i 1 else -EuclideanSpace.single i 1
lemma pole_norm (d : ℕ) (i : Fin (d+1)) (b : Bool) : ‖pole d i b‖ = 1 := by
  cases b <;> simp [pole]
def cap (d : ℕ) (i : Fin (d+1)) (b : Bool) : Set (Sphere d) :=
  Set.range (capMap (r := (9/10:ℝ)) (by norm_num) (by norm_num) (pole d i b) (pole_norm d i b))
lemma cap_finite (d : ℕ) (i : Fin (d+1)) (b : Bool) :
    Measure.hausdorffMeasure d (cap d i b) < ⊤ := by
  exact euclidean_cap_measure_finite d (a := (1/4:ℝ)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) _ _
lemma caps_cover (d : ℕ) (hd : d ≤ 3) : (⋃ i, ⋃ b, cap d i b) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := large_coordinate d hd x
  have hx : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  by_cases hp : 0 ≤ x.val i
  · refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨true, ?_⟩⟩
    apply in_cap _ _ (pole_norm d i true) hx
    change (1/2:ℝ) ≤ inner ℝ x.val (EuclideanSpace.single i 1)
    have he : inner ℝ x.val (EuclideanSpace.single i 1) = x.val i := by
      simpa using EuclideanSpace.inner_single_right i (1:ℝ) x.val
    rw [he]
    simpa [abs_of_nonneg hp] using hi
  · refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨false, ?_⟩⟩
    apply in_cap _ _ (pole_norm d i false) hx
    change (1/2:ℝ) ≤ inner ℝ x.val (-EuclideanSpace.single i 1)
    have he : inner ℝ x.val (EuclideanSpace.single i 1) = x.val i := by
      simpa using EuclideanSpace.inner_single_right i (1:ℝ) x.val
    rw [inner_neg_right, he]
    simpa [abs_of_neg (lt_of_not_ge hp)] using hi

theorem sphere_measure_finite (d : ℕ) (hd : d ≤ 3) :
    Measure.hausdorffMeasure d (Set.univ : Set (Sphere d)) < ⊤ := by
  rw [← caps_cover d hd]
  have hb (i : Fin (d+1)) : Measure.hausdorffMeasure d (⋃ b, cap d i b) < ⊤ := by
    simpa using measure_biUnion_lt_top (μ := Measure.hausdorffMeasure (X := Sphere d) d)
      (Set.finite_univ : (Set.univ : Set Bool).Finite) (fun b _ => cap_finite d i b)
  simpa using measure_biUnion_lt_top (μ := Measure.hausdorffMeasure (X := Sphere d) d)
    (Set.finite_univ : (Set.univ : Set (Fin (d+1))).Finite) (fun i _ => hb i)

theorem sphere_isFiniteMeasure (d : ℕ) (hd : d ≤ 3) :
    IsFiniteMeasure (Measure.hausdorffMeasure d : Measure (Sphere d)) :=
  ⟨sphere_measure_finite d hd⟩

theorem continuous_integrable (d : ℕ) (hd : d ≤ 3) (f : Sphere d → ℝ)
    (hf : Continuous f) : Integrable f (Measure.hausdorffMeasure d) := by
  letI := sphere_isFiniteMeasure d hd
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem unitFlux_integrable (c : Ambient 2) :
    Integrable (fun u : Sphere 2 =>
      u.val 0 * (u.val 0+c 0-1)^3 + u.val 1 * (u.val 1+c 1-2)^3 +
        u.val 2 * (u.val 2+c 2-3)) (Measure.hausdorffMeasure 2) := by
  apply continuous_integrable 2 (by norm_num)
  fun_prop

theorem mixed_integrable : Integrable (fun x : Sphere 3 => x.val 1^3*x.val 0)
    (Measure.hausdorffMeasure 3) := by
  apply continuous_integrable 3 (by norm_num)
  fun_prop

theorem square_integrable : Integrable (fun x : Sphere 3 => x.val 0^2)
    (Measure.hausdorffMeasure 3) := by
  apply continuous_integrable 3 (by norm_num)
  fun_prop

theorem projective_density_split :
    (∫ x : Sphere 3, x.val 1^3*x.val 0 - 4*x.val 0^2 ∂Measure.hausdorffMeasure 3) =
    (∫ x : Sphere 3, x.val 1^3*x.val 0 ∂Measure.hausdorffMeasure 3) -
      4*(∫ x : Sphere 3, x.val 0^2 ∂Measure.hausdorffMeasure 3) := by
  rw [integral_sub mixed_integrable (square_integrable.const_mul 4), integral_const_mul]

theorem unitFlux_split (c : Ambient 2) :
    (∫ u : Sphere 2, u.val 0 * (u.val 0+c 0-1)^3 +
      u.val 1 * (u.val 1+c 1-2)^3 + u.val 2 * (u.val 2+c 2-3)
      ∂Measure.hausdorffMeasure 2) =
    (∫ u : Sphere 2, u.val 0 * (u.val 0+c 0-1)^3 ∂Measure.hausdorffMeasure 2) +
    (∫ u : Sphere 2, u.val 1 * (u.val 1+c 1-2)^3 ∂Measure.hausdorffMeasure 2) +
    (∫ u : Sphere 2, u.val 2 * (u.val 2+c 2-3) ∂Measure.hausdorffMeasure 2) := by
  have h0 : Integrable (fun u : Sphere 2 => u.val 0 * (u.val 0+c 0-1)^3)
      (Measure.hausdorffMeasure 2) := continuous_integrable 2 (by decide) _ (by fun_prop)
  have h1 : Integrable (fun u : Sphere 2 => u.val 1 * (u.val 1+c 1-2)^3)
      (Measure.hausdorffMeasure 2) := continuous_integrable 2 (by decide) _ (by fun_prop)
  have h2 : Integrable (fun u : Sphere 2 => u.val 2 * (u.val 2+c 2-3))
      (Measure.hausdorffMeasure 2) := continuous_integrable 2 (by decide) _ (by fun_prop)
  simpa only [Pi.add_apply] using (integral_add (h0.add h1) h2).trans
    (congrArg (fun z => z + ∫ u : Sphere 2, u.val 2 * (u.val 2+c 2-3) ∂Measure.hausdorffMeasure 2)
      (integral_add h0 h1))

#print axioms unitFlux_split
#print axioms in_cap
#print axioms caps_cover
#print axioms sphere_measure_finite
#print axioms sphere_isFiniteMeasure
#print axioms continuous_integrable
#print axioms unitFlux_integrable
#print axioms mixed_integrable
#print axioms square_integrable
#print axioms projective_density_split
end ConstructionTargets.IntrinsicSphereFinite
