import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# APM a01A05 — nearly orthogonal sequences and Gram–Schmidt

## Statement repairs

Part (a) is false as printed. Already for two unit vectors with inner product
`1/2`, normalized Gram–Schmidt can move the second vector by
`sqrt (2 - sqrt 3) > 1/2`. More generally, the pairwise bounds do not control
the accumulated Gram–Schmidt error by `2⁻ᵐ`. Accordingly, part (a) is stated
as the negation of the claimed universal estimate rather than silently
omitted. Part (b), which is valid, is preserved.

The harvested `informal-solution.md` contains material for a01A04 rather than
this problem, so the TeX source and the mathematical correction above are used.

## Encoding questions

None. Mathlib's actual normalized Gram–Schmidt construction is used.
-/

open Filter

noncomputable section

structure apm_a01A05_NearOrthogonalSeq (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  f : ℕ → H
  norm_one : ∀ n, ‖f n‖ = 1
  inner_bound : ∀ n m, n < m →
    |inner ℝ (f n) (f m)| ≤ (2 : ℝ) ^ (-(m : ℝ))

private lemma apm_a01A05_geometric_decay_tendsto_zero :
    Tendsto (fun m : ℕ => (2 : ℝ) ^ (-(m : ℝ))) atTop (nhds 0) := by
  convert tendsto_pow_atTop_nhds_zero_of_lt_one
    (show 0 ≤ (2 : ℝ)⁻¹ by positivity) (show (2 : ℝ)⁻¹ < 1 by norm_num) using 1
  ext m
  rw [← Real.rpow_natCast]
  rw [Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]

private lemma apm_a01A05_inner_tendsto_zero_of_mem_span
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (seq : apm_a01A05_NearOrthogonalSeq H) {v : H}
    (hv : v ∈ Submodule.span ℝ (Set.range seq.f)) :
    Tendsto (fun m => inner ℝ v (seq.f m)) atTop (nhds 0) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      rcases hv with ⟨n, rfl⟩
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hdecay := apm_a01A05_geometric_decay_tendsto_zero
      rw [Metric.tendsto_atTop] at hdecay
      obtain ⟨N, hN⟩ := hdecay ε hε
      refine ⟨max N (n + 1), fun m hm => ?_⟩
      rw [dist_zero_right, Real.norm_eq_abs]
      exact lt_of_le_of_lt (seq.inner_bound n m (by omega))
        (by simpa [Real.dist_eq] using hN m (le_trans (le_max_left _ _) hm))
  | zero => simp
  | add x y hx hy hxl hyl =>
      simpa [inner_add_left] using hxl.add hyl
  | smul a x hx hxl =>
      simpa [inner_smul_left] using tendsto_const_nhds.mul hxl

private lemma apm_a01A05_inner_tendsto_zero_of_mem_closure_span
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (seq : apm_a01A05_NearOrthogonalSeq H) {v : H}
    (hv : v ∈ (Submodule.span ℝ (Set.range seq.f)).topologicalClosure) :
    Tendsto (fun m => inner ℝ v (seq.f m)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Metric.mem_closure_iff] at hv
  obtain ⟨w, hw, hvw⟩ := hv (ε / 2) (half_pos hε)
  have hwlim := apm_a01A05_inner_tendsto_zero_of_mem_span seq hw
  rw [Metric.tendsto_atTop] at hwlim
  obtain ⟨N, hN⟩ := hwlim (ε / 2) (half_pos hε)
  refine ⟨N, fun m hm => ?_⟩
  rw [dist_zero_right, Real.norm_eq_abs]
  have hwm : |inner ℝ w (seq.f m)| < ε / 2 := by
    simpa [dist_zero_right, Real.norm_eq_abs] using hN m hm
  have hvw_norm : ‖v - w‖ < ε / 2 := by
    simpa [dist_eq_norm] using hvw
  calc
    |inner ℝ v (seq.f m)| =
        |inner ℝ w (seq.f m) + inner ℝ (v - w) (seq.f m)| := by
          congr 1
          rw [inner_sub_left]
          ring
    _ ≤ |inner ℝ w (seq.f m)| + |inner ℝ (v - w) (seq.f m)| := abs_add_le _ _
    _ ≤ |inner ℝ w (seq.f m)| + ‖v - w‖ * ‖seq.f m‖ := by
      rw [← Real.norm_eq_abs]
      exact add_le_add_right (norm_inner_le_norm (𝕜 := ℝ) (v - w) (seq.f m)) _
    _ < ε / 2 + ε / 2 := by rw [seq.norm_one m, mul_one]; gcongr
    _ = ε := by ring

lemma apm_a01A05_inner_tendsto_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (seq : apm_a01A05_NearOrthogonalSeq H) (g : H) :
    Tendsto (fun m => inner ℝ g (seq.f m)) atTop (nhds 0) := by
  let S : Submodule ℝ H := Submodule.span ℝ (Set.range seq.f)
  let K : Submodule ℝ H := S.topologicalClosure
  let p : K := K.orthogonalProjection g
  have hp : Tendsto (fun m => inner ℝ (p : H) (seq.f m)) atTop (nhds 0) :=
    apm_a01A05_inner_tendsto_zero_of_mem_closure_span seq p.property
  convert hp using 1
  funext m
  let u : K := ⟨seq.f m, by
    rw [show K = S.topologicalClosure by rfl, ← SetLike.mem_coe,
      Submodule.topologicalClosure_coe]
    exact subset_closure (Submodule.subset_span ⟨m, rfl⟩)⟩
  exact (K.inner_orthogonalProjection_eq_of_mem_right u g).symm

/-- At index one, Gram--Schmidt subtracts only the projection onto the first
unit vector. This isolates the finite calculation needed by the counterexample. -/
lemma apm_a01A05_gramSchmidt_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : ℕ → H) (h0 : ‖f 0‖ = 1) :
    InnerProductSpace.gramSchmidt ℝ f 1 =
      f 1 - inner ℝ (f 0) (f 1) • f 0 := by
  rw [InnerProductSpace.gramSchmidt_def]
  rw [show Finset.Iio (1 : ℕ) = {0} by ext i; simp]
  rw [Finset.sum_singleton]
  have hg0 : InnerProductSpace.gramSchmidt ℝ f 0 = f 0 :=
    InnerProductSpace.gramSchmidt_bot ℝ f
  rw [hg0]
  rw [Submodule.starProjection_singleton]
  simp [h0]

lemma apm_a01A05_gramSchmidtNormed_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : ℕ → H) (h0 : ‖f 0‖ = 1) :
    InnerProductSpace.gramSchmidtNormed ℝ f 1 =
      ‖f 1 - inner ℝ (f 0) (f 1) • f 0‖⁻¹ •
        (f 1 - inner ℝ (f 0) (f 1) • f 0) := by
  simp only [InnerProductSpace.gramSchmidtNormed,
    apm_a01A05_gramSchmidt_one f h0]
  norm_num

abbrev apm_a01A05_l2 := lp (fun _ : ℕ ↦ ℝ) 2

/-- The infinite counterexample: the exceptional first pair is followed by
fresh coordinate vectors. -/
noncomputable def apm_a01A05_counterexample (n : ℕ) : apm_a01A05_l2 :=
  if n = 0 then lp.single 2 0 1
  else if n = 1 then
    (1 / 2 : ℝ) • lp.single 2 0 1 +
      (Real.sqrt 3 / 2) • lp.single 2 1 1
  else lp.single 2 n 1

lemma apm_a01A05_counterexample_zero :
    apm_a01A05_counterexample 0 = lp.single 2 0 1 := by
  simp [apm_a01A05_counterexample]

lemma apm_a01A05_counterexample_one :
    apm_a01A05_counterexample 1 =
      (1 / 2 : ℝ) • lp.single 2 0 1 +
        (Real.sqrt 3 / 2) • lp.single 2 1 1 := by
  simp [apm_a01A05_counterexample]

lemma apm_a01A05_counterexample_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    apm_a01A05_counterexample n = lp.single 2 n 1 := by
  simp [apm_a01A05_counterexample, (show n ≠ 0 by omega),
    (show n ≠ 1 by omega)]

lemma apm_a01A05_counterexample_norm_zero :
    ‖apm_a01A05_counterexample 0‖ = 1 := by
  simp [apm_a01A05_counterexample_zero, lp.norm_single]

lemma apm_a01A05_counterexample_norm_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    ‖apm_a01A05_counterexample n‖ = 1 := by
  rw [apm_a01A05_counterexample_of_two_le hn]
  simp [lp.norm_single]

lemma apm_a01A05_counterexample_norm_one :
    ‖apm_a01A05_counterexample 1‖ = 1 := by
  rw [apm_a01A05_counterexample_one]
  let e0 : apm_a01A05_l2 := lp.single 2 0 1
  let e1 : apm_a01A05_l2 := lp.single 2 1 1
  have hinner : inner ℝ ((1 / 2 : ℝ) • e0) ((Real.sqrt 3 / 2) • e1) = 0 := by
    rw [inner_smul_left, inner_smul_right, lp.inner_single_left]
    simp [e1]
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_real hinner
  simp [e0, e1, lp.norm_single, norm_smul] at hsq
  have hnonneg : 0 ≤ ‖(1 / 2 : ℝ) • e0 + (Real.sqrt 3 / 2) • e1‖ := norm_nonneg _
  rw [abs_of_nonneg (Real.sqrt_nonneg 3)] at hsq
  nlinarith

lemma apm_a01A05_counterexample_norm_one_all (n : ℕ) :
    ‖apm_a01A05_counterexample n‖ = 1 := by
  rcases n with _ | n
  · exact apm_a01A05_counterexample_norm_zero
  rcases n with _ | n
  · exact apm_a01A05_counterexample_norm_one
  exact apm_a01A05_counterexample_norm_of_two_le (by omega)

lemma apm_a01A05_counterexample_inner_bound (n m : ℕ) (hnm : n < m) :
    |inner ℝ (apm_a01A05_counterexample n) (apm_a01A05_counterexample m)| ≤
      (2 : ℝ) ^ (-(m : ℝ)) := by
  rcases m with _ | m
  · omega
  rcases m with _ | m
  · have hn : n = 0 := by omega
    subst n
    rw [apm_a01A05_counterexample_zero, apm_a01A05_counterexample_one,
      inner_add_right, inner_smul_right, inner_smul_right]
    simp [lp.inner_single_left]
    norm_num
  · have hm : 2 ≤ m + 2 := by omega
    rw [apm_a01A05_counterexample_of_two_le hm]
    rcases n with _ | n
    · rw [apm_a01A05_counterexample_zero, lp.inner_single_left]
      simp
      positivity
    rcases n with _ | n
    · rw [apm_a01A05_counterexample_one, inner_add_left, inner_smul_left,
        inner_smul_left, lp.inner_single_left, lp.inner_single_left]
      simp
      positivity
    · have hn : 2 ≤ n + 2 := by omega
      rw [apm_a01A05_counterexample_of_two_le hn, lp.inner_single_left]
      rw [lp.coeFn_single,
        Pi.single_eq_of_ne (by omega : n + 2 ≠ m + 2)]
      simp
      positivity

theorem apm_a01a05 :
    (¬ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      (seq : apm_a01A05_NearOrthogonalSeq H) (m : ℕ),
      ‖seq.f m - InnerProductSpace.gramSchmidtNormed ℝ seq.f m‖ ≤
        (2 : ℝ) ^ (-(m : ℝ))) ∧
    (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [CompleteSpace H] (seq : apm_a01A05_NearOrthogonalSeq H) (g : H),
      Tendsto (fun m ↦ inner ℝ g (seq.f m)) atTop (nhds 0)) := by
  constructor
  · intro h
    let seq : apm_a01A05_NearOrthogonalSeq apm_a01A05_l2 :=
      { f := apm_a01A05_counterexample
        norm_one := apm_a01A05_counterexample_norm_one_all
        inner_bound := apm_a01A05_counterexample_inner_bound }
    have hbound := h apm_a01A05_l2 seq 1
    let e0 : apm_a01A05_l2 := lp.single 2 0 1
    let e1 : apm_a01A05_l2 := lp.single 2 1 1
    have hinner : inner ℝ e0
        ((1 / 2 : ℝ) • e0 + (Real.sqrt 3 / 2) • e1) = 1 / 2 := by
      rw [inner_add_right, inner_smul_right, inner_smul_right,
        lp.inner_single_left, lp.inner_single_left]
      simp [e0, e1]
    have hgs : InnerProductSpace.gramSchmidtNormed ℝ seq.f 1 = e1 := by
      rw [apm_a01A05_gramSchmidtNormed_one seq.f (seq.norm_one 0)]
      change ‖((1 / 2 : ℝ) • e0 + (Real.sqrt 3 / 2) • e1) -
          inner ℝ e0 ((1 / 2 : ℝ) • e0 + (Real.sqrt 3 / 2) • e1) • e0‖⁻¹ •
          (((1 / 2 : ℝ) • e0 + (Real.sqrt 3 / 2) • e1) -
            inner ℝ e0 ((1 / 2 : ℝ) • e0 + (Real.sqrt 3 / 2) • e1) • e0) = e1
      rw [hinner]
      have hsqrt : Real.sqrt 3 ≠ 0 := by positivity
      rw [show ((1 / 2 : ℝ) • e0 + (Real.sqrt 3 / 2) • e1) -
          (1 / 2 : ℝ) • e0 = (Real.sqrt 3 / 2) • e1 by module]
      simp [norm_smul, e1, lp.norm_single, abs_of_nonneg (Real.sqrt_nonneg 3), hsqrt]
      rw [smul_smul]
      rw [show (2 / Real.sqrt 3) * (Real.sqrt 3 / 2) = (1 : ℝ) by field_simp,
        one_smul]
    rw [show seq.f 1 = (1 / 2 : ℝ) • e0 + (Real.sqrt 3 / 2) • e1 by
      simp [seq, e0, e1, apm_a01A05_counterexample_one], hgs] at hbound
    have horth : inner ℝ ((1 / 2 : ℝ) • e0)
        ((Real.sqrt 3 / 2 - 1) • e1) = 0 := by
      rw [inner_smul_left, inner_smul_right, lp.inner_single_left]
      simp [e0, e1]
    have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
    have hnonneg : 0 ≤ ‖(1 / 2 : ℝ) • e0 + (Real.sqrt 3 / 2 - 1) • e1‖ :=
      norm_nonneg _
    have hsqrt_lt : Real.sqrt 3 < 7 / 4 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    simp [e0, e1, lp.norm_single, norm_smul,
      abs_of_nonneg (Real.sqrt_nonneg 3)] at hsq
    norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hbound
    rw [show (1 / 2 : ℝ) • e0 + (Real.sqrt 3 / 2) • e1 - e1 =
      (1 / 2 : ℝ) • e0 + (Real.sqrt 3 / 2 - 1) • e1 by module] at hbound
    nlinarith
    /-
    Boundary (closer hop 3): hop 1 closed the valid weak-convergence conjunct
    with `apm_a01A05_inner_tendsto_zero`. The proof was recovered from
    repository history (`f4bf72c`) and revalidated against the frozen repaired
    statement. It first proves decay on the algebraic span using
    `Submodule.span_induction`, extends to the closed span using the unit-norm
    bound and Cauchy--Schwarz, and removes the orthogonal component with
    `Submodule.orthogonalProjection`.

    The remaining negated universal estimate needs a fully bundled infinite
    counterexample, not merely the two-vector calculation: the structure
    quantifies over a sequence indexed by every natural number. The intended
    witness lives in Mathlib's `ℓ²(ℕ,ℝ) = lp (fun _ : ℕ => ℝ) 2`: take the
    exceptional first pair `e₀` and `(1/2)e₀ + (sqrt 3/2)e₁`, then continue
    with fresh coordinate vectors. Source inspection found `lp.single`,
    `lp.inner_single_left/right`, and the low-index expansion through
    `gramSchmidt_def`/`gramSchmidt_bot`.

    Going beyond that boundary, hop 2 proves the space-independent lemmas
    `apm_a01A05_gramSchmidt_one` and
    `apm_a01A05_gramSchmidtNormed_one`. They expand the raw and normalized
    Gram--Schmidt vectors at index one under only `‖f 0‖ = 1`, reducing the
    projection sum exactly to `f 1 - ⟪f 0, f 1⟫ • f 0`. The live bridge is
    therefore only the infinite `lp.single` sequence's unit norms and
    pairwise bounds, followed by the resulting square-root inequality.

    Going beyond hop 2, `apm_a01A05_counterexample` now implements that
    infinite witness. Its values at zero, one, and later indices are compiled,
    and `apm_a01A05_counterexample_norm_one_all` proves every term has unit
    norm, including the exceptional radical calculation. The live bridge is
    narrowed to its pairwise estimates and the final index-one contradiction.

    `LEMMA-INDEX.md` pointed to `a98A02`'s Bessel coefficient lemmas, but the
    recovered closed-span argument is more direct and was used instead. All
    `ConstructionTargets/` modules are unrelated. Renewed searches of prior
    solved Gram--Schmidt artifacts, Mathlib's `lp` and Gram--Schmidt APIs, and
    git history found no pre-bundled counterexample. The frozen statement is
    unchanged.
    -/
  · intro H _ _ _ seq g
    exact apm_a01A05_inner_tendsto_zero seq g
