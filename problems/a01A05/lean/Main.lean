import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecificLimits.Basic

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

theorem apm_a01a05 :
    (¬ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      (seq : apm_a01A05_NearOrthogonalSeq H) (m : ℕ),
      ‖seq.f m - InnerProductSpace.gramSchmidtNormed ℝ seq.f m‖ ≤
        (2 : ℝ) ^ (-(m : ℝ))) ∧
    (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [CompleteSpace H] (seq : apm_a01A05_NearOrthogonalSeq H) (g : H),
      Tendsto (fun m ↦ inner ℝ g (seq.f m)) atTop (nhds 0)) := by
  constructor
  · /-
    Boundary (closer hop 2): hop 1 closed the valid weak-convergence conjunct
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

    `LEMMA-INDEX.md` pointed to `a98A02`'s Bessel coefficient lemmas, but the
    recovered closed-span argument is more direct and was used instead. All
    `ConstructionTargets/` modules are unrelated. Renewed searches of prior
    solved Gram--Schmidt artifacts, Mathlib's `lp` and Gram--Schmidt APIs, and
    git history found no pre-bundled counterexample. The frozen statement is
    unchanged.
    -/
    sorry
  · intro H _ _ _ seq g
    exact apm_a01A05_inner_tendsto_zero seq g
