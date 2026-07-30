import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# APM a01A05: Nearly-orthogonal sequences and Gram-Schmidt

**Problem.** Let `{fₙ}` be a sequence in a real Hilbert space `H` with
`‖fₙ‖ = 1` for all `n`, and `|⟨fₙ, fₘ⟩| ≤ 2⁻ᵐ` for all `n < m`.
Let `{eₙ}` be a Gram-Schmidt orthonormalization of `{fₙ}`.

(a) Show that `‖fₘ - eₘ‖ ≤ 2⁻ᵐ`.
(b) For any `g ∈ H`, show that `⟨g, fₘ⟩ → 0` as `m → ∞`.

In the original problem, `H = L²(ℝ)` with `⟨f,g⟩ = ∫ fg dx`.

**Statement repair note.**

The informal-solution file `apm-a01A05.md` was harvested with the **wrong
content**: it contains the proof for a01A04 (unit ball volumes), not a01A05
(Gram-Schmidt / nearly-orthogonal sequences). This file implements the correct
problem from `a01A05.tex`.
-/

set_option linter.unusedVariables false in
noncomputable section

open Filter

namespace ApmCanaries.A01A05

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A sequence of unit vectors with nearly-orthogonal inner products. -/
structure NearOrthogonalSeq (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] where
  /-- The sequence of unit vectors -/
  f : ℕ → H
  /-- Each fₙ has norm 1 -/
  norm_one : ∀ n, ‖f n‖ = 1
  /-- Inner products decay: |⟨fₙ, fₘ⟩| ≤ 2⁻ᵐ for n < m -/
  inner_bound : ∀ n m, n < m → |inner ℝ (f n) (f m)| ≤ (2 : ℝ) ^ (-(m : ℝ))

private lemma geometric_decay_tendsto_zero :
    Tendsto (fun m : ℕ => (2 : ℝ) ^ (-(m : ℝ))) atTop (nhds 0) := by
  convert tendsto_pow_atTop_nhds_zero_of_lt_one
    (show 0 ≤ (2 : ℝ)⁻¹ by positivity) (show (2 : ℝ)⁻¹ < 1 by norm_num) using 1
  ext m
  rw [← Real.rpow_natCast]
  rw [Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]

private lemma inner_tendsto_zero_of_mem_span
    (seq : NearOrthogonalSeq H) {v : H}
    (hv : v ∈ Submodule.span ℝ (Set.range seq.f)) :
    Tendsto (fun m => inner ℝ v (seq.f m)) atTop (nhds 0) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      rcases hv with ⟨n, rfl⟩
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hdecay := geometric_decay_tendsto_zero
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

private lemma inner_tendsto_zero_of_mem_closure_span
    (seq : NearOrthogonalSeq H) {v : H}
    (hv : v ∈ (Submodule.span ℝ (Set.range seq.f)).topologicalClosure) :
    Tendsto (fun m => inner ℝ v (seq.f m)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Metric.mem_closure_iff] at hv
  obtain ⟨w, hw, hvw⟩ := hv (ε / 2) (half_pos hε)
  have hwlim := inner_tendsto_zero_of_mem_span seq hw
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

/-! ## Part (b): ⟨g, fₘ⟩ → 0 for any g ∈ H -/

/-- Part (b): For any `g ∈ H`, the inner products `⟨g, fₘ⟩ → 0`.

    The proof first handles the algebraic span of the `fₙ`, using the given
    decay on generators and linearity. Unit norms give the uniform estimate
    needed to extend the result to the closed span. The component of `g`
    orthogonal to that closed span contributes zero.
-/
theorem inner_tendsto_zero [CompleteSpace H]
    (seq : NearOrthogonalSeq H) (g : H) :
    Tendsto (fun m => inner ℝ g (seq.f m)) atTop (nhds 0) := by
  let S : Submodule ℝ H := Submodule.span ℝ (Set.range seq.f)
  let K : Submodule ℝ H := S.topologicalClosure
  let p : K := K.orthogonalProjection g
  have hp :
      Tendsto (fun m => inner ℝ (p : H) (seq.f m)) atTop (nhds 0) :=
    inner_tendsto_zero_of_mem_closure_span seq p.property
  convert hp using 1
  funext m
  let u : K := ⟨seq.f m, by
    rw [show K = S.topologicalClosure by rfl, ← SetLike.mem_coe,
      Submodule.topologicalClosure_coe]
    exact subset_closure (Submodule.subset_span ⟨m, rfl⟩)⟩
  exact (K.inner_orthogonalProjection_eq_of_mem_right u g).symm

/-! ## Part (a): ‖fₘ - eₘ‖ ≤ 2⁻ᵐ -/

/-- Part (a): The Gram-Schmidt orthonormalization `{eₙ}` satisfies
    `‖fₘ - eₘ‖ ≤ 2⁻ᵐ`.

    **SORRY BOUNDARY:** Requires computing the Gram-Schmidt projection
    explicitly and bounding it using the near-orthogonality condition.
    Mathlib's `gramSchmidtNormed` provides the orthonormalization but the
    specific error bound requires the near-orthogonality condition.
-/
-- STATEMENT REPAIR 2026-07-30 (Joe-authorised). See faithfulness-ledger #7.
-- This is the one CLASS-C row: the ORIGINAL EXAM asks to "Show that
-- |f_m - e_m| ≤ 2⁻ᵐ", and that is false — Gram–Schmidt error ACCUMULATES over
-- all preceding vectors, so a per-PAIR hypothesis cannot yield the same bound on
-- the accumulated error. Knife-edge witness in ℓ²: f₀ = e₀,
-- f₁ = ½e₀ + (√3/2)e₁ saturates the hypothesis exactly (⟨f₀,f₁⟩ = ½ = 2⁻¹) yet
-- ‖f₁ - e₁‖ = √(2-√3) ≈ 0.5176 > 0.5. Margin ≈ 0.018; it still fails under
-- 1-indexing (≈ 0.252 vs 0.25). The deciding inequality was machine-checked.
--
-- Repaired to the O(2⁻ᵐ) reading, which is the evident intent and is
-- conservative: a uniform constant absorbs the accumulation. NOTE FOR REVIEW —
-- unlike the class-A repairs in the other files, this one is NOT dictated by an
-- informal solution (a01A05 has none); the choice of `∃ C` is ground control's
-- reading of the exam's intent and should be sanity-checked.
--
-- DURÉE REVIEW 2026-07-30: this repair is still false. In `ℓ²(ℕ)`, let `eᵢ`
-- be the coordinate basis, `aₘ = 2⁻⁽ᵐ⁺¹⁾`,
-- `bₘ = √(1 - m aₘ²)`, and
-- `fₘ = aₘ ∑_{i<m} eᵢ + bₘ eₘ`. Then `‖fₘ‖ = 1`, and for `n < m`,
-- `|⟪fₙ,fₘ⟫| = aₘ (n aₙ + bₙ) ≤ (3/2)aₘ ≤ 2⁻ᵐ`. Since this sequence is
-- triangular with positive diagonal, Gram--Schmidt returns `eₘ`. But
-- `‖fₘ-eₘ‖ ≥ √m aₘ = (√m/2)2⁻ᵐ`, so no uniform `C` exists. The statement
-- needs a polynomial loss (for example `C * √m * 2⁻ᵐ`) or a stronger
-- square-summed correlation hypothesis.
theorem gramSchmidt_approximation [CompleteSpace H]
    (seq : NearOrthogonalSeq H) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      ‖seq.f m - InnerProductSpace.gramSchmidtNormed ℝ seq.f m‖
        ≤ C * (2 : ℝ) ^ (-(m : ℝ)) := by
  sorry

end ApmCanaries.A01A05
