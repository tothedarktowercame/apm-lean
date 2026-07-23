import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option linter.unusedSectionVars false

open Filter Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Bessel summability (note: Mathlib has ⟪eₙ, g⟫, we want ⟪g, eₙ⟫)
lemma bessel_summable (e : ℕ → E) (he : Orthonormal ℝ e) (g : E) :
    Summable (fun n => ‖@inner ℝ E _ g (e n)‖ ^ 2) := by
  have : forall n, @inner ℝ E _ g (e n) = @inner ℝ E _ (e n) g := fun n => real_inner_comm (e n) g
  simp_rw [this]
  exact he.inner_products_summable g

-- Summable → terms → 0
lemma bessel_terms_tendsto (e : ℕ → E) (he : Orthonormal ℝ e) (g : E) :
    Tendsto (fun n => ‖@inner ℝ E _ g (e n)‖ ^ 2) atTop (nhds 0) :=
  (bessel_summable e he g).tendsto_atTop_zero

-- Cauchy-Schwarz: |⟨g, fₘ-eₘ⟩| ≤ ‖g‖ ‖fₘ-eₘ‖
lemma inner_diff_bound (g : E) (f e : ℕ → E) (m : ℕ) :
    ‖@inner ℝ E _ g (f m - e m)‖ ≤ ‖g‖ * ‖f m - e m‖ :=
  norm_inner_le_norm g (f m - e m)

-- Decomposition: ⟨g, fₘ⟩ = ⟨g, eₘ⟩ + ⟨g, fₘ - eₘ⟩
lemma inner_decomp (g : E) (f e : ℕ → E) (m : ℕ) :
    @inner ℝ E _ g (f m) = @inner ℝ E _ g (e m) + @inner ℝ E _ g (f m - e m) := by
  rw [inner_sub_right]; ring

-- Main theorem (Part b)
-- HtDP design for the 1 remaining sorry:
-- 1. Rewrite using inner_decomp: ⟨g,fₘ⟩ = ⟨g,eₘ⟩ + ⟨g,fₘ-eₘ⟩
-- 2. Tendsto.add to split into two limits
-- 3. Term 1: bessel_terms_tendsto gives ‖⟨g,eₘ⟩‖² → 0
--    Need: ‖⟨g,eₘ⟩‖² → 0 implies ⟨g,eₘ⟩ → 0
--    Use: tendsto_zero_iff_norm_tendsto_zero + sqrt monotonicity
-- 4. Term 2: squeeze_zero_norm with inner_diff_bound + hclose
--    ‖⟨g,fₘ-eₘ⟩‖ ≤ ‖g‖ * ‖fₘ-eₘ‖ → ‖g‖ * 0 = 0
theorem weak_convergence_of_approx_orthonormal
    (f e : ℕ → E) (he : Orthonormal ℝ e) (g : E)
    (hclose : Tendsto (fun m => ‖f m - e m‖) atTop (nhds 0)) :
    Tendsto (fun m => @inner ℝ E _ g (f m)) atTop (nhds (0 : ℝ)) := by
  sorry
