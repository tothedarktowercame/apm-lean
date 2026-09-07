import ConstructionTargets.SardAffineLineIteratedFDeriv
import ConstructionTargets.SardTaylorPolynomialCollapse

open Set

/-- Taylor's one-dimensional mean-remainder estimate, transferred to an affine
segment in a normed source space.  The highest line derivative is bounded with
the source displacement power exposed, and vanishing multivariable derivatives
at the segment base collapse the Taylor polynomial. -/
theorem affineLine_flat_taylor_remainder_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (a x : E) (k : ℕ) (C : ℝ)
    (hf : ContDiff ℝ (k + 1) f)
    (hzero : ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f a = 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (k + 1)
        (affineLineRestriction f a (x - a)) (Icc (0 : ℝ) 1) t‖ ≤
          C * ‖x - a‖ ^ (k + 1)) :
    ‖f x - f a‖ ≤ C * ‖x - a‖ ^ (k + 1) / (Nat.factorial k : ℝ) := by
  let g := affineLineRestriction f a (x - a)
  have hg : ContDiff ℝ (k + 1) g :=
    hf.comp (contDiff_const.add (contDiff_id.smul_const (x - a)))
  have hcollapse : taylorWithinEval g k (Icc (0 : ℝ) 1) 0 1 = g 0 := by
    apply taylorWithinEval_eq_value_of_iteratedDeriv_eq_zero
    · exact uniqueDiffOn_Icc (by norm_num)
    · simp
    · exact hg.of_le (by exact_mod_cast Nat.le_add_right k 1)
    · intro i hi hik
      rw [iteratedDeriv_eq_iteratedFDeriv]
      rw [iteratedFDeriv_affineLineRestriction_zero_of_eq_zero
        f a (x - a) (k + 1) i hf (by omega) (hzero i hi hik)]
      rfl
  have hrem := taylor_mean_remainder_bound (f := g) (a := 0) (b := 1)
    (C := C * ‖x - a‖ ^ (k + 1)) (x := 1) (n := k)
    (by norm_num) hg.contDiffOn (by simp) hbound
  rw [hcollapse] at hrem
  simpa [g, affineLineRestriction] using hrem

#print axioms affineLine_flat_taylor_remainder_bound
