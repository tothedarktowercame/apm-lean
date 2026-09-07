import ConstructionTargets.SardCompactIteratedFDerivBound

open Set ContinuousLinearMap

/-- The affine-line iterated derivative formula at an arbitrary parameter. -/
theorem iteratedFDeriv_affineLineRestriction_at
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (a v : E) (n i : ℕ) (t : ℝ)
    (hf : ContDiff ℝ n f) (hi : i ≤ n) :
    iteratedFDeriv ℝ i (affineLineRestriction f a v) t =
      (iteratedFDeriv ℝ i f (a + t • v)).compContinuousLinearMap
        (fun _ ↦ scalarLineMap v) := by
  let g : E → F := fun y ↦ f (a + y)
  let L : ℝ →L[ℝ] E := scalarLineMap v
  have hg : ContDiff ℝ n g := hf.comp (contDiff_const.add contDiff_id)
  have hfun : affineLineRestriction f a v = g ∘ L := by
    funext s
    simp [affineLineRestriction, g, L, scalarLineMap]
  rw [hfun, L.iteratedFDeriv_comp_right hg t (mod_cast hi)]
  simp only [g, L, iteratedFDeriv_comp_add_left]
  simp [scalarLineMap]

/-- An ambient derivative bound on a convex set gives the scaled derivative
bound required by Taylor's theorem on every affine segment in that set. -/
theorem affineLine_iteratedDerivWithin_norm_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (K : Set E) (hconv : Convex ℝ K)
    (a x : E) (ha : a ∈ K) (hx : x ∈ K) (n : ℕ) (C : ℝ)
    (hf : ContDiff ℝ n f)
    (hC : ∀ y ∈ K, ‖iteratedFDeriv ℝ n f y‖ ≤ C)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖iteratedDerivWithin n (affineLineRestriction f a (x - a))
      (Icc (0 : ℝ) 1) t‖ ≤ C * ‖x - a‖ ^ n := by
  have hline : a + t • (x - a) ∈ K := by
    have heq : a + t • (x - a) = AffineMap.lineMap a x t := by
      rw [AffineMap.lineMap_apply_module]
      module
    rw [heq]
    exact hconv.lineMap_mem ha hx ht
  have hg : ContDiff ℝ n (affineLineRestriction f a (x - a)) :=
    hf.comp (contDiff_const.add (contDiff_id.smul_const (x - a)))
  rw [← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  rw [iteratedFDerivWithin_eq_iteratedFDeriv
    (uniqueDiffOn_Icc (by norm_num)) hg.contDiffAt ht]
  rw [iteratedFDeriv_affineLineRestriction_at f a (x - a) n n t hf le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (a + t • (x - a))‖ *
        ∏ _ : Fin n, ‖scalarLineMap (x - a)‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C * ∏ _ : Fin n, ‖scalarLineMap (x - a)‖ := by
      gcongr
      exact hC _ hline
    _ = C * ‖x - a‖ ^ n := by
      simp [scalarLineMap, ContinuousLinearMap.norm_id]

#print axioms iteratedFDeriv_affineLineRestriction_at
#print axioms affineLine_iteratedDerivWithin_norm_le
