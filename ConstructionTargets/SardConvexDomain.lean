import ConstructionTargets.SardGeneralModel

open scoped ContDiff Manifold
open Set MeasureTheory

noncomputable section

theorem ContDiffWithinAt.domDomCongr_iteratedFDerivWithin_two_of_infty
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {x : E}
    (hf : ContDiffWithinAt ℝ ∞ f s x) (hu : UniqueDiffOn ℝ s)
    (hxs : x ∈ s) (hxi : x ∈ closure (interior s)) :
    (iteratedFDerivWithin ℝ 2 f s x).domDomCongr Fin.revPerm =
      iteratedFDerivWithin ℝ 2 f s x := by
  rw [← isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin hu hxs]
  apply hf.isSymmSndFDerivWithinAt
  · rw [minSmoothness_of_isRCLikeNormedField]
    exact (show (2 : WithTop ENat) ≤ ((⊤ : ENat) : WithTop ENat) from
      WithTop.coe_le_coe.mpr le_top)
  · exact hu
  · exact hxi
  · exact hxs

/-- Every lower iterated derivative of a real `C∞` map has symmetric second derivative.
This is the Schwarz step used to exchange consecutive slots in a higher iterated derivative. -/
theorem ContDiffWithinAt.isSymmSndFDerivWithinAt_iteratedFDerivWithin_of_infty
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {x : E}
    (hf : ContDiffWithinAt ℝ ∞ f s x) (hu : UniqueDiffOn ℝ s)
    (hxs : x ∈ s) (hxi : x ∈ closure (interior s)) (n : ℕ) :
    IsSymmSndFDerivWithinAt ℝ (iteratedFDerivWithin ℝ n f s) s x := by
  apply (hf.iteratedFDerivWithin_right hu (m := 2) (i := n) ?_ hxs).isSymmSndFDerivWithinAt
  · rw [minSmoothness_of_isRCLikeNormedField]
  · exact hu
  · exact hxi
  · exact hxs
  · exact WithTop.coe_le_coe.mpr le_top

/-- A continuous multilinear map fixed by every transposition is fixed by every permutation. -/
theorem ContinuousMultilinearMap.domDomCongr_eq_self_of_swap
    {R E F ι : Type*} [Semiring R] [TopologicalSpace R]
    [AddCommMonoid E] [Module R E] [TopologicalSpace E]
    [AddCommMonoid F] [Module R F] [TopologicalSpace F]
    [Finite ι] [DecidableEq ι]
    (m : ContinuousMultilinearMap R (λ _ : ι ↦ E) F)
    (h : ∀ i j : ι, m.domDomCongr (Equiv.swap i j) = m)
    (sigma : Equiv.Perm ι) : m.domDomCongr sigma = m := by
  induction sigma using Equiv.Perm.swap_induction_on with
  | one => rfl
  | swap_mul sigma i j _ ih =>
      ext v
      change m (v ∘ (Equiv.swap i j * sigma)) = m v
      exact (DFunLike.congr_fun ih (v ∘ Equiv.swap i j)).trans (DFunLike.congr_fun (h i j) v)

/-- Adjacent transpositions suffice to fix a continuous multilinear map on `Fin (n + 1)`. -/
theorem ContinuousMultilinearMap.domDomCongr_eq_self_of_adjacent_swap
    {R E F : Type*} [Semiring R] [TopologicalSpace R]
    [AddCommMonoid E] [Module R E] [TopologicalSpace E]
    [AddCommMonoid F] [Module R F] [TopologicalSpace F]
    {n : ℕ} (m : ContinuousMultilinearMap R (λ _ : Fin (n + 1) ↦ E) F)
    (h : ∀ i : Fin n, m.domDomCongr (Equiv.swap i.castSucc i.succ) = m)
    (sigma : Equiv.Perm (Fin (n + 1))) : m.domDomCongr sigma = m := by
  let S : Submonoid (Equiv.Perm (Fin (n + 1))) :=
    { carrier := {sigma | m.domDomCongr sigma = m}
      one_mem' := rfl
      mul_mem' := by
        intro a b ha hb
        ext v
        change m (fun i ↦ v ((a * b) i)) = m v
        exact (DFunLike.congr_fun hb (v ∘ a)).trans (DFunLike.congr_fun ha v) }
  have hrange : Set.range (λ i : Fin n ↦ Equiv.swap i.castSucc i.succ) ⊆ S := by
    rintro _ ⟨i, rfl⟩
    exact h i
  have htop : S = ⊤ := by
    apply top_unique
    rw [← Equiv.Perm.mclosure_swap_castSucc_succ n]
    exact Submonoid.closure_le.mpr hrange
  show sigma ∈ S
  rw [htop]
  exact Submonoid.mem_top sigma

/-- A permutation identity holding for a multilinear-valued map on a set is preserved by its
within derivative. -/
theorem ContinuousMultilinearMap.domDomCongr_fderivWithin_eq_self
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {x : E} {n : ℕ}
    (g : E → ContinuousMultilinearMap ℝ (λ _ : Fin n ↦ E) F)
    (hu : UniqueDiffOn ℝ s) (hxs : x ∈ s) (sigma : Equiv.Perm (Fin n))
    (hg : ∀ y ∈ s, (g y).domDomCongr sigma = g y) (v : E) :
    (fderivWithin ℝ g s x v).domDomCongr sigma = fderivWithin ℝ g s x v := by
  let L : ContinuousMultilinearMap ℝ (λ _ : Fin n ↦ E) F ≃ₗᵢ[ℝ]
      ContinuousMultilinearMap ℝ (λ _ : Fin n ↦ E) F :=
    ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E F sigma
  have heq : EqOn (L ∘ g) g s := by
    intro y hy
    exact hg y hy
  have hd : fderivWithin ℝ (L ∘ g) s x = fderivWithin ℝ g s x :=
    fderivWithin_congr heq (heq hxs)
  rw [LinearIsometryEquiv.comp_fderivWithin (𝕜 := ℝ) L (hu x hxs)] at hd
  exact DFunLike.congr_fun hd v

/-- Symmetry of an iterated derivative lifts to the next derivative on the tail slots. -/
theorem iteratedFDerivWithin_domDomCongr_decomposeFin_symm_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {x : E} {n : ℕ}
    (hu : UniqueDiffOn ℝ s) (hxs : x ∈ s) (sigma : Equiv.Perm (Fin n))
    (hg : ∀ y ∈ s, (iteratedFDerivWithin ℝ n f s y).domDomCongr sigma =
      iteratedFDerivWithin ℝ n f s y) :
    (iteratedFDerivWithin ℝ (n + 1) f s x).domDomCongr
        (Equiv.Perm.decomposeFin.symm (0, sigma)) =
      iteratedFDerivWithin ℝ (n + 1) f s x := by
  ext v
  simp only [ContinuousMultilinearMap.domDomCongr_apply,
    iteratedFDerivWithin_succ_apply_left]
  have hd := ContinuousMultilinearMap.domDomCongr_fderivWithin_eq_self
    (iteratedFDerivWithin ℝ n f s) hu hxs sigma hg (v 0)
  have hv := DFunLike.congr_fun hd (Fin.tail v)
  simpa [Function.comp_def, Fin.tail, Equiv.Perm.decomposeFin_symm_apply_succ] using hv

namespace ConstructionTargets.SardConvexDomain

theorem modelRange_withinCriticalImage_subset_interior_union_frontier
    {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : ModelWithCorners ℝ E H) (f : E → F) :
    f '' {x | x ∈ Set.range I ∧
      ¬ Function.Surjective (fderivWithin ℝ f (Set.range I) x)} ⊆
      f '' {x | x ∈ interior (Set.range I) ∧
        ¬ Function.Surjective (fderiv ℝ f x)} ∪
      f '' frontier (Set.range I) := by
  rintro y ⟨x, hx, rfl⟩
  by_cases hxi : x ∈ interior (Set.range I)
  · left
    refine ⟨x, ⟨hxi, ?_⟩, rfl⟩
    exact fun hsurj => hx.2
      ((_root_.ConstructionTargets.SardGeneralModel.modelRange_interior_surjective_fderivWithin_iff
        I f x hxi).2 hsurj)
  · right
    refine ⟨x, ?_, rfl⟩
    rw [frontier, I.isClosed_range.closure_eq]
    exact ⟨hx.1, hxi⟩

theorem modelRange_withinCriticalImage_null_of_interior_of_frontier
    {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] (I : ModelWithCorners ℝ E H) (f : E → F)
    (mu : Measure F)
    (hinterior : mu (f '' {x | x ∈ interior (Set.range I) ∧
      ¬ Function.Surjective (fderiv ℝ f x)}) = 0)
    (hfrontier : mu (f '' frontier (Set.range I)) = 0) :
    mu (f '' {x | x ∈ Set.range I ∧
      ¬ Function.Surjective (fderivWithin ℝ f (Set.range I) x)}) = 0 := by
  apply measure_mono_null
    (modelRange_withinCriticalImage_subset_interior_union_frontier I f)
  exact measure_union_null hinterior hfrontier

end ConstructionTargets.SardConvexDomain
