import ConstructionTargets.SardGeneralModel

open scoped ContDiff Manifold
open Set MeasureTheory

noncomputable section

/-- Two maps continuous within a set agree at a point in the closure of any smaller set on
which they agree. -/
theorem ContinuousWithinAt.eq_of_eqOn_of_mem_closure
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {s t : Set X} {x : X} {f g : X → Y}
    (hx : x ∈ closure t) (hts : t ⊆ s)
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
    (heq : Set.EqOn f g t) : f x = g x := by
  have hn : (nhdsWithin x t).NeBot := mem_closure_iff_clusterPt.mp hx
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.mono hts) (hg.mono hts)
    (heq.eventuallyEq_of_mem self_mem_nhdsWithin)

/-- Intersecting a set with a neighborhood of a closure point preserves that closure point. -/
theorem mem_closure_inter_of_mem_nhds
    {X : Type*} [TopologicalSpace X] {t u : Set X} {x : X}
    (hx : x ∈ closure t) (hu : u ∈ nhds x) : x ∈ closure (u ∩ t) := by
  rw [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_inter_of_mem]
  · exact mem_closure_iff_nhdsWithin_neBot.mp hx
  · exact mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨u, hu, inter_subset_left⟩

/-- Intersecting a smaller set with a relative neighborhood in a larger set preserves a closure
point of the smaller set. -/
theorem mem_closure_inter_of_mem_nhdsWithin
    {X : Type*} [TopologicalSpace X] {s t u : Set X} {x : X}
    (hx : x ∈ closure t) (hts : t ⊆ s)
    (hu : u ∈ nhdsWithin x s) : x ∈ closure (u ∩ t) := by
  have hut : u ∈ nhdsWithin x t := (nhdsWithin_mono x hts) hu
  rw [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_inter_of_mem hut]
  exact mem_closure_iff_nhdsWithin_neBot.mp hx

/-- Infinite differentiability at a point supplies, for each finite order, a relative
neighborhood on which that finite differentiability holds pointwise. -/
theorem ContDiffWithinAt.exists_mem_nhdsWithin_contDiffWithinAt_of_infty
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {x : E}
    (hf : ContDiffWithinAt ℝ ∞ f s x) (hxs : x ∈ s) (k : ℕ) :
    ∃ u ∈ nhdsWithin x s, ∀ y ∈ u, ContDiffWithinAt ℝ k f s y := by
  have hk : ContDiffWithinAt ℝ (k : WithTop ENat) f s x :=
    hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have he := hk.eventually (by simp)
  simpa [insert_eq_of_mem hxs] using he.exists_mem

/-- The finite-smooth relative neighborhood supplied by `C∞` may be chosen together with
the dense-interior closure fact needed to extend identities back to the base point. -/
theorem ContDiffWithinAt.exists_mem_nhdsWithin_contDiffWithinAt_closure_interior_of_infty
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {x : E}
    (hf : ContDiffWithinAt ℝ ∞ f s x) (hxs : x ∈ s)
    (hxi : x ∈ closure (interior s)) (k : ℕ) :
    ∃ u ∈ nhdsWithin x s, x ∈ closure (u ∩ interior s) ∧
      ∀ y ∈ u, ContDiffWithinAt ℝ k f s y := by
  rcases hf.exists_mem_nhdsWithin_contDiffWithinAt_of_infty hxs k with ⟨u, hu, hfu⟩
  exact ⟨u, hu, mem_closure_inter_of_mem_nhdsWithin hxi interior_subset hu, hfu⟩

/-- Two maps continuous within a set agree at a point in the closure of its interior if they
agree throughout that interior. -/
theorem ContinuousWithinAt.eq_of_eqOn_interior_of_mem_closure
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {s : Set X} {x : X} {f g : X → Y}
    (hx : x ∈ closure (interior s))
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
    (heq : Set.EqOn f g (interior s)) : f x = g x := by
  have hn : (nhdsWithin x (interior s)).NeBot := mem_closure_iff_clusterPt.mp hx
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.mono interior_subset) (hg.mono interior_subset)
    (heq.eventuallyEq_of_mem self_mem_nhdsWithin)

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

/-- The Schwarz step for the `n`-th lower jet only consumes `n + 2` derivatives. -/
theorem ContDiffWithinAt.isSymmSndFDerivWithinAt_iteratedFDerivWithin_of_nat
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {x : E} {n : ℕ}
    (hf : ContDiffWithinAt ℝ (n + 2) f s x) (hu : UniqueDiffOn ℝ s)
    (hxs : x ∈ s) (hxi : x ∈ closure (interior s)) :
    IsSymmSndFDerivWithinAt ℝ (iteratedFDerivWithin ℝ n f s) s x := by
  apply (hf.iteratedFDerivWithin_right hu (m := 2) (i := n) ?_ hxs).isSymmSndFDerivWithinAt
  · rw [minSmoothness_of_isRCLikeNormedField]
  · exact hu
  · exact hxi
  · exact hxs
  · exact le_of_eq (add_comm (2 : WithTop ENat) (n : WithTop ENat))

/-- An iterated-derivative permutation identity valid on the interior extends to a boundary
point where the map is smooth within the set and the interior is dense. -/
theorem ContDiffWithinAt.domDomCongr_iteratedFDerivWithin_of_eqOn_interior
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {x : E}
    (hf : ContDiffWithinAt ℝ ∞ f s x) (hu : UniqueDiffOn ℝ s)
    (hxs : x ∈ s) (hxi : x ∈ closure (interior s))
    (n : ℕ) (sigma : Equiv.Perm (Fin n))
    (heq : ∀ y ∈ interior s,
      (iteratedFDerivWithin ℝ n f s y).domDomCongr sigma =
        iteratedFDerivWithin ℝ n f s y) :
    (iteratedFDerivWithin ℝ n f s x).domDomCongr sigma =
      iteratedFDerivWithin ℝ n f s x := by
  let L : ContinuousMultilinearMap ℝ (λ _ : Fin n ↦ E) F ≃ₗᵢ[ℝ]
      ContinuousMultilinearMap ℝ (λ _ : Fin n ↦ E) F :=
    ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E F sigma
  have hc := hf.continuousWithinAt_iteratedFDerivWithin hu
    (show (n : WithTop ENat) ≤ (∞ : WithTop ENat) from WithTop.coe_le_coe.mpr le_top) hxs
  exact ContinuousWithinAt.eq_of_eqOn_interior_of_mem_closure hxi
    (L.continuous.continuousAt.comp_continuousWithinAt hc) hc heq

/-- A jet-permutation identity on any smaller set whose closure contains the base point
extends to that point when the original map is smooth within the ambient set. -/
theorem ContDiffWithinAt.domDomCongr_iteratedFDerivWithin_of_eqOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s t : Set E} {f : E → F} {x : E}
    (hf : ContDiffWithinAt ℝ ∞ f s x) (hu : UniqueDiffOn ℝ s)
    (hxs : x ∈ s) (hxt : x ∈ closure t) (hts : t ⊆ s)
    (n : ℕ) (sigma : Equiv.Perm (Fin n))
    (heq : ∀ y ∈ t,
      (iteratedFDerivWithin ℝ n f s y).domDomCongr sigma =
        iteratedFDerivWithin ℝ n f s y) :
    (iteratedFDerivWithin ℝ n f s x).domDomCongr sigma =
      iteratedFDerivWithin ℝ n f s x := by
  let L : ContinuousMultilinearMap ℝ (λ _ : Fin n ↦ E) F ≃ₗᵢ[ℝ]
      ContinuousMultilinearMap ℝ (λ _ : Fin n ↦ E) F :=
    ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E F sigma
  have hc := hf.continuousWithinAt_iteratedFDerivWithin hu
    (show (n : WithTop ENat) ≤ (∞ : WithTop ENat) from WithTop.coe_le_coe.mpr le_top) hxs
  exact ContinuousWithinAt.eq_of_eqOn_of_mem_closure hxt hts
    (L.continuous.continuousAt.comp_continuousWithinAt hc) hc heq

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

/-- A permutation identity holding locally within the differentiation set is preserved by the
within derivative at the base point. -/
theorem ContinuousMultilinearMap.domDomCongr_fderivWithin_eq_self_of_eventuallyEq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {x : E} {n : ℕ}
    (g : E → ContinuousMultilinearMap ℝ (λ _ : Fin n ↦ E) F)
    (hu : UniqueDiffOn ℝ s) (hxs : x ∈ s) (sigma : Equiv.Perm (Fin n))
    (hg : Filter.EventuallyEq (nhdsWithin x s) (fun y => (g y).domDomCongr sigma) g)
    (v : E) :
    (fderivWithin ℝ g s x v).domDomCongr sigma = fderivWithin ℝ g s x v := by
  let L : ContinuousMultilinearMap ℝ (λ _ : Fin n ↦ E) F ≃ₗᵢ[ℝ]
      ContinuousMultilinearMap ℝ (λ _ : Fin n ↦ E) F :=
    ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E F sigma
  have heq : Filter.EventuallyEq (nhdsWithin x s) (L ∘ g) g := hg
  have hd : fderivWithin ℝ (L ∘ g) s x = fderivWithin ℝ g s x :=
    heq.fderivWithin_eq_of_mem hxs
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

/-- A local symmetry identity for an iterated derivative lifts to the tail slots of the next
iterated derivative. -/
theorem iteratedFDerivWithin_domDomCongr_decomposeFin_symm_zero_of_eventuallyEq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {x : E} {n : ℕ}
    (hu : UniqueDiffOn ℝ s) (hxs : x ∈ s) (sigma : Equiv.Perm (Fin n))
    (hg : Filter.EventuallyEq (nhdsWithin x s)
      (fun y => (iteratedFDerivWithin ℝ n f s y).domDomCongr sigma)
      (iteratedFDerivWithin ℝ n f s)) :
    (iteratedFDerivWithin ℝ (n + 1) f s x).domDomCongr
        (Equiv.Perm.decomposeFin.symm (0, sigma)) =
      iteratedFDerivWithin ℝ (n + 1) f s x := by
  ext v
  simp only [ContinuousMultilinearMap.domDomCongr_apply,
    iteratedFDerivWithin_succ_apply_left]
  have hd := ContinuousMultilinearMap.domDomCongr_fderivWithin_eq_self_of_eventuallyEq
    (iteratedFDerivWithin ℝ n f s) hu hxs sigma hg (v 0)
  have hv := DFunLike.congr_fun hd (Fin.tail v)
  simpa [Function.comp_def, Fin.tail, Equiv.Perm.decomposeFin_symm_apply_succ] using hv

/-- Symmetry of the lower jet's second derivative exchanges the first two slots of the
corresponding higher iterated derivative. -/
theorem iteratedFDerivWithin_domDomCongr_swap_zero_one
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {x : E} {n : ℕ}
    (hu : UniqueDiffOn ℝ s) (hxs : x ∈ s)
    (h : IsSymmSndFDerivWithinAt ℝ (iteratedFDerivWithin ℝ n f s) s x) :
    (iteratedFDerivWithin ℝ (n + 2) f s x).domDomCongr
        (Equiv.swap (0 : Fin (n + 2)) 1) =
      iteratedFDerivWithin ℝ (n + 2) f s x := by
  ext v
  simp only [ContinuousMultilinearMap.domDomCongr_apply,
    iteratedFDerivWithin_succ_apply_left]
  rw [iteratedFDerivWithin_succ_eq_comp_left]
  let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm
  have hd := LinearIsometryEquiv.comp_fderivWithin (𝕜 := ℝ) L
    (f := fderivWithin ℝ (iteratedFDerivWithin ℝ n f s) s) (s := s) (x := x) (hu x hxs)
  change ((fderivWithin ℝ (L ∘ fderivWithin ℝ (iteratedFDerivWithin ℝ n f s) s) s x)
    (v ((Equiv.swap 0 1) 0))) (Fin.tail fun i => v ((Equiv.swap 0 1) i)) = _
  rw [hd]
  change
    (fderivWithin ℝ (fderivWithin ℝ (iteratedFDerivWithin ℝ n f s) s) s x
      (v 1) (v 0)) (Fin.tail (Fin.tail v)) =
    (fderivWithin ℝ (fderivWithin ℝ (iteratedFDerivWithin ℝ n f s) s) s x
      (v 0) (v 1)) (Fin.tail (Fin.tail v))
  exact DFunLike.congr_fun (h (v 1) (v 0)) (Fin.tail (Fin.tail v))

/-- Finite-order smoothness directly fixes the leading adjacent transposition of the
corresponding iterated derivative. -/
theorem ContDiffWithinAt.iteratedFDerivWithin_domDomCongr_swap_zero_one_of_nat
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {x : E} {n : ℕ}
    (hf : ContDiffWithinAt ℝ (n + 2) f s x) (hu : UniqueDiffOn ℝ s)
    (hxs : x ∈ s) (hxi : x ∈ closure (interior s)) :
    (iteratedFDerivWithin ℝ (n + 2) f s x).domDomCongr
        (Equiv.swap (0 : Fin (n + 2)) 1) =
      iteratedFDerivWithin ℝ (n + 2) f s x :=
  iteratedFDerivWithin_domDomCongr_swap_zero_one hu hxs
    (hf.isSymmSndFDerivWithinAt_iteratedFDerivWithin_of_nat hu hxs hxi)

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
