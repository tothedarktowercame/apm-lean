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

/-- At an interior point, finite differentiability persists on a relative neighborhood that
stays inside the interior. -/
theorem ContDiffWithinAt.eventually_mem_interior_contDiffWithinAt_of_nat
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {x : E} {k : ℕ}
    (hf : ContDiffWithinAt ℝ k f s x) (hxi : x ∈ interior s) :
    ∀ᶠ y in nhdsWithin x s, y ∈ interior s ∧ ContDiffWithinAt ℝ k f s y := by
  have hxs : x ∈ s := interior_subset hxi
  have hsmooth : ∀ᶠ y in nhdsWithin x s, ContDiffWithinAt ℝ k f s y := by
    simpa [insert_eq_of_mem hxs] using hf.eventually (by simp)
  have hinterior : ∀ᶠ y in nhdsWithin x s, y ∈ interior s :=
    mem_nhdsWithin_of_mem_nhds (isOpen_interior.mem_nhds hxi)
  filter_upwards [hinterior, hsmooth] with y hy hfy
  exact ⟨hy, hfy⟩

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

/-- A pointwise jet-permutation identity on a relative neighborhood is the corresponding
eventual equality in `nhdsWithin`. -/
theorem iteratedFDerivWithin_domDomCongr_eventuallyEq_of_mem
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s u : Set E} {f : E → F} {x : E} {n : ℕ}
    (hu : u ∈ nhdsWithin x s) (sigma : Equiv.Perm (Fin n))
    (h : ∀ y ∈ u,
      (iteratedFDerivWithin ℝ n f s y).domDomCongr sigma =
        iteratedFDerivWithin ℝ n f s y) :
    Filter.EventuallyEq (nhdsWithin x s)
      (fun y => (iteratedFDerivWithin ℝ n f s y).domDomCongr sigma)
      (iteratedFDerivWithin ℝ n f s) := by
  filter_upwards [hu] with y hy
  exact h y hy

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

/-- An adjacent symmetry of a lower jet lifts to the same adjacent transposition shifted
past the new leading derivative slot. -/
theorem iteratedFDerivWithin_domDomCongr_adjacent_succ
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {x : E} {n : ℕ}
    (hu : UniqueDiffOn ℝ s) (hxs : x ∈ s) (i : Fin n)
    (hg : ∀ y ∈ s,
      (iteratedFDerivWithin ℝ (n + 1) f s y).domDomCongr
          (Equiv.swap i.castSucc i.succ) =
        iteratedFDerivWithin ℝ (n + 1) f s y) :
    (iteratedFDerivWithin ℝ (n + 2) f s x).domDomCongr
        (Equiv.swap i.castSucc.succ i.succ.succ) =
      iteratedFDerivWithin ℝ (n + 2) f s x := by
  have hp : Equiv.Perm.decomposeFin.symm (0, Equiv.swap i.castSucc i.succ) =
      Equiv.swap i.castSucc.succ i.succ.succ := by
    ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [Equiv.Perm.decomposeFin_symm_apply_zero,
        Equiv.swap_apply_of_ne_of_ne] <;> grind
    · simp only [Equiv.Perm.decomposeFin_symm_apply_succ]
      simp [Equiv.swap_apply_def]
      split_ifs <;> simp_all
  rw [← hp]
  exact iteratedFDerivWithin_domDomCongr_decomposeFin_symm_zero hu hxs
    (Equiv.swap i.castSucc i.succ) hg

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

/-- A locally valid lower adjacent symmetry lifts to the shifted adjacent transposition of
the next jet at the base point. -/
theorem iteratedFDerivWithin_domDomCongr_adjacent_succ_of_eventuallyEq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {x : E} {n : ℕ}
    (hu : UniqueDiffOn ℝ s) (hxs : x ∈ s) (i : Fin n)
    (hg : Filter.EventuallyEq (nhdsWithin x s)
      (fun y => (iteratedFDerivWithin ℝ (n + 1) f s y).domDomCongr
        (Equiv.swap i.castSucc i.succ))
      (iteratedFDerivWithin ℝ (n + 1) f s)) :
    (iteratedFDerivWithin ℝ (n + 2) f s x).domDomCongr
        (Equiv.swap i.castSucc.succ i.succ.succ) =
      iteratedFDerivWithin ℝ (n + 2) f s x := by
  have hp : Equiv.Perm.decomposeFin.symm (0, Equiv.swap i.castSucc i.succ) =
      Equiv.swap i.castSucc.succ i.succ.succ := by
    ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [Equiv.Perm.decomposeFin_symm_apply_zero,
        Equiv.swap_apply_of_ne_of_ne] <;> grind
    · simp only [Equiv.Perm.decomposeFin_symm_apply_succ]
      simp [Equiv.swap_apply_def]
      split_ifs <;> simp_all
  rw [← hp]
  exact iteratedFDerivWithin_domDomCongr_decomposeFin_symm_zero_of_eventuallyEq
    hu hxs (Equiv.swap i.castSucc i.succ) hg

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

/-- At an interior point, finite differentiability through order `n` makes the `n`-th
iterated derivative invariant under every permutation. -/
theorem ContDiffWithinAt.domDomCongr_iteratedFDerivWithin_of_nat_of_mem_interior
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {x : E} (hu : UniqueDiffOn ℝ s) :
    ∀ n : ℕ, ContDiffWithinAt ℝ n f s x → x ∈ interior s →
      ∀ sigma : Equiv.Perm (Fin n),
        (iteratedFDerivWithin ℝ n f s x).domDomCongr sigma =
          iteratedFDerivWithin ℝ n f s x := by
  intro n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
      intro hf hxi sigma
      cases n with
      | zero =>
          ext v
          congr 1
      | succ n =>
          apply ContinuousMultilinearMap.domDomCongr_eq_self_of_adjacent_swap _ _ sigma
          intro i
          cases n with
          | zero => exact Fin.elim0 i
          | succ m =>
              refine Fin.cases ?_ (fun j => ?_) i
              · simpa only [Nat.add_eq, Nat.add_zero, Nat.add_assoc] using
                  hf.iteratedFDerivWithin_domDomCongr_swap_zero_one_of_nat hu
                    (interior_subset hxi) (subset_closure hxi)
              · have hflower : ContDiffWithinAt ℝ (m + 1) f s x :=
                  hf.of_le (WithTop.coe_le_coe.mpr (by
                    have hm : ((m + 1 : ℕ) : ENat) ≤ ((m + 2 : ℕ) : ENat) := by
                      exact_mod_cast Nat.le_succ (m + 1)
                    simpa using hm))
                have hev := hflower.eventually_mem_interior_contDiffWithinAt_of_nat hxi
                apply iteratedFDerivWithin_domDomCongr_adjacent_succ_of_eventuallyEq
                  hu (interior_subset hxi) j
                filter_upwards [hev] with y hy
                exact ih (m + 1) (by omega) hy.2 hy.1 (Equiv.swap j.castSucc j.succ)

/-- Every finite iterated derivative of a real `C∞` map is symmetric at a point accumulated
by the interior of its unique-differentiability set. -/
theorem ContDiffWithinAt.domDomCongr_iteratedFDerivWithin_of_infty
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {x : E}
    (hf : ContDiffWithinAt ℝ ∞ f s x) (hu : UniqueDiffOn ℝ s)
    (hxs : x ∈ s) (hxi : x ∈ closure (interior s))
    {n : ℕ} (sigma : Equiv.Perm (Fin n)) :
    (iteratedFDerivWithin ℝ n f s x).domDomCongr sigma =
      iteratedFDerivWithin ℝ n f s x := by
  rcases hf.exists_mem_nhdsWithin_contDiffWithinAt_closure_interior_of_infty hxs hxi n with
    ⟨u, hu_mem, hxu, hfu⟩
  apply hf.domDomCongr_iteratedFDerivWithin_of_eqOn hu hxs hxu
    (inter_subset_right.trans interior_subset) n sigma
  intro y hy
  exact (hfu y hy.1).domDomCongr_iteratedFDerivWithin_of_nat_of_mem_interior
    hu n hy.2 sigma

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

theorem ContDiffOn.convexWithinJet
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F}
    (hs : Convex ℝ s) (hsi : (interior s).Nonempty)
    (hf : ContDiffOn ℝ ∞ f s) :
    ∃ J : (n : ℕ) → E → E[×n]→L[ℝ] F,
      (∀ n, ContinuousOn (J n) s) ∧
      (∀ x ∈ s, J 0 x (fun i => Fin.elim0 i) = f x) ∧
      (∀ x ∈ s, ∀ v, J 1 x (fun _ => v) = fderivWithin ℝ f s x v) ∧
      (∀ n x, x ∈ s → ∀ σ : Equiv.Perm (Fin n),
        (J n x).domDomCongr σ = J n x) := by
  have hu : UniqueDiffOn ℝ s := uniqueDiffOn_convex hs hsi
  refine ⟨fun n => iteratedFDerivWithin ℝ n f s, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hf.continuousOn_iteratedFDerivWithin
      (WithTop.coe_le_coe.mpr le_top) hu
  · intro x hx
    exact iteratedFDerivWithin_zero_apply _
  · intro x hx v
    exact iteratedFDerivWithin_one_apply (hu x hx) _
  · intro n x hx σ
    exact (hf x hx).domDomCongr_iteratedFDerivWithin_of_infty hu hx
      (by
        rw [hs.closure_interior_eq_closure_of_nonempty_interior hsi]
        exact subset_closure hx) σ

/-- The geometric data consumed by the partition-of-unity stage of the Whitney
extension construction.  The sets called `cube` are kept abstract here: the
construction theorem is responsible for producing them with all the metric,
covering, and overlap properties recorded below. -/
structure WhitneyCubeCover
    {E : Type*} [PseudoMetricSpace E] (s : Set E) where
  ι : Type*
  countable_index : Countable ι
  cube : ι → Set E
  enlargement : ι → Set E
  center : ι → E
  anchor : ι → E
  scale : ι → ℝ
  scale_pos : ∀ i, 0 < scale i
  anchor_mem : ∀ i, anchor i ∈ s
  anchor_nearest : ∀ i, Metric.infDist (center i) s = dist (center i) (anchor i)
  cube_subset_compl : ∀ i, cube i ⊆ sᶜ
  cube_subset_enlargement : ∀ i, cube i ⊆ enlargement i
  ball_subset_cube : ∀ i, Metric.ball (center i) (scale i / 4) ⊆ cube i
  cube_subset_closedBall : ∀ i, cube i ⊆ Metric.closedBall (center i) (scale i)
  cover_compl : sᶜ ⊆ ⋃ i, cube i
  locallyFinite_enlargement : LocallyFinite enlargement
  scale_le_infDist : ∀ i, scale i ≤ Metric.infDist (center i) s
  infDist_le_scale : ∀ i, Metric.infDist (center i) s ≤ 8 * scale i
  overlapBound : ℕ
  overlap_finite : ∀ x, {i | x ∈ enlargement i}.Finite
  overlap_card_le : ∀ x, {i | x ∈ enlargement i}.ncard ≤ overlapBound

/-- A closed nonempty subset of a finite-dimensional real normed space has a
chosen nearest point to every point.  This supplies the anchors in a Whitney
cube cover independently of the dyadic maximal-cover construction. -/
theorem exists_nearestPoint_of_isClosed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} (hs : IsClosed s) (hne : s.Nonempty)
    (x : E) : ∃ a ∈ s, Metric.infDist x s = dist x a :=
  hs.exists_infDist_eq_dist hne x

/-- The degenerate Whitney cover when the closed set is the whole space.  This
is the empty-family branch of `closedSet_whitneyCubeCover`; separating it keeps
the maximal-cube construction focused on a nonempty complement. -/
theorem closedSet_whitneyCubeCover_univ
    (E : Type*) [PseudoMetricSpace E] :
    Nonempty (WhitneyCubeCover.{_, 0} (Set.univ : Set E)) := by
  let absurdIndex : Empty → False := Empty.elim
  refine ⟨{
    ι := Empty
    countable_index := inferInstance
    cube := Empty.elim
    enlargement := Empty.elim
    center := Empty.elim
    anchor := Empty.elim
    scale := Empty.elim
    scale_pos := fun i => (absurdIndex i).elim
    anchor_mem := fun i => (absurdIndex i).elim
    anchor_nearest := fun i => (absurdIndex i).elim
    cube_subset_compl := fun i => (absurdIndex i).elim
    cube_subset_enlargement := fun i => (absurdIndex i).elim
    ball_subset_cube := fun i => (absurdIndex i).elim
    cube_subset_closedBall := fun i => (absurdIndex i).elim
    cover_compl := by simp
    locallyFinite_enlargement := locallyFinite_of_finite _
    scale_le_infDist := fun i => (absurdIndex i).elim
    infDist_le_scale := fun i => (absurdIndex i).elim
    overlapBound := 0
    overlap_finite := fun x => by
      have h : {i : Empty | x ∈ (Empty.elim i : Set E)} = ∅ := by
        ext i
        exact Empty.elim i
      rw [h]
      exact Set.finite_empty
    overlap_card_le := fun x => by
      have h : {i : Empty | x ∈ (Empty.elim i : Set E)} = ∅ := by
        ext i
        exact Empty.elim i
      rw [h]
      simp }⟩

/-- Reduction of the closed-set Whitney cover theorem to the only geometric
case: a closed nonempty proper subset. -/
theorem closedSet_whitneyCubeCover_of_proper_case
    {E : Type*} [PseudoMetricSpace E] {s : Set E}
    (hs : IsClosed s) (hne : s.Nonempty)
    (hproper : IsClosed s → s.Nonempty → s ≠ Set.univ →
      Nonempty (WhitneyCubeCover.{_, 0} s)) :
    Nonempty (WhitneyCubeCover.{_, 0} s) := by
  by_cases hsu : s = Set.univ
  · subst s
    exact closedSet_whitneyCubeCover_univ E
  · exact hproper hs hne hsu

/-- Every center in the complement of a closed nonempty finite-dimensional
set has both the positive Whitney scale and a nearest anchor in the set. -/
theorem exists_positive_infDist_nearest_of_isClosed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} (hs : IsClosed s) (hne : s.Nonempty)
    {x : E} (hx : x ∉ s) :
    0 < Metric.infDist x s ∧
      ∃ a ∈ s, Metric.infDist x s = dist x a := by
  exact ⟨(hs.notMem_iff_infDist_pos hne).1 hx,
    exists_nearestPoint_of_isClosed hs hne x⟩

end ConstructionTargets.SardConvexDomain
