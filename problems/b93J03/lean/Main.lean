import Mathlib

/-!
# APM b93J03

## Statement repairs

Part (a) as printed needs `V` nonzero, since the zero vector space has no
eigenvector, so `Nontrivial V` is a hypothesis of that clause only. Part (b) holds
for every `V`.

## Encoding questions

None. The ordered basis is indexed by `Fin (finrank k V)`, and upper
triangularity is Mathlib's `Matrix.BlockTriangular id` predicate.
-/

lemma apm_b93J03_ker_ne_bot_of_isNilpotent
    {k M : Type*} [Field k] [AddCommGroup M] [Module k M] [Nontrivial M]
    (f : Module.End k M) (hf : IsNilpotent f) : LinearMap.ker f ≠ ⊥ := by
  intro hker
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
  obtain ⟨n, hn⟩ := hf
  have hpow : Function.Injective (f ^ n) := by
    clear hn
    induction n with
    | zero => simpa using Function.injective_id
    | succ n ih =>
        rw [pow_succ]
        simpa only [Module.End.mul_apply] using ih.comp hinj
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  apply hx
  apply hpow
  simp [hn]

lemma apm_b93J03_exists_nonzero_mem_ker_of_isNilpotent_restrict
    {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (f : Module.End k M) (p : Submodule k M) (hp : ∀ x ∈ p, f x ∈ p)
    (hp0 : p ≠ ⊥) (hf : IsNilpotent (f.restrict hp)) :
    ∃ x : M, x ≠ 0 ∧ x ∈ p ∧ f x = 0 := by
  letI : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hp0
  have hker := apm_b93J03_ker_ne_bot_of_isNilpotent (f.restrict hp) hf
  obtain ⟨x, hxker, hx0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hker)
  refine ⟨x, ?_, x.property, ?_⟩
  · simpa only [Submodule.mem_bot, Subtype.ext_iff] using hx0
  · exact congr_arg Subtype.val hxker

lemma apm_b93J03_exists_nonzero_common_kernel_finset
    {k M ι : Type*} [Field k] [AddCommGroup M] [Module k M] [Nontrivial M]
    [DecidableEq ι]
    (f : ι → Module.End k M) (s : Finset ι)
    (hcomm : ∀ i j, Commute (f i) (f j))
    (hnil : ∀ i ∈ s, IsNilpotent (f i)) :
    ∃ x : M, x ≠ 0 ∧ ∀ i ∈ s, f i x = 0 := by
  induction s using Finset.induction_on with
  | empty =>
      obtain ⟨x, hx⟩ := exists_ne (0 : M)
      exact ⟨x, hx, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨x, hx0, hx⟩ := ih (fun i hi ↦ hnil i (Finset.mem_insert_of_mem hi))
      let p : Submodule k M := ⨅ i ∈ s, LinearMap.ker (f i)
      have hp0 : p ≠ ⊥ := by
        intro hp
        have hxp : x ∈ p := by simpa [p] using hx
        rw [hp] at hxp
        exact hx0 (by simpa using hxp)
      have hp : ∀ y ∈ p, f a y ∈ p := by
        intro y hy
        simp only [p, Submodule.mem_iInf] at hy ⊢
        intro i hi
        simp only [LinearMap.mem_ker]
        rw [← Module.End.mul_apply, (hcomm i a).eq, Module.End.mul_apply, hy i hi, map_zero]
      have hnilRestrict : IsNilpotent ((f a).restrict hp) :=
        Module.End.isNilpotent.restrict hp (hnil a (Finset.mem_insert_self a s))
      obtain ⟨y, hy0, hyp, hya⟩ :=
        apm_b93J03_exists_nonzero_mem_ker_of_isNilpotent_restrict (f a) p hp hp0 hnilRestrict
      refine ⟨y, hy0, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hya
      · simp only [p, Submodule.mem_iInf] at hyp
        exact hyp i hi

lemma apm_b93J03_exists_nonzero_common_kernel
    {k M ι : Type*} [Field k] [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] [Nontrivial M]
    (f : ι → Module.End k M) (hcomm : ∀ i j, Commute (f i) (f j))
    (hnil : ∀ i, IsNilpotent (f i)) :
    ∃ x : M, x ≠ 0 ∧ ∀ i, f i x = 0 := by
  let S : Set (Module.End k M) := Set.range f
  obtain ⟨g, hgS, hgspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq k S
  choose idx hidx using hgS
  have hgcomm : ∀ i j, Commute (g i) (g j) := by
    intro i j
    rw [← hidx i, ← hidx j]
    exact hcomm (idx i) (idx j)
  have hgnil : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank k (Submodule.span k S)))),
      IsNilpotent (g i) := by
    intro i hi
    rw [← hidx i]
    exact hnil (idx i)
  obtain ⟨x, hx0, hx⟩ := apm_b93J03_exists_nonzero_common_kernel_finset
    g Finset.univ hgcomm hgnil
  refine ⟨x, hx0, ?_⟩
  let p : Submodule k (Module.End k M) :=
    { carrier := {u | u x = 0}
      zero_mem' := rfl
      add_mem' := by
        intro u v hu hv
        change u x = 0 at hu
        change v x = 0 at hv
        change (u + v) x = 0
        simp [hu, hv]
      smul_mem' := by
        intro c u hu
        change u x = 0 at hu
        change (c • u) x = 0
        simp [hu] }
  have hgp : Submodule.span k (Set.range g) ≤ p := by
    rw [Submodule.span_le]
    rintro u ⟨i, rfl⟩
    change g i x = 0
    exact hx i (Finset.mem_univ i)
  intro i
  have hfiS : f i ∈ Submodule.span k S := Submodule.subset_span ⟨i, rfl⟩
  have hfi : f i ∈ p := hgp (hgspan.symm ▸ hfiS)
  change f i x = 0 at hfi
  exact hfi

lemma apm_b93J03_exists_nonzero_simultaneous_maxGenEigenspace
    (k V ι : Type*) [Field k] [IsAlgClosed k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (f : ι → Module.End k V)
    (hcomm : Pairwise fun i j : ι ↦ Commute (f i) (f j)) :
    ∃ χ : ι → k, (⨅ i, (f i).maxGenEigenspace (χ i)) ≠ ⊥ := by
  have htop : ⨆ χ : ι → k, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by
    apply Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f hcomm
    intro i
    exact Module.End.iSup_maxGenEigenspace_eq_top (f i)
  by_contra h
  push_neg at h
  have hz : (⨆ χ : ι → k, ⨅ i, (f i).maxGenEigenspace (χ i)) = ⊥ :=
    iSup_eq_bot.mpr h
  rw [htop] at hz
  exact top_ne_bot hz

lemma apm_b93J03_exists_common_eigenvector
    (k V ι : Type*) [Field k] [IsAlgClosed k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (f : ι → Module.End k V)
    (hcomm : Pairwise fun i j : ι ↦ Commute (f i) (f j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ μ : k, f i v = μ • v := by
  obtain ⟨χ, hp0⟩ :=
    apm_b93J03_exists_nonzero_simultaneous_maxGenEigenspace k V ι f hcomm
  let p : Submodule k V := ⨅ i, (f i).maxGenEigenspace (χ i)
  have hcomm' (i j : ι) : Commute (f i) (f j) := by
    rcases eq_or_ne i j with rfl | hij
    · exact Commute.refl (f i)
    · exact hcomm hij
  have hfmap (i : ι) : ∀ x ∈ p, f i x ∈ p := by
    intro x hx
    simp only [p, Submodule.mem_iInf] at hx ⊢
    intro j
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm' j i) (χ j) (hx j)
  let shift : ι → Module.End k V :=
    fun i ↦ f i - algebraMap k (Module.End k V) (χ i)
  have hshiftmap (i : ι) : ∀ x ∈ p, shift i x ∈ p := by
    intro x hx
    change f i x - χ i • x ∈ p
    exact p.sub_mem (hfmap i x hx) (p.smul_mem (χ i) hx)
  let g : ι → Module.End k p := fun i ↦ (shift i).restrict (hshiftmap i)
  have hgcomm (i j : ι) : Commute (g i) (g j) := by
    show g i * g j = g j * g i
    ext x
    simp only [g, LinearMap.restrict_apply, shift, LinearMap.sub_apply,
      Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
      Module.End.mul_apply, map_sub, map_smul]
    rw [← Module.End.mul_apply, (hcomm' i j).eq, Module.End.mul_apply]
    module
  have hgnil (i : ι) : IsNilpotent (g i) := by
    apply Module.End.isNilpotent_restrict_of_le
      (q := (f i).maxGenEigenspace (χ i)) (iInf_le _ i)
    exact Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (f i) (χ i)
  letI : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hp0
  obtain ⟨v, hv0, hv⟩ := apm_b93J03_exists_nonzero_common_kernel g hgcomm hgnil
  refine ⟨v, ?_, ?_⟩
  · exact fun h ↦ hv0 (Subtype.ext h)
  · intro i
    refine ⟨χ i, ?_⟩
    have hvi := congr_arg Subtype.val (hv i)
    simpa only [g, LinearMap.restrict_apply, shift, LinearMap.sub_apply,
      Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
      ZeroMemClass.coe_zero, sub_eq_zero] using hvi

lemma apm_b93J03_sumQuot_blockTriangular
    {k V m n : Type*} [Field k] [AddCommGroup V] [Module k V]
    [Fintype m] [Fintype n] [LinearOrder m] [LinearOrder n]
    (W : Submodule k V) (bW : Module.Basis m k W)
    (bQ : Module.Basis n k (V ⧸ W)) (f : Module.End k V)
    (hf : ∀ x ∈ W, f x ∈ W)
    (hW : (LinearMap.toMatrix bW bW (f.restrict hf)).BlockTriangular id)
    (hQ : (LinearMap.toMatrix bQ bQ (W.mapQ W f hf)).BlockTriangular id) :
    (LinearMap.toMatrix (Module.Basis.sumQuot bW bQ)
      (Module.Basis.sumQuot bW bQ) f).BlockTriangular id := by
  intro i j hji
  rcases i with i | i <;> rcases j with j | j
  · have hji' : j < i := by simpa using hji
    rw [LinearMap.toMatrix_apply, Module.Basis.sumQuot_inl,
      Module.Basis.sumQuot_repr_inl_of_mem _ _ _ (hf _ (bW j).property)]
    simpa only [LinearMap.toMatrix_apply, LinearMap.restrict_apply] using hW hji'
  · simp at hji
  · rw [LinearMap.toMatrix_apply, Module.Basis.sumQuot_inl]
    exact Module.Basis.sumQuot_repr_inr_of_mem bW bQ (f (bW j)) (hf _ (bW j).property) i
  · have hji' : j < i := by simpa using hji
    rw [LinearMap.toMatrix_apply, Module.Basis.sumQuot_repr_inr]
    have hm : W.mkQ (f (Module.Basis.sumQuot bW bQ (Sum.inr j))) =
        W.mapQ W f hf (bQ j) := by
      rw [← Module.Basis.sumQuot_inr bW bQ j]
      exact (Submodule.mapQ_apply W W f _).symm
    rw [hm]
    simpa only [LinearMap.toMatrix_apply] using hQ hji'

lemma apm_b93J03_fin_basis_sumQuot_blockTriangular
    {k V : Type*} {m n : ℕ} [Field k] [AddCommGroup V] [Module k V]
    (W : Submodule k V) (bW : Module.Basis (Fin m) k W)
    (bQ : Module.Basis (Fin n) k (V ⧸ W)) (f : Module.End k V)
    (hf : ∀ x ∈ W, f x ∈ W)
    (hW : (LinearMap.toMatrix bW bW (f.restrict hf)).BlockTriangular id)
    (hQ : (LinearMap.toMatrix bQ bQ (W.mapQ W f hf)).BlockTriangular id) :
    (LinearMap.toMatrix
      ((Module.Basis.sumQuot bW bQ).reindex finSumFinEquiv)
      ((Module.Basis.sumQuot bW bQ).reindex finSumFinEquiv) f).BlockTriangular id := by
  intro i j hji
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j
  · have hji' : j < i := by simpa using hji
    simp only [LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply,
      Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.sumQuot_inl,
      Module.Basis.sumQuot_repr_inl_of_mem _ _ _ (hf _ (bW j).property)]
    simpa only [LinearMap.toMatrix_apply, LinearMap.restrict_apply] using hW hji'
  · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] at hji
    have hi := i.isLt
    have hj := j.isLt
    change m + j.val < i.val at hji
    omega
  · simp only [LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply,
      Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.sumQuot_inl]
    exact Module.Basis.sumQuot_repr_inr_of_mem bW bQ (f (bW j)) (hf _ (bW j).property) i
  · have hji' : j < i := by simpa using hji
    simp only [LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply,
      Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.sumQuot_repr_inr]
    have hm : W.mkQ (f (Module.Basis.sumQuot bW bQ (Sum.inr j))) =
        W.mapQ W f hf (bQ j) := by
      rw [← Module.Basis.sumQuot_inr bW bQ j]
      exact (Submodule.mapQ_apply W W f _).symm
    rw [hm]
    simpa only [LinearMap.toMatrix_apply] using hQ hji'

lemma apm_b93J03_mapQ_commute
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (W : Submodule k V) (f g : Module.End k V)
    (hf : ∀ x ∈ W, f x ∈ W) (hg : ∀ x ∈ W, g x ∈ W)
    (hcomm : Commute f g) :
    Commute (W.mapQ W f hf) (W.mapQ W g hg) := by
  show W.mapQ W f hf * W.mapQ W g hg = W.mapQ W g hg * W.mapQ W f hf
  apply W.linearMap_qext
  ext x
  simp only [LinearMap.comp_apply, Module.End.mul_apply, Submodule.mkQ_apply,
    Submodule.mapQ_apply]
  exact congr_arg Submodule.Quotient.mk (congr_arg (fun u : Module.End k V ↦ u x) hcomm.eq)

lemma apm_b93J03_exists_fin_one_basis_span
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (v : V) (hv : v ≠ 0) :
    Nonempty (Module.Basis (Fin 1) k (Submodule.span k {v})) := by
  let vec : Fin 1 → V := fun _ ↦ v
  have hli : LinearIndependent k vec := linearIndependent_unique_iff.mpr hv
  let b := Module.Basis.span hli
  have hrange : Set.range vec = {v} := by
    ext x
    simp [vec]
  exact ⟨hrange ▸ b⟩

lemma apm_b93J03_fin_one_blockTriangular
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (_b : Module.Basis (Fin 1) k V) (f : Module.End k V) :
    (LinearMap.toMatrix _b _b f).BlockTriangular id := by
  intro i j hji
  omega

lemma apm_b93J03_finrank_quotient_lt
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (W : Submodule k V) (hW : W ≠ ⊥) :
    Module.finrank k (V ⧸ W) < Module.finrank k V := by
  have hpos : 0 < Module.finrank k W :=
    Nat.zero_lt_of_lt (Submodule.one_le_finrank_iff.mpr hW)
  have hrank := W.finrank_quotient_add_finrank
  omega

lemma apm_b93J03_exists_simultaneous_triangular_basis
    (k V ι : Type*) [Field k] [IsAlgClosed k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V]
    (f : ι → Module.End k V)
    (hcomm : Pairwise fun i j : ι ↦ Commute (f i) (f j)) :
    ∃ b : Module.Basis (Fin (Module.finrank k V)) k V,
      ∀ i, (LinearMap.toMatrix b b (f i)).BlockTriangular id := by
  generalize hn : Module.finrank k V = n
  induction n using Nat.strongRecOn generalizing V with
  | ind n ih =>
      rcases n with _ | n
      · haveI : Subsingleton V := Module.finrank_zero_iff.mp hn
        refine ⟨Module.Basis.empty V, ?_⟩
        intro i r c hcr
        exact Fin.elim0 r
      · letI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hn
        obtain ⟨v, hv0, hv⟩ := apm_b93J03_exists_common_eigenvector k V ι f hcomm
        let W : Submodule k V := Submodule.span k {v}
        have hW0 : W ≠ ⊥ := by
          intro h
          have : v ∈ W := Submodule.subset_span (Set.mem_singleton v)
          rw [h] at this
          exact hv0 (by simpa using this)
        choose μ hμ using hv
        have hf (i : ι) : ∀ x ∈ W, f i x ∈ W := by
          intro x hx
          have hle : W ≤ W.comap (f i) := by
            change Submodule.span k {v} ≤ W.comap (f i)
            rw [Submodule.span_le]
            intro y hy
            rw [Set.mem_singleton_iff.mp hy]
            change f i v ∈ W
            rw [hμ i]
            exact W.smul_mem (μ i) (Submodule.subset_span (Set.mem_singleton v))
          exact hle hx
        let fq : ι → Module.End k (V ⧸ W) := fun i ↦ W.mapQ W (f i) (hf i)
        have hqcomm : Pairwise fun i j : ι ↦ Commute (fq i) (fq j) := by
          intro i j hij
          exact apm_b93J03_mapQ_commute W (f i) (f j) (hf i) (hf j) (hcomm hij)
        have hlt : Module.finrank k (V ⧸ W) < Nat.succ n := by
          simpa only [hn] using apm_b93J03_finrank_quotient_lt W hW0
        obtain ⟨bQ, hbQ⟩ := ih _ hlt (V := V ⧸ W) fq hqcomm rfl
        obtain ⟨bW⟩ := apm_b93J03_exists_fin_one_basis_span (k := k) v hv0
        have hWrank : Module.finrank k W = 1 := by
          exact finrank_span_singleton hv0
        have hrank : 1 + Module.finrank k (V ⧸ W) = Nat.succ n := by
          calc
            1 + Module.finrank k (V ⧸ W) = Module.finrank k (V ⧸ W) +
                Module.finrank k W := by rw [hWrank, add_comm]
            _ = Module.finrank k V := W.finrank_quotient_add_finrank
            _ = Nat.succ n := hn
        let bs := (Module.Basis.sumQuot bW bQ).reindex finSumFinEquiv
        let b : Module.Basis (Fin (Nat.succ n)) k V := bs.reindex (finCongr hrank)
        refine ⟨b, ?_⟩
        intro i
        have hs : (LinearMap.toMatrix bs bs (f i)).BlockTriangular id :=
          apm_b93J03_fin_basis_sumQuot_blockTriangular W bW bQ (f i) (hf i)
            (apm_b93J03_fin_one_blockTriangular bW ((f i).restrict (hf i))) (hbQ i)
        intro r c hcr
        have hcr' : (finCongr hrank).symm c < (finCongr hrank).symm r := by
          simpa using hcr
        simpa only [b, LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply,
          Module.Basis.reindex_apply] using hs hcr'

theorem apm_b93j03 :
    ∀ (k V : Type*) [Field k] [IsAlgClosed k] [AddCommGroup V]
        [Module k V] [FiniteDimensional k V]
        (A : Set (V →ₗ[k] V)),
      (∀ a ∈ A, ∀ b ∈ A, a.comp b = b.comp a) →
      (Nontrivial V → ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, ∃ μ : k, a v = μ • v) ∧
      (∃ basis : Module.Basis (Fin (Module.finrank k V)) k V,
        ∀ a ∈ A, (LinearMap.toMatrix basis basis a).BlockTriangular id) := by
  intro k V _ _ _ _ _ A hA
  let f : A → Module.End k V := fun a ↦ a.1
  have hcomm : Pairwise fun i j : A ↦ Commute (f i) (f j) := by
    intro i j hij
    change (i.1.comp j.1) = (j.1.comp i.1)
    exact hA i.1 i.2 j.1 j.2
  refine ⟨fun hV ↦ ?_, ?_⟩
  · obtain ⟨v, hv0, hv⟩ := apm_b93J03_exists_common_eigenvector k V A f hcomm
    exact ⟨v, hv0, fun a ha ↦ by simpa only [f] using hv ⟨a, ha⟩⟩
  · obtain ⟨b, hb⟩ := apm_b93J03_exists_simultaneous_triangular_basis k V A f hcomm
    exact ⟨b, fun a ha ↦ by simpa only [f] using hb ⟨a, ha⟩⟩
