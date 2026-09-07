import Mathlib

/-!
# APM m00A03: Riesz's lemma and compact-operator spectra

## Statement repairs

None.

## Encoding questions

The scalar field of the Banach space is not printed. Because part (b) discusses
the complex spectrum using `z` and `|z|`, we use the standard complex Banach
space formulation. No central object is omitted: the conclusion concerns
Mathlib's algebraic spectrum of the continuous linear operator itself.
-/

open Set Metric Filter

noncomputable section

/-- Finiteness above every strict positive cutoff also gives finiteness on the
closed annulus used in the usual Riesz--Schauder contradiction. -/
lemma apm_m00A03_finite_norm_ge_of_finite_norm_gt
    (s : Set ℂ)
    (h : ∀ ε : ℝ, 0 < ε → {z ∈ s | ε < ‖z‖}.Finite)
    (ε : ℝ) (hε : 0 < ε) : {z ∈ s | ε ≤ ‖z‖}.Finite := by
  apply (h (ε / 2) (by positivity)).subset
  intro z hz
  exact ⟨hz.1, (half_lt_self hε).trans_le hz.2⟩

lemma apm_m00A03_derivedSet_subset_zero_of_annular_finite
    (s : Set ℂ) (h : ∀ ε : ℝ, 0 < ε → {z ∈ s | ε ≤ ‖z‖}.Finite) :
    derivedSet s ⊆ {0} := by
  intro x hx
  simp only [Set.mem_singleton_iff]
  by_contra hx0
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let T : Set ℂ := {z ∈ s | ‖x‖ / 2 ≤ ‖z‖}
  have hT : T.Finite := h (‖x‖ / 2) (by positivity)
  have hTdiff : (T \ {x}).Finite := hT.diff
  have hopen : IsOpen ((T \ {x})ᶜ) := hTdiff.isClosed.isOpen_compl
  have hnhds : ball x (‖x‖ / 2) ∩ (T \ {x})ᶜ ∈ nhds x :=
    inter_mem (ball_mem_nhds x (by positivity)) (hopen.mem_nhds (by simp))
  obtain ⟨y, hy, hyne⟩ := (accPt_iff_nhds.mp hx)
    (ball x (‖x‖ / 2) ∩ (T \ {x})ᶜ) hnhds
  have hydist : dist y x < ‖x‖ / 2 := by
    simpa [dist_comm] using hy.1.1
  have hynorm : ‖x‖ / 2 ≤ ‖y‖ := by
    have htri := norm_sub_norm_le x y
    rw [← dist_eq_norm] at htri
    have hydist' : dist x y < ‖x‖ / 2 := by simpa [dist_comm] using hydist
    nlinarith
  have hyT : y ∈ T := ⟨hy.2, hynorm⟩
  exact hy.1.2 ⟨hyT, by simpa [hyne]⟩

/-- Why this unblocks `apm_m00a03`: this is the precise Riesz--Schauder
finiteness assertion still missing from Mathlib. The already compiled
topological lemma derives the claimed spectral derived-set bound from it. -/
theorem apm_m00A03_bridge_1
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] (A : X →L[ℂ] X) (hA : IsCompactOperator A) :
    ∀ ε : ℝ, 0 < ε → {z ∈ spectrum ℂ A | ε < ‖z‖}.Finite := by
  intro ε hε
  let S : Set ℂ := {z ∈ spectrum ℂ A | ε < ‖z‖}
  by_contra hS
  have hSinf : S.Infinite := hS
  letI : Infinite S := Set.infinite_coe_iff.mpr hSinf
  let e : ℕ ↪ S := Infinite.natEmbedding S
  let μ : ℕ → ℂ := fun n ↦ (e n : ℂ)
  have hμ : Function.Injective μ := fun _ _ h ↦ e.injective (Subtype.ext h)
  have hμ_mem (n : ℕ) : μ n ∈ spectrum ℂ A := (e n).property.1
  have hμ_norm (n : ℕ) : ε < ‖μ n‖ := (e n).property.2
  have hμ_ne (n : ℕ) : μ n ≠ 0 := by
    intro hn
    simpa [hn] using (lt_trans hε (hμ_norm n))
  have heig (n : ℕ) : Module.End.HasEigenvalue (A : Module.End ℂ X) (μ n) :=
    (hA.hasEigenvalue_iff_mem_spectrum (hμ_ne n)).mpr (hμ_mem n)
  choose x hx using fun n ↦ (heig n).exists_hasEigenvector
  have hli : LinearIndependent ℂ x :=
    Module.End.eigenvectors_linearIndependent' (A : Module.End ℂ X) μ hμ x hx
  let V : ℕ → Submodule ℂ X := fun n ↦ Submodule.span ℂ (x '' Set.Iio n)
  have hV_mono {m n : ℕ} (hmn : m ≤ n) : V m ≤ V n := by
    apply Submodule.span_mono
    rintro y ⟨i, hi, rfl⟩
    exact ⟨i, lt_of_lt_of_le hi hmn, rfl⟩
  have hxV (n : ℕ) : x n ∈ V (n + 1) :=
    Submodule.subset_span ⟨n, Nat.lt_succ_self n, rfl⟩
  have hxnot (n : ℕ) : x n ∉ V n := by
    intro hxn
    have hall := (linearIndependent_iff_notMem_span.mp hli n)
    apply hall
    apply (Submodule.span_mono ?_) hxn
    rintro y ⟨i, hi, rfl⟩
    exact ⟨i, by
      simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_singleton_iff]
      exact (show i < n from hi).ne, rfl⟩
  have hVclosed (n : ℕ) : IsClosed (V n : Set X) := by
    letI : FiniteDimensional ℂ (V n) :=
      FiniteDimensional.span_of_finite ℂ
        ((Set.finite_Iio n).image x)
    exact Submodule.closed_of_finiteDimensional (V n)
  have hVproper (n : ℕ) : ∃ y : V (n + 1), y ∉ Submodule.comap (V (n + 1)).subtype (V n) := by
    exact ⟨⟨x n, hxV n⟩, hxnot n⟩
  choose z hzV hznorm hzfar using fun n ↦
    riesz_lemma_of_lt_one
      (F := Submodule.comap (V (n + 1)).subtype (V n))
      ((hVclosed n).preimage continuous_subtype_val) (hVproper n)
      (r := (1 / 2 : ℝ)) (by norm_num)
  let w : ℕ → X := fun n ↦ z n
  have hwV (n : ℕ) : w n ∈ V (n + 1) := (z n).property
  have hwnorm (n : ℕ) : ‖w n‖ = 1 := hznorm n
  have hwfar (n : ℕ) (y : X) (hy : y ∈ V n) : (1 / 2 : ℝ) ≤ ‖w n - y‖ := by
    have := hzfar n ⟨y, hV_mono (Nat.le_succ n) hy⟩ hy
    simpa [w, dist_eq_norm] using this
  have hA_eig (n : ℕ) : A (x n) = μ n • x n := (hx n).apply_eq_smul
  have hA_maps (n : ℕ) (y : X) (hy : y ∈ V n) : A y ∈ V n := by
    apply Submodule.span_induction (p := fun y _ ↦ A y ∈ V n) _ (by simp)
      (fun _ _ _ _ ha hb ↦ by simpa using (V n).add_mem ha hb)
      (fun c y _ ha ↦ by simpa using (V n).smul_mem c ha) hy
    rintro _ ⟨i, hi, rfl⟩
    rw [hA_eig]
    exact (V n).smul_mem _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hshift (n : ℕ) (y : X) (hy : y ∈ V (n + 1)) :
      A y - μ n • y ∈ V n := by
    apply Submodule.span_induction (p := fun y _ ↦ A y - μ n • y ∈ V n) _
      (by simp) (fun a b _ _ ha hb ↦ by simpa [map_add, smul_add, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm] using (V n).add_mem ha hb)
      (fun c y _ hy ↦ by
        simpa [map_smul, smul_sub, smul_smul, mul_comm] using (V n).smul_mem c hy) hy
    rintro _ ⟨i, hi, rfl⟩
    rw [hA_eig]
    by_cases hin : i = n
    · subst i; simp
    · have hil : i < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hin
      exact (V n).sub_mem ((V n).smul_mem _ (Submodule.subset_span ⟨i, hil, rfl⟩))
        ((V n).smul_mem _ (Submodule.subset_span ⟨i, hil, rfl⟩))
  have hp : Pairwise fun m n ↦ ε / 2 < ‖A (w m) - A (w n)‖ := by
    apply Pairwise.of_lt
    · intro m n h
      simpa [norm_sub_rev] using h
    intro m n hmn
    let u : X := (μ n)⁻¹ • (A (w m) - (A (w n) - μ n • w n))
    have huV : u ∈ V n := by
      apply (V n).smul_mem
      exact (V n).sub_mem (hA_maps n _ (hV_mono hmn (hwV m)))
        (hshift n _ (hwV n))
    have heq : μ n • (w n - u) = A (w n) - A (w m) := by
      dsimp [u]
      rw [smul_sub, smul_inv_smul₀ (hμ_ne n)]
      module
    have hsep := hwfar n u huV
    have hnμ : ε < ‖μ n‖ := hμ_norm n
    rw [norm_sub_rev, ← heq, norm_smul]
    nlinarith [mul_le_mul_of_nonneg_left hsep (norm_nonneg (μ n))]
  obtain ⟨K, hK, hsub⟩ := hA.image_closedBall_subset_compact 1
  have hAwK (n : ℕ) : A (w n) ∈ K := hsub ⟨w n, by simp [hwnorm], rfl⟩
  obtain ⟨y, _, ψ, hψ, hlim⟩ := hK.tendsto_subseq hAwK
  have hcauchy := hlim.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy (ε / 2) (by positivity)
  have hclose : ‖A (w (ψ (N + 1))) - A (w (ψ N))‖ < ε / 2 := by
    simpa [dist_eq_norm_sub] using hN (N + 1) (by omega)
  have hneψ : ψ (N + 1) ≠ ψ N := hψ.injective.ne (by omega)
  exact (not_lt_of_ge (le_of_lt (hp hneψ))) hclose

theorem apm_m00a03
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] :
    (∀ (Y Z : Submodule ℂ X),
      Y ≤ Z → Y ≠ Z → IsClosed (Y : Set X) →
        ∃ z ∈ Z, ‖z‖ = 1 ∧ (1 / 2 : ℝ) ≤ infDist z (Y : Set X)) ∧
    ∀ A : X →L[ℂ] X, IsCompactOperator A →
      (∀ ε : ℝ, 0 < ε →
        {z ∈ spectrum ℂ A | ε < ‖z‖}.Finite) ∧
      derivedSet (spectrum ℂ A) ⊆ {0} := by
  constructor
  · intro Y Z hYZ hne hYclosed
    have hnle : ¬ Z ≤ Y := by
      intro hZY
      exact hne (le_antisymm hYZ hZY)
    obtain ⟨w, hwZ, hwY⟩ := SetLike.not_le_iff_exists.mp hnle
    let F : Submodule ℂ Z := Y.comap Z.subtype
    have hFclosed : IsClosed (F : Set Z) := by
      exact hYclosed.preimage continuous_subtype_val
    have hFproper : ∃ x : Z, x ∉ F := ⟨⟨w, hwZ⟩, hwY⟩
    obtain ⟨z, _, hznorm, hzfar⟩ :=
      riesz_lemma_of_lt_one hFclosed hFproper (r := (1 / 2 : ℝ)) (by norm_num)
    refine ⟨(z : X), z.property, hznorm, ?_⟩
    rw [Metric.le_infDist ⟨0, Y.zero_mem⟩]
    intro y hy
    have hyZ : y ∈ Z := hYZ hy
    have hyF : (⟨y, hyZ⟩ : Z) ∈ F := hy
    have := hzfar ⟨y, hyZ⟩ hyF
    simpa [dist_eq_norm] using this
  · intro A hA
    have hfinite : ∀ ε : ℝ, 0 < ε →
        {z ∈ spectrum ℂ A | ε < ‖z‖}.Finite := by
      exact apm_m00A03_bridge_1 A hA
    refine ⟨hfinite, ?_⟩
    exact apm_m00A03_derivedSet_subset_zero_of_annular_finite
      (spectrum ℂ A) (fun ε hε ↦
        apm_m00A03_finite_norm_ge_of_finite_norm_gt
          (spectrum ℂ A) hfinite ε hε)

#print axioms apm_m00a03
