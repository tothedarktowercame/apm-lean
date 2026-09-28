import Mathlib

/-!
# APM m99J04

## Statement repairs

The eigenbasis index was previously restricted to `Type 0`, although the
natural index assembled from the eigenspaces of a scalar field `𝕜 : Type u𝕜`
and a Hilbert space `H : Type uH` lives in `Type (max u𝕜 uH)`. Both
eigenbasis existentials are made universe-polymorphic at that natural level.

## Encoding questions

“Basis” means a Hilbert basis, not an algebraic Hamel basis. The generalized
eigenvectors are encoded as the image of a Hilbert basis under the given
continuous linear equivalence; this is precisely a topological (Riesz) basis
and does not falsely claim that its vectors are orthonormal in the original
inner product.
-/

noncomputable section

universe u𝕜 uH

def apm_m99j04_conjugate
    {𝕜 : Type u𝕜} {H : Type uH} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H ≃L[𝕜] H) (T : H →L[𝕜] H) : H →L[𝕜] H :=
  (ContinuousLinearMap.adjoint A.toContinuousLinearMap).comp
    (T.comp A.toContinuousLinearMap)

def apm_m99j04_weight
    {𝕜 : Type u𝕜} {H : Type uH} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H ≃L[𝕜] H) : H →L[𝕜] H :=
  (ContinuousLinearMap.adjoint A.symm.toContinuousLinearMap).comp
    A.symm.toContinuousLinearMap

def apm_m99j04_HasEigenHilbertBasis
    {𝕜 : Type u𝕜} {H : Type uH} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H) : Prop :=
  ∃ (ι : Type (max u𝕜 uH)) (b : HilbertBasis ι 𝕜 H)
      (eigenvalue : ι → 𝕜),
    ∀ i, star (eigenvalue i) = eigenvalue i ∧
      T (b i) = eigenvalue i • b i

lemma apm_m99j04_eigen_hilbert_basis
    (𝕜 : Type u𝕜) (H : Type uH) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H) (hc : IsCompactOperator T)
    (hs : ContinuousLinearMap.adjoint T = T) :
    ∃ (ι : Type (max u𝕜 uH)) (b : HilbertBasis ι 𝕜 H) (e : ι → 𝕜),
      ∀ i, star (e i) = e i ∧ T (b i) = e i • b i := by
  let hsym : T.IsSymmetric := by
    exact (ContinuousLinearMap.eq_adjoint_iff T T).mp hs.symm
  have hex : ∀ μ : 𝕜, ∃ (s : Set (Module.End.eigenspace (T : Module.End 𝕜 H) μ))
      (b : HilbertBasis s 𝕜 (Module.End.eigenspace (T : Module.End 𝕜 H) μ)),
      ⇑b = ((↑) : s → Module.End.eigenspace (T : Module.End 𝕜 H) μ) := by
    intro μ
    exact @exists_hilbertBasis 𝕜 _
      (Module.End.eigenspace (T : Module.End 𝕜 H) μ) _ _
      ((ContinuousLinearMap.isClosed_eigenspace T μ).completeSpace_coe)
  choose s b hb using hex
  let v : (Σ μ : 𝕜, s μ) → H := fun i ↦ (b i.1 i.2 : H)
  have hborth : ∀ μ, Orthonormal 𝕜 (b μ) := by
    intro μ
    exact (b μ).orthonormal
  have hv : Orthonormal 𝕜 v := by
    exact hsym.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
      hborth
  have hvbot : Submodule.orthogonal (Submodule.span 𝕜 (Set.range v)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hxall : x ∈ Submodule.orthogonal
        (⨆ μ, Module.End.eigenspace (T : Module.End 𝕜 H) μ) := by
      rw [Submodule.mem_orthogonal']
      intro y hy
      have hmem : ∀ (μ : 𝕜) (y : H),
          y ∈ Module.End.eigenspace (T : Module.End 𝕜 H) μ →
          inner 𝕜 x y = 0 := by
        intro μ y hy
        have hz : ∀ i, inner 𝕜 x (b μ i) = 0 := by
            intro i
            apply Submodule.inner_left_of_mem_orthogonal
            · exact Submodule.subset_span (show v ⟨μ, i⟩ ∈ Set.range v from ⟨⟨μ, i⟩, rfl⟩)
            · exact hx
        have hsum := ((b μ).hasSum_repr ⟨y, hy⟩).mapL
          (Module.End.eigenspace (T : Module.End 𝕜 H) μ).subtypeₗᵢ.toContinuousLinearMap
        have hinner := hsum.mapL (innerSL 𝕜 x)
        calc
          inner 𝕜 x y = ∑' i,
              (b μ).repr ⟨y, hy⟩ i * inner 𝕜 x (b μ i) := by
                simpa using hinner.tsum_eq.symm
          _ = ∑' _i : s μ, (0 : 𝕜) := by
            congr 1
            funext i
            rw [hz i, mul_zero]
          _ = 0 := tsum_zero
      exact Submodule.iSup_induction
        (motive := fun y ↦ inner 𝕜 x y = 0)
        (fun μ ↦ Module.End.eigenspace (T : Module.End 𝕜 H) μ) hy
        hmem (by simp) (fun y z hy hz ↦ by simp [inner_add_right, hy, hz])
    have hspectral := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hsym
    simpa [hspectral] using hxall
  let B : HilbertBasis (Σ μ : 𝕜, s μ) 𝕜 H := HilbertBasis.mkOfOrthogonalEqBot hv hvbot
  refine ⟨(Σ μ : 𝕜, s μ), B, fun i ↦ i.1, ?_⟩
  intro i
  have hi : (b i.1 i.2 : H) ∈ Module.End.eigenspace (T : Module.End 𝕜 H) i.1 := (b i.1 i.2).property
  have heig : T (b i.1 i.2) = i.1 • (b i.1 i.2 : H) := by
    exact Module.End.mem_eigenspace_iff.mp hi
  have hreal : star i.1 = i.1 := hsym.conj_eigenvalue_eq_self
    (Module.End.hasEigenvalue_of_hasEigenvector ⟨hi, by
      intro hz
      apply (hborth i.1).ne_zero i.2
      exact Subtype.ext hz⟩)
  simpa [B, v] using And.intro hreal heig


lemma apm_m99j04_weight_inner
    {𝕜 : Type u𝕜} {H : Type uH} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H ≃L[𝕜] H) (x y : H) :
    inner 𝕜 (apm_m99j04_weight A (A x)) (A y) = inner 𝕜 x y := by
  simp [apm_m99j04_weight, ContinuousLinearMap.adjoint_inner_left]

/-- An eigenvector of the congruence transports to a generalized eigenvector
for the original operator and the induced weight. -/
lemma apm_m99j04_generalized_eigenvector
    {𝕜 : Type u𝕜} {H : Type uH} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H ≃L[𝕜] H) (T : H →L[𝕜] H) (w : H) (eigenvalue : 𝕜)
    (hw : apm_m99j04_conjugate A T w = eigenvalue • w) :
    T (A w) = eigenvalue • apm_m99j04_weight A (A w) := by
  have h := congrArg
    (fun z => ContinuousLinearMap.adjoint A.symm.toContinuousLinearMap z) hw
  have hinv :
      (ContinuousLinearMap.adjoint A.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.adjoint A.toContinuousLinearMap) =
        ContinuousLinearMap.id 𝕜 H := by
    rw [← ContinuousLinearMap.adjoint_comp]
    congr 1
    ext x
    simp
  simp only [apm_m99j04_conjugate, ContinuousLinearMap.comp_apply,
    map_smul] at h
  change ((ContinuousLinearMap.adjoint A.symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.adjoint A.toContinuousLinearMap)) (T (A w)) =
      eigenvalue • ContinuousLinearMap.adjoint A.symm.toContinuousLinearMap w at h
  rw [hinv] at h
  simpa [apm_m99j04_weight] using h

/-- A continuous linear equivalence satisfying `A†A = 1` carries every
Hilbert basis to an orthonormal family. -/
lemma apm_m99j04_orthonormal_map_of_adjoint_comp
    {𝕜 : Type u𝕜} {H : Type uH} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H ≃L[𝕜] H) {ι : Type (max u𝕜 uH)} (w : HilbertBasis ι 𝕜 H)
    (hunit : (ContinuousLinearMap.adjoint A.toContinuousLinearMap).comp
        A.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 H) :
    Orthonormal 𝕜 (fun i ↦ A (w i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  calc
    inner 𝕜 (A (w i)) (A (w j)) =
        inner 𝕜
          (ContinuousLinearMap.adjoint A.toContinuousLinearMap (A (w i)))
          (w j) := by
            simpa using
              (ContinuousLinearMap.adjoint_inner_left A.toContinuousLinearMap
                (w j) (A (w i))).symm
    _ = inner 𝕜
          (((ContinuousLinearMap.adjoint A.toContinuousLinearMap).comp
            A.toContinuousLinearMap) (w i)) (w j) := rfl
    _ = inner 𝕜 (w i) (w j) := by rw [hunit]; rfl
    _ = if i = j then 1 else 0 := by
      have hw := w.orthonormal
      rw [orthonormal_iff_ite] at hw
      exact hw i j

/-- Conversely, orthonormality of the image of one Hilbert basis forces
`A†A = 1`.  Equality on basis vectors is read off from Hilbert coordinates,
then extended using the convergent Hilbert-basis expansion. -/
lemma apm_m99j04_adjoint_comp_of_orthonormal_map
    {𝕜 : Type u𝕜} {H : Type uH} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H ≃L[𝕜] H) {ι : Type (max u𝕜 uH)} (w : HilbertBasis ι 𝕜 H)
    (horth : Orthonormal 𝕜 (fun i ↦ A (w i))) :
    (ContinuousLinearMap.adjoint A.toContinuousLinearMap).comp
        A.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 H := by
  classical
  let B := (ContinuousLinearMap.adjoint A.toContinuousLinearMap).comp
    A.toContinuousLinearMap
  have hB (i : ι) : B (w i) = w i := by
    apply w.repr.injective
    ext j
    rw [w.repr_apply_apply, w.repr_apply_apply]
    change inner 𝕜 (w j)
      (ContinuousLinearMap.adjoint A.toContinuousLinearMap (A (w i))) = _
    rw [ContinuousLinearMap.adjoint_inner_right]
    rw [orthonormal_iff_ite] at horth
    have hw := w.orthonormal
    rw [orthonormal_iff_ite] at hw
    exact (horth j i).trans (hw j i).symm
  ext x
  have hs := (w.hasSum_repr x).mapL B
  have hid := (w.hasSum_repr x).mapL (ContinuousLinearMap.id 𝕜 H)
  apply HasSum.tsum_eq at hs
  apply HasSum.tsum_eq at hid
  rw [← hs, ← hid]
  congr 1
  funext i
  simp [B, hB]

theorem apm_m99j04
    (𝕜 : Type u𝕜) (H : Type uH) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H)
    (hTcompact : IsCompactOperator T)
    (hTself : ContinuousLinearMap.adjoint T = T)
    (A : H ≃L[𝕜] H) :
    apm_m99j04_HasEigenHilbertBasis T ∧
      IsCompactOperator (apm_m99j04_conjugate A T) ∧
      ContinuousLinearMap.adjoint (apm_m99j04_conjugate A T) =
        apm_m99j04_conjugate A T ∧
      ∃ (ι : Type (max u𝕜 uH)) (w : HilbertBasis ι 𝕜 H)
          (eigenvalue : ι → 𝕜),
        (∀ i, star (eigenvalue i) = eigenvalue i) ∧
        (∀ i,
          T (A (w i)) =
            eigenvalue i • apm_m99j04_weight A (A (w i))) ∧
        (∀ i, inner 𝕜 (apm_m99j04_weight A (A (w i))) (A (w i)) = 1) ∧
        (∀ i j, i ≠ j →
          inner 𝕜 (apm_m99j04_weight A (A (w i))) (A (w j)) = 0) ∧
        (Orthonormal 𝕜 (fun i => A (w i)) ↔
          (ContinuousLinearMap.adjoint A.toContinuousLinearMap).comp
              A.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 H) := by
  obtain ⟨ι, b, e, hb⟩ := apm_m99j04_eigen_hilbert_basis 𝕜 H T hTcompact hTself
  have hc : IsCompactOperator (apm_m99j04_conjugate A T) := by
    simpa [apm_m99j04_conjugate, Function.comp_def] using
      (hTcompact.comp_clm A.toContinuousLinearMap).clm_comp
        (ContinuousLinearMap.adjoint A.toContinuousLinearMap)
  have hs : ContinuousLinearMap.adjoint (apm_m99j04_conjugate A T) =
      apm_m99j04_conjugate A T := by
    rw [apm_m99j04_conjugate, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp, hTself,
      ContinuousLinearMap.adjoint_adjoint]
    exact ContinuousLinearMap.comp_assoc _ _ _
  obtain ⟨κ, w, eigenvalue, hw⟩ :=
    apm_m99j04_eigen_hilbert_basis 𝕜 H (apm_m99j04_conjugate A T) hc hs
  refine ⟨⟨ι, b, e, hb⟩, hc, hs, κ, w, eigenvalue, ?_⟩
  refine ⟨fun i => (hw i).1, ?_, ?_, ?_, ?_⟩
  · intro i
    exact apm_m99j04_generalized_eigenvector A T (w i) (eigenvalue i) (hw i).2
  · intro i
    rw [apm_m99j04_weight_inner]
    rw [inner_self_eq_norm_sq_to_K, w.orthonormal.1 i]
    simp
  · intro i j hij
    rw [apm_m99j04_weight_inner]
    exact w.orthonormal.2 hij
  · constructor
    · exact apm_m99j04_adjoint_comp_of_orthonormal_map A w
    · exact apm_m99j04_orthonormal_map_of_adjoint_comp A w
