import Mathlib

/-!
# APM m99J04

## Statement repairs

None.

## Encoding questions

“Basis” means a Hilbert basis, not an algebraic Hamel basis. The generalized
eigenvectors are encoded as the image of a Hilbert basis under the given continuous
linear equivalence; this is precisely a topological (Riesz) basis and does not falsely
claim that its vectors are orthonormal in the original inner product.
-/

noncomputable section

def apm_m99j04_conjugate
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H ≃L[𝕜] H) (T : H →L[𝕜] H) : H →L[𝕜] H :=
  (ContinuousLinearMap.adjoint A.toContinuousLinearMap).comp
    (T.comp A.toContinuousLinearMap)

def apm_m99j04_weight
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H ≃L[𝕜] H) : H →L[𝕜] H :=
  (ContinuousLinearMap.adjoint A.symm.toContinuousLinearMap).comp
    A.symm.toContinuousLinearMap

def apm_m99j04_HasEigenHilbertBasis
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H) : Prop :=
  ∃ (ι : Type) (b : HilbertBasis ι 𝕜 H) (eigenvalue : ι → 𝕜),
    ∀ i, star (eigenvalue i) = eigenvalue i ∧
      T (b i) = eigenvalue i • b i

lemma apm_m99j04_weight_inner
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H ≃L[𝕜] H) (x y : H) :
    inner 𝕜 (apm_m99j04_weight A (A x)) (A y) = inner 𝕜 x y := by
  simp [apm_m99j04_weight, ContinuousLinearMap.adjoint_inner_left]

/-- An eigenvector of the congruence transports to a generalized eigenvector
for the original operator and the induced weight. -/
lemma apm_m99j04_generalized_eigenvector
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
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
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H ≃L[𝕜] H) {ι : Type} (w : HilbertBasis ι 𝕜 H)
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
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : H ≃L[𝕜] H) {ι : Type} (w : HilbertBasis ι 𝕜 H)
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
    (𝕜 H : Type*) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H)
    (hTcompact : IsCompactOperator T)
    (hTself : ContinuousLinearMap.adjoint T = T)
    (A : H ≃L[𝕜] H) :
    apm_m99j04_HasEigenHilbertBasis T ∧
      IsCompactOperator (apm_m99j04_conjugate A T) ∧
      ContinuousLinearMap.adjoint (apm_m99j04_conjugate A T) =
        apm_m99j04_conjugate A T ∧
      ∃ (ι : Type) (w : HilbertBasis ι 𝕜 H) (eigenvalue : ι → 𝕜),
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
  have hconjugate_compact : IsCompactOperator (apm_m99j04_conjugate A T) := by
    simpa [apm_m99j04_conjugate, Function.comp_def] using
      (hTcompact.comp_clm A.toContinuousLinearMap).clm_comp
        (ContinuousLinearMap.adjoint A.toContinuousLinearMap)
  have hconjugate_self :
      ContinuousLinearMap.adjoint (apm_m99j04_conjugate A T) =
        apm_m99j04_conjugate A T := by
    rw [apm_m99j04_conjugate, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp, hTself,
      ContinuousLinearMap.adjoint_adjoint]
    exact ContinuousLinearMap.comp_assoc _ _ _
  /-
  Boundary (closer hop 2): compactness and self-adjointness of the congruence `A† T A` are
  proved above. Completing the frozen theorem requires turning Mathlib's
  compact spectral theorem
  `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` into a
  single `HilbertBasis` indexed across all eigenspaces, then transporting that
  basis through `A`; the weighted inner-product transport identity needed for
  its normalization and orthogonality is proved above. Closer hop 1 also proves
  `apm_m99j04_generalized_eigenvector`, which transports each ordinary
  eigenvector equation for `A† T A` to the frozen generalized equation for
  `T` and the weight. This hop proves
  `apm_m99j04_orthonormal_map_of_adjoint_comp`: for every Hilbert basis `w`,
  `A†A = id` implies that `i ↦ A (w i)` is orthonormal. It uses the adjoint
  inner-product identity and `HilbertBasis.orthonormal`, closing the reverse
  direction of the frozen final equivalence. I searched
  the `OrthogonalFamily`, eigenspace direct-sum, `HilbertBasis`, adjoint of
  continuous-linear equivalences, and isometry/unitarity APIs, but did not
  find the required infinite-dimensional eigenbasis constructor or the
  converse dense-basis isometry bridge in this pass.

  Closer hop 3 proves that converse locally as
  `apm_m99j04_adjoint_comp_of_orthonormal_map`.  Hilbert-basis coordinates and
  `ContinuousLinearMap.adjoint_inner_right` show that `A†A` fixes every basis
  vector; mapping `HilbertBasis.hasSum_repr` through the two continuous linear
  maps extends the equality to every vector.  Hence the frozen final
  equivalence is completely closed by the two local lemmas.  Searches of the
  compact spectral theorem source, `OrthogonalFamily`/`IsHilbertSum`, closed
  artifacts, construction libraries, and git history still found no packaged
  constructor assembling bases of all nonzero eigenspaces together with the
  kernel into a single labeled `HilbertBasis`.  That spectral eigenbasis
  construction is the sole remaining boundary.
  -/
  sorry
