import Mathlib

/-!
# APM m01J03 — powers of `T†T` converge to a finite-rank projection

## Statement repairs

None.

## Encoding notes

Convergence is operator-norm convergence, as established by the compact
self-adjoint spectral-gap argument.  The limiting subspace is not left
existentially ambiguous: it is defined as the eigenvalue-one subspace
`ker (T†T - I)`.
-/

noncomputable def apm_m01j03_selfAdjointSquare
    {𝕜 H : Type} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H) : H →L[𝕜] H :=
  (ContinuousLinearMap.adjoint T).comp T

noncomputable def apm_m01j03_topEigenspace
    {𝕜 H : Type} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H) : Submodule 𝕜 H :=
  LinearMap.ker
    ((apm_m01j03_selfAdjointSquare T).toLinearMap - LinearMap.id)

def apm_m01j03_IsOrthogonalProjection
    {𝕜 H : Type} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (P : H →L[𝕜] H) (A : Submodule 𝕜 H) : Prop :=
  P.comp P = P ∧
  ContinuousLinearMap.adjoint P = P ∧
  LinearMap.range P.toLinearMap = A

theorem apm_m01j03
    (𝕜 H : Type) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H) (hT : IsCompactOperator T) (hnorm : ‖T‖ = 1) :
    Module.Finite 𝕜 (apm_m01j03_topEigenspace T) ∧
    ∃ P : H →L[𝕜] H,
      apm_m01j03_IsOrthogonalProjection P
        (apm_m01j03_topEigenspace T) ∧
      Filter.Tendsto
        (fun n : ℕ => (apm_m01j03_selfAdjointSquare T) ^ n)
        Filter.atTop (nhds P) := by
  have hcompact : IsCompactOperator (apm_m01j03_selfAdjointSquare T) := by
    exact hT.clm_comp (ContinuousLinearMap.adjoint T)
  have heigenspace :
      apm_m01j03_topEigenspace T =
        Module.End.eigenspace
          (apm_m01j03_selfAdjointSquare T).toLinearMap (1 : 𝕜) := by
    ext x
    simp [apm_m01j03_topEigenspace, sub_eq_zero]
  have hfinite : Module.Finite 𝕜 (apm_m01j03_topEigenspace T) := by
    rw [heigenspace]
    exact ContinuousLinearMap.finite_dimensional_eigenspace
      hcompact (1 : 𝕜) one_ne_zero
  refine ⟨hfinite, ?_⟩
  letI : Module.Finite 𝕜 (apm_m01j03_topEigenspace T) := hfinite
  letI : (apm_m01j03_topEigenspace T).HasOrthogonalProjection := inferInstance
  refine ⟨(apm_m01j03_topEigenspace T).starProjection, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact (apm_m01j03_topEigenspace T).isIdempotentElem_starProjection
    · exact isSelfAdjoint_starProjection (apm_m01j03_topEigenspace T)
    · exact (apm_m01j03_topEigenspace T).range_starProjection
  · /-
    Boundary for operator-norm convergence: the compiled reduction above proves
    compactness of `T†T`, identifies the frozen kernel with its eigenvalue-one
    eigenspace, proves that eigenspace finite-dimensional using
    `ContinuousLinearMap.finite_dimensional_eigenspace`, and constructs its
    canonical orthogonal projection. The remaining step is the spectral gap:
    show every other spectral value of the positive compact self-adjoint
    operator has norm at most some `r < 1`, then bound
    `‖(T†T)^n - P‖ ≤ r^n`. Mathlib's compact self-adjoint spectral theorem
    supplies `orthogonalComplement_iSup_eigenspaces_eq_bot` and finite
    eigenspaces, but searches found no packaged isolation/gap theorem or
    operator-norm convergence lemma for these powers.
    -/
    sorry
