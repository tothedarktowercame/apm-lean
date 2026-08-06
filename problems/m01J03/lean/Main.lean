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
  sorry
