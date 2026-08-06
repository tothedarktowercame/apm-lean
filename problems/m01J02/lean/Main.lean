import Mathlib

/-!
# APM m01J02 — sums and products of orthogonal projections

## Statement repairs

* The source writes `P ∩ N` in part (c); this is corrected to `M ∩ N`, as
  required by the two projections named in the problem.
* The notation `P_{M+N}` presupposes that `M+N` admits an orthogonal projection.
  This existence is made explicit by the `HasOrthogonalProjection` instance for
  `M ⊔ N`.

## Encoding notes

Closed orthogonally complemented subspaces use Mathlib's
`Submodule.HasOrthogonalProjection`, and `Submodule.starProjection` is the
projection regarded as an operator `H →L[𝕜] H`.
-/

def apm_m01j02_IsOrthogonalProjection
    {𝕜 H : Type} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (P : H →L[𝕜] H) (M : Submodule 𝕜 H) : Prop :=
  P.comp P = P ∧
  ContinuousLinearMap.adjoint P = P ∧
  LinearMap.range P.toLinearMap = M

theorem apm_m01j02
    (𝕜 H : Type) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M N : Submodule 𝕜 H)
    [M.HasOrthogonalProjection] [N.HasOrthogonalProjection]
    [(M ⊔ N).HasOrthogonalProjection] :
    apm_m01j02_IsOrthogonalProjection M.starProjection M ∧
    (M.starProjection + N.starProjection = (M ⊔ N).starProjection ↔ M ⟂ N) ∧
    ((∃ A : Submodule 𝕜 H,
      apm_m01j02_IsOrthogonalProjection
        (M.starProjection.comp N.starProjection) A) ↔
      M.starProjection.comp N.starProjection =
        N.starProjection.comp M.starProjection) ∧
    (M.starProjection.comp N.starProjection =
        N.starProjection.comp M.starProjection →
      apm_m01j02_IsOrthogonalProjection
        (M.starProjection.comp N.starProjection) (M ⊓ N)) := by
  sorry
