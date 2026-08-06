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
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · exact M.isIdempotentElem_starProjection
    · exact isSelfAdjoint_starProjection M
    · exact M.range_starProjection
  · constructor
    · /-
      Boundary for the sum criterion: Mathlib provides
      `IsOrtho.starProjection_comp_starProjection` and
      `starProjection_comp_starProjection_eq_zero_iff`, which settle the
      orthogonal-to-sum direction after identifying the projection on `M ⊔ N`.
      The reverse direction requires extracting vanishing cross terms from the
      idempotence of the asserted sum and then using positivity of an
      orthogonal projection to show each cross term is zero. No packaged lemma
      for the full equality with `(M ⊔ N).starProjection` was found.
      -/
      sorry
    · constructor
      · /-
        Boundary for the product criterion: algebraically, adjoint reversal
        via `ContinuousLinearMap.adjoint_comp` and self-adjointness of each
        `starProjection` turn self-adjointness of the product into commutation;
        conversely commutation gives both idempotence and self-adjointness.
        The attempted direct rewrite exposed a representation mismatch between
        `star` and `ContinuousLinearMap.adjoint`, and the nested `.comp`
        associativity normalization remains to be packaged into helper lemmas.
        -/
        sorry
      · intro hcomm
        refine ⟨?_, ?_, ?_⟩
        · /- Same composition-normalization boundary as above. -/
          sorry
        · /- Same adjoint-representation boundary as above. -/
          sorry
        · ext x
          constructor
          · rintro ⟨y, rfl⟩
            constructor
            · exact M.starProjection_apply_mem _
            · rw [hcomm]
              exact N.starProjection_apply_mem _
          · intro hx
            refine ⟨x, ?_⟩
            change M.starProjection (N.starProjection x) = x
            rw [N.starProjection_eq_self_iff.mpr hx.2,
              M.starProjection_eq_self_iff.mpr hx.1]
