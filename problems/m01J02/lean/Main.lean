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

      Closer hop 1 additionally searched `IsStarProjection.add`,
      `isStarProjection_iff_eq_starProjection_range`, and the idempotent-ring
      API.  `IsStarProjection.add` proves only the forward construction from a
      zero product.  Expanding idempotence yields `P_M P_N + P_N P_M = 0`, but
      the library has no converse lemma extracting `P_M P_N = 0`; formalizing
      that extraction still requires the inner-product positivity calculation
      from the informal proof.  The other three former holes are now closed
      below using `ContinuousLinearMap.adjoint_comp` and pointwise composition
      algebra.
      -/
      sorry
    · constructor
      · -- Mathlib: `ContinuousLinearMap.adjoint_comp` and self-adjoint projections.
        constructor
        · rintro ⟨A, _, hself, _⟩
          have hM : ContinuousLinearMap.adjoint M.starProjection = M.starProjection :=
            isSelfAdjoint_starProjection M
          have hN : ContinuousLinearMap.adjoint N.starProjection = N.starProjection :=
            isSelfAdjoint_starProjection N
          rw [ContinuousLinearMap.adjoint_comp, hN, hM] at hself
          exact hself.symm
        · intro hcomm
          refine ⟨M ⊓ N, ?_, ?_, ?_⟩
          · ext x
            simp only [ContinuousLinearMap.comp_apply]
            have hc : M.starProjection (N.starProjection (N.starProjection x)) =
                N.starProjection (M.starProjection (N.starProjection x)) := by
              exact DFunLike.congr_fun hcomm (N.starProjection x)
            rw [← hc]
            rw [M.starProjection_eq_self_iff.mpr (M.starProjection_apply_mem _)]
            rw [N.starProjection_eq_self_iff.mpr (N.starProjection_apply_mem _)]
          · have hM : ContinuousLinearMap.adjoint M.starProjection = M.starProjection :=
              isSelfAdjoint_starProjection M
            have hN : ContinuousLinearMap.adjoint N.starProjection = N.starProjection :=
              isSelfAdjoint_starProjection N
            rw [ContinuousLinearMap.adjoint_comp, hN, hM]
            exact hcomm.symm
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
      · intro hcomm
        refine ⟨?_, ?_, ?_⟩
        ·
          ext x
          simp only [ContinuousLinearMap.comp_apply]
          have hc : M.starProjection (N.starProjection (N.starProjection x)) =
              N.starProjection (M.starProjection (N.starProjection x)) := by
            exact DFunLike.congr_fun hcomm (N.starProjection x)
          rw [← hc]
          rw [M.starProjection_eq_self_iff.mpr (M.starProjection_apply_mem _)]
          rw [N.starProjection_eq_self_iff.mpr (N.starProjection_apply_mem _)]
        ·
          have hM : ContinuousLinearMap.adjoint M.starProjection = M.starProjection :=
            isSelfAdjoint_starProjection M
          have hN : ContinuousLinearMap.adjoint N.starProjection = N.starProjection :=
            isSelfAdjoint_starProjection N
          rw [ContinuousLinearMap.adjoint_comp, hN, hM]
          exact hcomm.symm
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
