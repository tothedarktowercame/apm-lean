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

/-- Once the spectral-gap estimate is available, the operator-norm convergence
is purely a normed-ring argument.  This isolates the analytic boundary from
the compact spectral theorem. -/
private lemma apm_m01j03_tendsto_powers_of_gap
    {A : Type*} [NormedRing A] (a p : A)
    (hp : p * p = p) (hap : a * p = p) (hpa : p * a = p)
    (hgap : ‖a - p‖ < 1) :
    Filter.Tendsto (fun n : ℕ => a ^ n) Filter.atTop (nhds p) := by
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  have hpow : Filter.Tendsto (fun n : ℕ => (a - p) ^ (n + 1))
      Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hgap).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hpa_pow : ∀ n : ℕ, p * a ^ (n + 1) = p := by
    intro n
    induction n with
    | zero => simpa using hpa
    | succ n ih =>
        rw [pow_succ, ← mul_assoc p (a ^ (n + 1)) a, ih, hpa]
  have hid : ∀ n : ℕ, a ^ (n + 1) - p = (a - p) ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ' a (n + 1), pow_succ' (a - p) (n + 1), ← ih]
        rw [sub_mul, mul_sub a, hap, mul_sub p, hpa_pow n, hp]
        simp
  have := hpow.add_const p
  convert this using 1
  · funext n
    exact sub_eq_iff_eq_add.mp (hid n)
  · simp

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
  have hself : ContinuousLinearMap.adjoint
      (apm_m01j03_selfAdjointSquare T) = apm_m01j03_selfAdjointSquare T := by
    simp [apm_m01j03_selfAdjointSquare, ContinuousLinearMap.adjoint_comp]
  have hpositive : (apm_m01j03_selfAdjointSquare T).IsPositive := by
    exact T.isPositive_adjoint_comp_self
  have hnormSquare : ‖apm_m01j03_selfAdjointSquare T‖ = 1 := by
    rw [apm_m01j03_selfAdjointSquare,
      ContinuousLinearMap.norm_adjoint_comp_self, hnorm]
    norm_num
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
  · let S := apm_m01j03_selfAdjointSquare T
    let P := (apm_m01j03_topEigenspace T).starProjection
    have hSP : S.comp P = P := by
      ext x
      have hx : P x ∈ apm_m01j03_topEigenspace T :=
        Submodule.starProjection_apply_mem (apm_m01j03_topEigenspace T) x
      rw [apm_m01j03_topEigenspace, LinearMap.mem_ker] at hx
      exact sub_eq_zero.mp (by simpa [S, P, ContinuousLinearMap.comp_apply] using hx)
    have hPS : P.comp S = P := by
      have hadj := congrArg ContinuousLinearMap.adjoint hSP
      rw [ContinuousLinearMap.adjoint_comp] at hadj
      dsimp [S, P] at hadj ⊢
      have hPself : ContinuousLinearMap.adjoint
          (apm_m01j03_topEigenspace T).starProjection =
          (apm_m01j03_topEigenspace T).starProjection :=
        isSelfAdjoint_starProjection (apm_m01j03_topEigenspace T)
      rw [hself, hPself] at hadj
      exact hadj
    have hPP : P.comp P = P :=
      (apm_m01j03_topEigenspace T).isIdempotentElem_starProjection
    have hgap : ‖S - P‖ < 1 := by
      have hfactor : S - P = S.comp (1 - P) := by
        ext x
        simp [ContinuousLinearMap.comp_apply, sub_eq_add_neg, hSP]
      have hle : ‖S - P‖ ≤ 1 := by
        rw [hfactor]
        calc
          ‖S.comp (1 - P)‖ ≤ ‖S‖ * ‖1 - P‖ :=
            ContinuousLinearMap.opNorm_comp_le S (1 - P)
          _ ≤ 1 * 1 := mul_le_mul
            (by simpa [S] using le_of_eq hnormSquare)
            (by
              rw [← Submodule.starProjection_orthogonal'
                (apm_m01j03_topEigenspace T)]
              exact Submodule.starProjection_norm_le _)
            (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      apply lt_of_le_of_ne hle
      intro heq
      /-
      Boundary (closer hop 2): all algebra after the compact spectral theorem
      is now compiled.  The local lemma `apm_m01j03_tendsto_powers_of_gap`
      proves in any normed ring that an idempotent `P`, fixed on both sides by
      `S`, and `‖S - P‖ < 1` imply `S ^ n → P`.  The identities `S P = P`
      and `P S = P` are proved immediately above (the second by adjoints).

      Thus the sole missing fact is exactly `‖S - P‖ < 1`.  Further source
      searches covered `FredholmAlternative.hasEigenvalue_iff_mem_spectrum`,
      compact/self-adjoint `orthogonalComplement_iSup_eigenspaces_eq_bot`,
      finite nonzero eigenspaces, CFC spectrum/isometry APIs, and the compact
      operator spectral-radius API.  Mathlib proves that nonzero spectral
      points are eigenvalues, but exposes no theorem that nonzero spectral
      points of a compact operator are isolated (or that only finitely many
      lie outside each neighborhood of zero).  Without that missing compact-
      spectrum discreteness theorem, the strict gap below cannot be derived
      merely from finite-dimensionality of the eigenspace at `1`.

      `LEMMA-INDEX.md`, all closed artifacts (185 at this checkout), sibling
      `m99J04`, `ConstructionTargets/`, `YoungL2.lean`, and git history contain
      no such isolation lemma or operator-power convergence result.

      Closer hop 3 found a route around the full discreteness theorem.
      `CStarAlgebra.norm_or_neg_norm_mem_spectrum` puts one of `‖S-P‖` and
      `-‖S-P‖` in the real spectrum of the self-adjoint operator `S-P`.
      Under the contradictory assumption `‖S-P‖ = 1`, real-to-`𝕜` spectrum
      transport followed by compact Fredholm alternative should therefore
      produce a nonzero eigenvector with eigenvalue `1` or `-1`.  The
      identities `SP=P`, `PS=P`, and `P²=P` put every such nonzero-eigenvalue
      vector in `ker P`; positivity and `‖S‖=1` then exclude `-1`, while the
      `+1` case lies in the top eigenspace and hence is fixed by `P`, a
      contradiction.  A further source check found that
      `spectrum.algebraMap_mem 𝕜` performs the required real-to-`𝕜` spectrum
      transport directly; `ContinuousLinearMap.spectralRadius_eq_nnnorm`
      independently uses the same `RCLike` mechanism.  Thus the remaining
      boundary is only the `±1` eigenvector contradiction (including the
      positivity exclusion), not spectrum isolation, and does not require
      annular spectral finiteness.
      -/
      have hPself : ContinuousLinearMap.adjoint P = P := by
        exact isSelfAdjoint_starProjection (apm_m01j03_topEigenspace T)
      have hAself : IsSelfAdjoint (S - P) := by
        have hSs : IsSelfAdjoint S := by simpa [S] using hself
        have hPs : IsSelfAdjoint P := by simpa [P] using hPself
        exact hSs.sub hPs
      have hAcompact : IsCompactOperator (S - P) := by
        rw [hfactor]
        exact hcompact.comp_clm (1 - P)
      have hTne : T ≠ 0 := by
        intro h
        rw [h, norm_zero] at hnorm
        norm_num at hnorm
      obtain ⟨x0, hx0⟩ : ∃ x, T x ≠ 0 := by
        by_contra! h
        apply hTne
        ext x
        exact h x
      letI : Nontrivial H := ⟨⟨x0, 0, fun hx => hx0 (by simp [hx])⟩⟩
      have hspectrum : algebraMap ℝ 𝕜 ‖S - P‖ ∈ spectrum 𝕜 (S - P) ∨
          algebraMap ℝ 𝕜 (-‖S - P‖) ∈ spectrum 𝕜 (S - P) := by
        simp_rw [spectrum, Set.mem_compl_iff, map_neg]
        by_contra! h
        obtain ⟨c, hc0, hc⟩ :=
          (S - P).abs_rayleighQuotient_le_of_norm_mem_resolventSet h.1 h.2
        grind [ciSup_le hc,
          ContinuousLinearMap.norm_eq_iSup_rayleighQuotient (S - P) hAself.isSymmetric]
      rw [heq] at hspectrum
      rcases hspectrum with hspec | hspec
      · have hspecK : algebraMap ℝ 𝕜 (1 : ℝ) ∈ spectrum 𝕜 (S - P) := by
          simpa using hspec
        have hev : Module.End.HasEigenvalue (S - P).toLinearMap (1 : 𝕜) :=
          (hAcompact.hasEigenvalue_iff_mem_spectrum one_ne_zero).mpr (by simpa using hspecK)
        obtain ⟨x, hx⟩ := hev.exists_hasEigenvector
        have hxA : (S - P) x = x := by
          simpa using hx.apply_eq_smul
        have hxP : P x = 0 := by
          have := congrArg P hxA
          simp only [ContinuousLinearMap.sub_apply] at this
          rw [map_sub, ← ContinuousLinearMap.comp_apply, hPS,
            ← ContinuousLinearMap.comp_apply,
            hPP] at this
          simpa using this.symm
        have hxS : S x = x := by simpa [ContinuousLinearMap.sub_apply, hxP] using hxA
        have hxtop : x ∈ apm_m01j03_topEigenspace T := by
          rw [apm_m01j03_topEigenspace, LinearMap.mem_ker]
          exact sub_eq_zero.mpr (by simpa [S] using hxS)
        have hxP' : P x = x := by
          exact (apm_m01j03_topEigenspace T).starProjection_eq_self_iff.mpr hxtop
        exact hx.2 (by simpa [hxP] using hxP'.symm)
      · have hspecK : algebraMap ℝ 𝕜 (-1 : ℝ) ∈ spectrum 𝕜 (S - P) := by
          simpa using hspec
        have hneg : (-1 : 𝕜) ≠ 0 := by norm_num
        have hev : Module.End.HasEigenvalue (S - P).toLinearMap (-1 : 𝕜) :=
          (hAcompact.hasEigenvalue_iff_mem_spectrum hneg).mpr (by simpa using hspecK)
        obtain ⟨x, hx⟩ := hev.exists_hasEigenvector
        have hxA : (S - P) x = -x := by
          simpa using hx.apply_eq_smul
        have hxP : P x = 0 := by
          have := congrArg P hxA
          simp only [ContinuousLinearMap.sub_apply, map_neg] at this
          rw [map_sub, ← ContinuousLinearMap.comp_apply, hPS,
            ← ContinuousLinearMap.comp_apply,
            hPP] at this
          simpa using this
        have hxS : S x = -x := by simpa [ContinuousLinearMap.sub_apply, hxP] using hxA
        have hpos := hpositive.re_inner_nonneg_left x
        rw [show apm_m01j03_selfAdjointSquare T = S by rfl] at hpos
        rw [hxS] at hpos
        have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx.2
        have hneg : 0 ≤ -(‖x‖ ^ 2) := by simpa using hpos
        nlinarith [sq_pos_of_pos hxnorm]
    exact apm_m01j03_tendsto_powers_of_gap S P
      (apm_m01j03_topEigenspace T).isIdempotentElem_starProjection hSP hPS hgap
