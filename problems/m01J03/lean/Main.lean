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
    have hgap : ‖S - P‖ < 1 := by
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
      -/
      sorry
    exact apm_m01j03_tendsto_powers_of_gap S P
      (apm_m01j03_topEigenspace T).isIdempotentElem_starProjection hSP hPS hgap
