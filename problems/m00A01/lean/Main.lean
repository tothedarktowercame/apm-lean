import Mathlib

/-!
# APM m00A01

## Statement repairs

The malformed source hypothesis `M \cap N \{0\}` is repaired to
`M \cap N = \{0\}`.  This is the reading required by the claimed injectivity and is
also the reading used by the supplied informal solution.

## Encoding questions

None.  The scalar field is any `RCLike` field, covering the real and complex Hilbert
space cases.  An orthogonal projection is characterized by its value lying in the
target subspace and its residual lying in the orthogonal complement.
-/

noncomputable section

def apmOrthogonalComplement
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (N : Submodule 𝕜 H) : Submodule 𝕜 H :=
  Nᗮ

def apmIsOrthogonalProjectionTo
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (N : Submodule 𝕜 H) (T : H → H) : Prop :=
  ∀ x, T x ∈ N ∧ x - T x ∈ apmOrthogonalComplement N

def apmRestrictedComplement
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (M N : Submodule 𝕜 H) (P : H →L[𝕜] N)
    (hP : ∀ x, x - (P x : H) ∈ apmOrthogonalComplement N) :
    M → apmOrthogonalComplement N :=
  fun x => ⟨(x : H) - (P x : H), hP x⟩

/-- The continuous-linear packaging of `apmRestrictedComplement`. -/
def apmRestrictedComplementCLM
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (M N : Submodule 𝕜 H) (P : H →L[𝕜] N)
    (hP : ∀ x, x - (P x : H) ∈ apmOrthogonalComplement N) :
    M →L[𝕜] Nᗮ :=
  (M.subtypeL - N.subtypeL.comp (P.comp M.subtypeL)).codRestrict
    (apmOrthogonalComplement N) (fun x => hP x)

@[simp] lemma apmRestrictedComplementCLM_apply
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (M N : Submodule 𝕜 H) (P : H →L[𝕜] N)
    (hP : ∀ x, x - (P x : H) ∈ apmOrthogonalComplement N) (x : M) :
    apmRestrictedComplementCLM M N P hP x = apmRestrictedComplement M N P hP x := rfl

theorem apm_m00a01
    (𝕜 H : Type*) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (M N : Submodule 𝕜 H)
    (hMclosed : IsClosed (M : Set H)) (hNclosed : IsClosed (N : Set H))
    (hdisjoint : M ⊓ N = ⊥) (hsum : M ⊔ N = ⊤)
    (P : H →L[𝕜] N)
    (hP : ∀ x, x - (P x : H) ∈ apmOrthogonalComplement N) :
    apmIsOrthogonalProjectionTo N (fun x => (P x : H)) ∧
      apmIsOrthogonalProjectionTo (apmOrthogonalComplement N)
        (fun x => x - (P x : H)) ∧
      Function.Bijective (apmRestrictedComplement M N P hP) ∧
      ∃ α : ℝ, 0 < α ∧
        ∀ x : M, α * ‖(x : H)‖ ≤ ‖(x : H) - (P x : H)‖ := by
  have hzero_of_mem_both {x : H} (hxM : x ∈ M) (hxN : x ∈ N) : x = 0 := by
    have hx : x ∈ M ⊓ N := ⟨hxM, hxN⟩
    rw [hdisjoint] at hx
    simpa using hx
  have hzero_of_mem_N_perp {x : H} (hxN : x ∈ N)
      (hxperp : x ∈ apmOrthogonalComplement N) : x = 0 := by
    have hx : x ∈ N ⊓ apmOrthogonalComplement N := ⟨hxN, hxperp⟩
    rw [apmOrthogonalComplement, Submodule.inf_orthogonal_eq_bot] at hx
    simpa using hx
  have hP_eq_of_mem {x : H} (hx : x ∈ N) : (P x : H) = x := by
    have hdiffN : x - (P x : H) ∈ N := N.sub_mem hx (P x).property
    have hz := hzero_of_mem_N_perp hdiffN (hP x)
    exact (sub_eq_zero.mp hz).symm
  have hP_eq_zero_of_mem_perp {x : H} (hx : x ∈ apmOrthogonalComplement N) :
      (P x : H) = 0 := by
    have hPxperp : (P x : H) ∈ apmOrthogonalComplement N := by
      have := (apmOrthogonalComplement N).sub_mem hx (hP x)
      simpa [apmOrthogonalComplement] using this
    exact hzero_of_mem_N_perp (P x).property hPxperp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨(P x).property, hP x⟩
  · intro x
    constructor
    · exact hP x
    · have hPx : (P x : H) ∈
          apmOrthogonalComplement (apmOrthogonalComplement N) := by
        exact Submodule.le_orthogonal_orthogonal N (P x).property
      simpa [apmOrthogonalComplement] using hPx
  · constructor
    · intro x y hxy
      apply Subtype.ext
      have hval := congrArg Subtype.val hxy
      change (x : H) - (P x : H) = (y : H) - (P y : H) at hval
      have hdiffN : (x : H) - (y : H) ∈ N := by
        have heq : (x : H) - (y : H) = (P x : H) - (P y : H) := by
          rw [sub_eq_sub_iff_add_eq_add] at hval ⊢
          simpa [add_comm] using hval
        rw [heq]
        exact N.sub_mem (P x).property (P y).property
      have hdiffM : (x : H) - (y : H) ∈ M := M.sub_mem x.property y.property
      exact sub_eq_zero.mp (hzero_of_mem_both hdiffM hdiffN)
    · intro z
      have hzsum : (z : H) ∈ M ⊔ N := by
        rw [hsum]
        exact Submodule.mem_top
      obtain ⟨m, hm, n, hn, hmn⟩ := Submodule.mem_sup.mp hzsum
      refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
      change m - (P m : H) = (z : H)
      have hPz : (P (z : H) : H) = 0 := hP_eq_zero_of_mem_perp z.property
      have hPn : (P n : H) = n := hP_eq_of_mem hn
      have happ' : P m + P n = P (z : H) := by
        simpa using congrArg P hmn
      have happ := congrArg Subtype.val happ'
      change (P m : H) + (P n : H) = (P (z : H) : H) at happ
      rw [hPz, hPn] at happ
      rw [← hmn]
      rw [show (P m : H) = -n by
        rw [eq_neg_iff_add_eq_zero]
        exact happ]
      abel
  · /-
    Boundary after closer hop 1: both projection characterizations and the bijectivity of
    `apmRestrictedComplement M N P hP` are proved above.  The remaining bridge
    is the quantitative lower bound from the bounded inverse theorem.

    New progress: `apmRestrictedComplementCLM` now packages the subtype-valued
    expression as a `ContinuousLinearMap M (Nᵆ)`, and
    `apmRestrictedComplementCLM_apply` identifies it definitionally with the
    frozen function. The remaining route is to use the established bijectivity with
    `ContinuousLinearEquiv.ofBijective`, and extract an antilipschitz/norm lower
    bound from the resulting equivalence. Source inspection additionally found
    `antilipschitzWith_iff_exists_mul_le_norm`, which returns exactly a positive
    real constant and the desired multiplicative norm inequality, avoiding
    inverse-norm positivity edge cases. Searches covered
    `ContinuousLinearEquiv.ofBijective`,
    `ContinuousLinearMap.bijective_iff_dense_range_and_antilipschitz`, and
    `ContinuousLinearEquiv.antilipschitz`. The remaining elaboration blocker is
    installing/aligning the `CompleteSpace` instance for the orthogonal-complement
    subtype while building `ContinuousLinearEquiv.ofBijective`, then feeding its
    antilipschitz result through the positive-constant equivalence. The ambient
    and subtype norms reduce definitionally once that equivalence is constructed.
    -/
    sorry
