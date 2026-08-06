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
  sorry
