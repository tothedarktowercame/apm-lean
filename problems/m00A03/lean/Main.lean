import Mathlib

/-!
# APM m00A03: Riesz's lemma and compact-operator spectra

## Statement repairs

None.

## Encoding questions

The scalar field of the Banach space is not printed. Because part (b) discusses
the complex spectrum using `z` and `|z|`, we use the standard complex Banach
space formulation. No central object is omitted: the conclusion concerns
Mathlib's algebraic spectrum of the continuous linear operator itself.
-/

open Set Metric

noncomputable section

theorem apm_m00a03
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] :
    (∀ (Y Z : Submodule ℂ X),
      Y ≤ Z → Y ≠ Z → IsClosed (Y : Set X) →
        ∃ z ∈ Z, ‖z‖ = 1 ∧ (1 / 2 : ℝ) ≤ infDist z (Y : Set X)) ∧
    ∀ A : X →L[ℂ] X, IsCompactOperator A →
      (∀ ε : ℝ, 0 < ε →
        {z ∈ spectrum ℂ A | ε < ‖z‖}.Finite) ∧
      derivedSet (spectrum ℂ A) ⊆ {0} := by
  constructor
  · intro Y Z hYZ hne hYclosed
    have hnle : ¬ Z ≤ Y := by
      intro hZY
      exact hne (le_antisymm hYZ hZY)
    obtain ⟨w, hwZ, hwY⟩ := SetLike.not_le_iff_exists.mp hnle
    let F : Submodule ℂ Z := Y.comap Z.subtype
    have hFclosed : IsClosed (F : Set Z) := by
      exact hYclosed.preimage continuous_subtype_val
    have hFproper : ∃ x : Z, x ∉ F := ⟨⟨w, hwZ⟩, hwY⟩
    obtain ⟨z, _, hznorm, hzfar⟩ :=
      riesz_lemma_of_lt_one hFclosed hFproper (r := (1 / 2 : ℝ)) (by norm_num)
    refine ⟨(z : X), z.property, hznorm, ?_⟩
    rw [Metric.le_infDist ⟨0, Y.zero_mem⟩]
    intro y hy
    have hyZ : y ∈ Z := hYZ hy
    have hyF : (⟨y, hyZ⟩ : Z) ∈ F := hy
    have := hzfar ⟨y, hyZ⟩ hyF
    simpa [dist_eq_norm] using this
  · intro A hA
    /-
    Boundary: Riesz's lemma is closed above using Mathlib's compiled
    `riesz_lemma_of_lt_one`, applied to the comap of `Y` inside the subtype
    `Z`, and converted to the requested `Metric.infDist` statement via
    `Metric.le_infDist`.

    For the compact-spectrum half, Mathlib's current
    `Analysis/Normed/Operator/FredholmAlternative.lean` provides
    `IsCompactOperator.hasEigenvalue_iff_mem_spectrum`, establishing that every
    nonzero spectral value is an eigenvalue. It does not package the stronger
    finiteness-away-from-zero or `derivedSet` conclusions. Searches for
    `IsCompactOperator.*spectrum.*Finite`, `derivedSet.*spectrum`, and related
    declarations returned no bridge. Completing this conjunct therefore still
    requires the long flag-of-eigenspaces/Riesz-separation argument from the
    informal proof, including extraction of infinitely many distinct spectral
    points and compactness contradiction. No solved sibling contains that
    complete formal chain.
    -/
    sorry
