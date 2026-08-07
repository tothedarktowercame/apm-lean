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

open Set Metric Filter

noncomputable section

/-- Finiteness above every strict positive cutoff also gives finiteness on the
closed annulus used in the usual Riesz--Schauder contradiction. -/
lemma apm_m00A03_finite_norm_ge_of_finite_norm_gt
    (s : Set ℂ)
    (h : ∀ ε : ℝ, 0 < ε → {z ∈ s | ε < ‖z‖}.Finite)
    (ε : ℝ) (hε : 0 < ε) : {z ∈ s | ε ≤ ‖z‖}.Finite := by
  apply (h (ε / 2) (by positivity)).subset
  intro z hz
  exact ⟨hz.1, (half_lt_self hε).trans_le hz.2⟩

lemma apm_m00A03_derivedSet_subset_zero_of_annular_finite
    (s : Set ℂ) (h : ∀ ε : ℝ, 0 < ε → {z ∈ s | ε ≤ ‖z‖}.Finite) :
    derivedSet s ⊆ {0} := by
  intro x hx
  simp only [Set.mem_singleton_iff]
  by_contra hx0
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let T : Set ℂ := {z ∈ s | ‖x‖ / 2 ≤ ‖z‖}
  have hT : T.Finite := h (‖x‖ / 2) (by positivity)
  have hTdiff : (T \ {x}).Finite := hT.diff
  have hopen : IsOpen ((T \ {x})ᶜ) := hTdiff.isClosed.isOpen_compl
  have hnhds : ball x (‖x‖ / 2) ∩ (T \ {x})ᶜ ∈ nhds x :=
    inter_mem (ball_mem_nhds x (by positivity)) (hopen.mem_nhds (by simp))
  obtain ⟨y, hy, hyne⟩ := (accPt_iff_nhds.mp hx)
    (ball x (‖x‖ / 2) ∩ (T \ {x})ᶜ) hnhds
  have hydist : dist y x < ‖x‖ / 2 := by
    simpa [dist_comm] using hy.1.1
  have hynorm : ‖x‖ / 2 ≤ ‖y‖ := by
    have htri := norm_sub_norm_le x y
    rw [← dist_eq_norm] at htri
    have hydist' : dist x y < ‖x‖ / 2 := by simpa [dist_comm] using hydist
    nlinarith
  have hyT : y ∈ T := ⟨hy.2, hynorm⟩
  exact hy.1.2 ⟨hyT, by simpa [hyne]⟩

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
    have hfinite : ∀ ε : ℝ, 0 < ε →
        {z ∈ spectrum ℂ A | ε < ‖z‖}.Finite := by
    /-
    Boundary after closer hop 1: Riesz's lemma is closed above using Mathlib's compiled
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

    New progress: `apm_m00A03_finite_norm_ge_of_finite_norm_gt` closes the
    strict-vs-closed cutoff mismatch: the statement's finiteness for
    `ε < ‖z‖`, applied at `ε / 2`, yields finiteness of the standard annulus
    `ε ≤ ‖z‖`. Searches also inspected `Topology/DerivedSet.lean` and found
    `accPt_iff_nhds`; once annular finiteness is proved, the derived-set clause
    can be discharged topologically by choosing a positive-norm neighborhood
    and excluding the finitely many remaining points. Thus the genuinely open
    analytic bridge is the first finiteness clause itself.

    Closer hop 2 inspected the complete proof of
    `IsCompactOperator.hasEigenvalue_or_mem_resolventSet`.  Its final section
    already supplies the exact compact-image/subsequence contradiction APIs:
    `IsCompactOperator.image_closedBall_subset_compact`,
    `IsCompact.tendsto_subseq`, `Metric.cauchySeq_iff'`, and a pairwise norm
    separation argument.  That proof is parameterized by one fixed `μ`, however,
    so it cannot directly establish annular finiteness.  The missing new
    construction is now isolated to: select a sequence of distinct points from
    an infinite annular subset of the spectrum; turn them into eigenvectors via
    `hA.hasEigenvalue_iff_mem_spectrum`; prove their finite spans form a strict,
    closed, invariant flag with the shift property; and apply Riesz's lemma to
    obtain the separated bounded sequence consumed by those compactness APIs.
    Sibling `m96A01` proves only finite dimensionality of each individual
    nonzero eigenspace, which does not construct this flag.  No closed artifact,
    lemma-index entry, or construction library supplies the missing assembly.

    Closer hop 3 proves the full topological consequence as
    `apm_m00A03_derivedSet_subset_zero_of_annular_finite`: a ball of radius
    `‖x‖ / 2`, intersected with the complement of the finite closed annulus
    (apart from `x`), contradicts `accPt_iff_nhds` at every `x ≠ 0`.
    Consequently this final `sorry` is confined exactly to annular spectral
    finiteness, i.e. the multi-eigenvalue invariant-flag/Riesz-separation
    construction described above.
    -/
      sorry
    refine ⟨hfinite, ?_⟩
    exact apm_m00A03_derivedSet_subset_zero_of_annular_finite
      (spectrum ℂ A) (fun ε hε ↦
        apm_m00A03_finite_norm_ge_of_finite_norm_gt
          (spectrum ℂ A) hfinite ε hε)
