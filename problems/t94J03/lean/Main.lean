import Mathlib

/-!
# APM t94J03

## Statement repairs

None.

## Encoding questions

None.  `ℝⁿ` is the genuine Euclidean space, `Sⁿ` is the unit sphere in
`ℝⁿ⁺¹`, and maps on a closed subspace or open neighborhood use the
corresponding subtype topology.
-/

open Set

abbrev apm_t94J03_Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev apm_t94J03_Sn (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

theorem apm_t94j03
    {X : Type*} [TopologicalSpace X] [NormalSpace X]
    (A : Set X) (hA : IsClosed A) (n : ℕ) :
    (∀ f : C(A, apm_t94J03_Rn n),
      ∃ F : C(X, apm_t94J03_Rn n),
        ∀ a : A, F a = f a) ∧
    (∀ f : C(A, apm_t94J03_Sn n),
      ∃ (U : Set X) (hUopen : IsOpen U) (hAU : A ⊆ U)
        (F : C(U, apm_t94J03_Sn n)),
        ∀ a : A, F ⟨a, hAU a.2⟩ = f a) := by
  constructor
  · intro f
    obtain ⟨F, hF⟩ := f.exists_restrict_eq hA
    refine ⟨F, ?_⟩
    intro a
    exact DFunLike.congr_fun hF a
  · /-
    Boundary: after applying the Euclidean extension above to the composite
    of a sphere-valued map with `continuous_subtype_val`, the remaining route
    takes the open nonzero locus and normalizes by the norm. I searched
    `TietzeExtension`, Euclidean/sphere retractions, normalization,
    `ContinuousMap`, and norm-division continuity APIs. Mathlib supplies the
    ambient extension but no packaged continuous radial retraction from the
    punctured Euclidean space to `Metric.sphere 0 1`; assembling the subtype
    map, nonvanishing proof, norm-one calculation, and restriction equality
    is the remaining blocker.
    -/
    sorry
