import Mathlib
import ConstructionTargets.StatementSurfaceModels

/-! # t96A01: finite-index subgroups of a genus-four surface group

A closed connected orientable surface of genus four is specified by a
homeomorphism to the concrete standard genus-four polygon quotient. This is
an explicit meaning of genus, not a supplied fundamental-group computation.
The group in the conclusion has 6n+2 generators and the single product-of-
commutators relator. FiniteIndex excludes Mathlib's index=0 sentinel for an
infinite index; it adds no restriction to the source's finite natural index.
-/

open ConstructionTargets.StatementSurfaceModels ConstructionTargets.Surfaces

theorem apm_t96a01
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [T2Space S] [SecondCountableTopology S] [CompactSpace S] [ConnectedSpace S]
    (hgenus : Nonempty (S ≃ₜ Surface true 4)) (s : S)
    (n : ℕ) (H : Subgroup (FundamentalGroup S s))
    [H.FiniteIndex] (hindex : H.index = n) :
    Nonempty (H ≃* OrientableSurfaceGroup (3 * n + 1)) := by
  sorry
