import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.PolygonSurfacePiOne
import ConstructionTargets.SurfaceClassification
import ConstructionTargets.CoveringDegree
import ConstructionTargets.CoveringMonodromyCosets
import ConstructionTargets.SuppliedCoverAlgebra

/-! # Blueprint for t96A01: finite-index subgroups of a genus-four surface group -/

open ConstructionTargets.StatementSurfaceModels ConstructionTargets.Surfaces

noncomputable section

/-! ## Definitions shared by the independent lemma seats -/

/-- The canonical interior basepoint of the standard orientable polygon surface. -/
abbrev T96A01SurfaceBase (g : ℕ) : Surface true g :=
  surfacePoint true g

/-! ## Independent library interfaces -/

/-- **LIBRARY (polygon-surface fundamental group).**  The standard orientable
genus-`g` polygon quotient has the usual one-relator surface group. -/
theorem t96A01_orientableSurface_fundamentalGroup (g : ℕ) :
    Nonempty
      (FundamentalGroup (Surface true g) (T96A01SurfaceBase g) ≃*
        OrientableSurfaceGroup g) := by
  sorry

/-- Finite index rules out Mathlib's `index = 0` sentinel. -/
theorem t96A01_index_pos
    {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
    (n : ℕ) (hindex : H.index = n) :
    0 < n := by
  rw [← hindex]
  exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

/-- **LIBRARY (covering-subgroup correspondence).**  A finite-index subgroup
is realized as the fundamental group of a connected cover whose fibre has the
prescribed cardinality. -/
theorem t96A01_finiteIndexSubgroup_connectedCover
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [T2Space S] [SecondCountableTopology S] [CompactSpace S] [ConnectedSpace S]
    (s : S)
    (n : ℕ) (hn : 0 < n) (H : Subgroup (FundamentalGroup S s))
    [H.FiniteIndex] (hindex : H.index = n) :
    ∃ (E : Type) (_ : TopologicalSpace E) (p : E → S) (e : E),
      IsCoveringMap p ∧ PathConnectedSpace E ∧ p e = s ∧
      Nat.card (p ⁻¹' {s}) = n ∧
      Nonempty (FundamentalGroup E e ≃* H) := by
  sorry

/-- **LIBRARY (finite-cover Euler characteristic and surface recognition).**
A connected `n`-sheeted cover of a genus-four surface has genus `3*n+1`.
The conclusion includes the harmless basepoint transport needed downstream. -/
theorem t96A01_connectedFiniteCover_surfaceFundamentalGroup
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [T2Space S] [SecondCountableTopology S] [CompactSpace S] [ConnectedSpace S]
    (hgenus : Nonempty (S ≃ₜ Surface true 4)) (s : S)
    (n : ℕ) (hn : 0 < n)
    (E : Type*) [TopologicalSpace E] [PathConnectedSpace E]
    (p : E → S) (e : E) (hp : IsCoveringMap p) (hpe : p e = s)
    (hsheets : Nat.card (p ⁻¹' {s}) = n) :
    Nonempty
      (FundamentalGroup E e ≃*
        FundamentalGroup (Surface true (3 * n + 1))
          (T96A01SurfaceBase (3 * n + 1))) := by
  sorry

theorem apm_t96a01
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [T2Space S] [SecondCountableTopology S] [CompactSpace S] [ConnectedSpace S]
    (hgenus : Nonempty (S ≃ₜ Surface true 4)) (s : S)
    (n : ℕ) (H : Subgroup (FundamentalGroup S s))
    [H.FiniteIndex] (hindex : H.index = n) :
    Nonempty (H ≃* OrientableSurfaceGroup (3 * n + 1)) := by
  have hn : 0 < n := t96A01_index_pos H n hindex
  obtain ⟨E, topE, p, e, hp, hE, hpe, hsheets, hsubgroup⟩ :=
    t96A01_finiteIndexSubgroup_connectedCover s n hn H hindex
  letI : TopologicalSpace E := topE
  letI : PathConnectedSpace E := hE
  obtain ⟨hsurface⟩ :=
    t96A01_connectedFiniteCover_surfaceFundamentalGroup
      hgenus s n hn E p e hp hpe hsheets
  obtain ⟨hsubgroup⟩ := hsubgroup
  obtain ⟨hpi₁⟩ := t96A01_orientableSurface_fundamentalGroup (3 * n + 1)
  exact ⟨hsubgroup.symm.trans (hsurface.trans hpi₁)⟩

#print axioms apm_t96a01
