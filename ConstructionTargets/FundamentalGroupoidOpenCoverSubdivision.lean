import ConstructionTargets.SimplyConnectedOpenCover

/-!
# Path subdivision subordinate to a two-open cover

This is the path-generation input for a future fundamental-groupoid
Seifert--van Kampen theorem.  It records an ordered finite subdivision,
restricted subpaths in the selected cover pieces, and reconstruction in the
path-homotopy quotient.
-/

open Set
open scoped unitInterval

noncomputable section

namespace ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision

variable {X : Type*} [TopologicalSpace X]

/-- Finite ordered subdivision data for a path, subordinate to two sets. -/
structure PathTwoOpenSubdivision {x y : X} (p : Path x y)
    (U V : Set X) where
  n : ℕ
  vertex : Fin (n + 2) → unitInterval
  side : Fin (n + 1) → Bool
  vertex_zero : vertex 0 = 0
  vertex_last : vertex (Fin.last (n + 1)) = 1
  monotone_vertex : Monotone vertex
  segment_mem : ∀ k, Icc (vertex k.castSucc) (vertex k.succ) ⊆
    p ⁻¹' twoChart U V (side k)

namespace PathTwoOpenSubdivision

variable {x y : X} {p : Path x y} {U V : Set X}

def point (S : PathTwoOpenSubdivision p U V) : Fin (S.n + 2) → X :=
  fun k ↦ p (S.vertex k)

def piece (S : PathTwoOpenSubdivision p U V) (k : Fin (S.n + 1)) :
    Path (S.point k.castSucc) (S.point k.succ) :=
  p.subpath (S.vertex k.castSucc) (S.vertex k.succ)

theorem vertex_le_succ (S : PathTwoOpenSubdivision p U V)
    (k : Fin (S.n + 1)) : S.vertex k.castSucc ≤ S.vertex k.succ :=
  S.monotone_vertex k.castSucc_le_succ

/-- Every restricted subpath lies in its selected cover member. -/
theorem piece_mem (S : PathTwoOpenSubdivision p U V)
    (k : Fin (S.n + 1)) (s : unitInterval) :
    S.piece k s ∈ twoChart U V (S.side k) := by
  have hs : S.piece k s ∈ Set.range (S.piece k) := Set.mem_range_self s
  change (p.subpath (S.vertex k.castSucc) (S.vertex k.succ)) s ∈
    Set.range (p.subpath (S.vertex k.castSucc) (S.vertex k.succ)) at hs
  rw [Path.range_subpath_of_le p _ _ (S.vertex_le_succ k)] at hs
  rcases hs with ⟨r, hr, hrs⟩
  change (p.subpath (S.vertex k.castSucc) (S.vertex k.succ)) s ∈
    twoChart U V (S.side k)
  rw [← hrs]
  exact S.segment_mem k hr

theorem point_zero (S : PathTwoOpenSubdivision p U V) : S.point 0 = x := by
  simp [point, S.vertex_zero, p.source]

theorem point_last (S : PathTwoOpenSubdivision p U V) :
    S.point (Fin.last (S.n + 1)) = y := by
  simp [point, S.vertex_last, p.target]

/-- Concatenating the restricted subpaths reconstructs the original path up
to endpoint-preserving path homotopy. -/
theorem concat_piece_homotopic (S : PathTwoOpenSubdivision p U V) :
    Path.Homotopic (Path.concat S.point S.piece)
      (p.cast S.point_zero S.point_last) := by
  have hparts := Path.Homotopic.concat_subpath p S.vertex
  have hend : p.subpath (S.vertex 0) (S.vertex (Fin.last (S.n + 1))) =
      p.cast S.point_zero S.point_last := by
    apply Path.ext
    funext s
    change p (Icc.convexCombo (S.vertex 0)
      (S.vertex (Fin.last (S.n + 1))) s) = p s
    rw [S.vertex_zero, S.vertex_last, Icc.convexCombo_zero_one]
  simpa [point, piece] using hparts.trans
    (hend ▸ Path.Homotopic.refl (p.cast S.point_zero S.point_last))

/-- The corresponding fundamental-groupoid morphism is the finite composite
of morphisms represented by paths lying in individual cover members. -/
theorem quotient_concat_eq (S : PathTwoOpenSubdivision p U V) :
    Path.Homotopic.Quotient.mk (Path.concat S.point S.piece) =
      Path.Homotopic.Quotient.mk (p.cast S.point_zero S.point_last) :=
  Quotient.sound S.concat_piece_homotopic

end PathTwoOpenSubdivision

/-- Every path in a two-open cover admits finite subordinate subdivision data. -/
theorem exists_pathTwoOpenSubdivision {x y : X} (p : Path x y)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    Nonempty (PathTwoOpenSubdivision p U V) := by
  let cover : Bool → Set unitInterval := fun b ↦
    if b then p ⁻¹' U else p ⁻¹' V
  have hopen : ∀ b, IsOpen (cover b) := by
    intro b
    cases b <;> simp [cover, hU, hV, IsOpen.preimage p.continuous]
  have hall : (Set.univ : Set unitInterval) ⊆ ⋃ b, cover b := by
    intro t _
    have hpt : p t ∈ U ∪ V := by rw [hcover]; trivial
    rcases hpt with htU | htV
    · exact Set.mem_iUnion.mpr ⟨true, by simpa [cover] using htU⟩
    · exact Set.mem_iUnion.mpr ⟨false, by simpa [cover] using htV⟩
  obtain ⟨n, vertex, side, hzero, hlast, hmono, hsegment⟩ :=
    exists_fin_Icc_subset_open_cover_unitInterval hopen hall
  refine ⟨{
    n := n
    vertex := vertex
    side := side
    vertex_zero := hzero
    vertex_last := hlast
    monotone_vertex := hmono
    segment_mem := ?_ }⟩
  intro k t ht
  have hm := hsegment k ht
  cases hside : side k <;>
    simpa [cover, twoChart, hside] using hm

#print axioms PathTwoOpenSubdivision.piece_mem
#print axioms PathTwoOpenSubdivision.concat_piece_homotopic
#print axioms PathTwoOpenSubdivision.quotient_concat_eq
#print axioms exists_pathTwoOpenSubdivision

end ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
