import ConstructionTargets.HomotopySquareStripLadder

/-!
# Endpoint vertical morphisms of a homotopy-grid strip
-/

open Set CategoryTheory
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.HomotopySquareStripEndpoints

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.HomotopySquareUniformGrid
open ConstructionTargets.HomotopySquareRowSubdivisions
open ConstructionTargets.HomotopySquareCellBoundary
open ConstructionTargets.HomotopySquareCellDescent
open ConstructionTargets.HomotopySquareStripLadder
open ConstructionTargets.PathMapPathTransport

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p q : Path x y} {U V : Set X}
variable {C : Type*} [Category C]

theorem mapPath_refl (D : @TwoOpenDescentDatum X _ U V C _)
    (b : Bool) (z : X) (hz : z ∈ twoChart U V b) :
    D.mapPath b (Path.refl z) (fun _ ↦ hz) = 𝟙 (D.obj z) := by
  have hpath : pathInPiece U V b (Path.refl z) (fun _ ↦ hz) =
      Path.refl (⟨z, hz⟩ : CoverPiece U V b) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    rfl
  simp only [TwoOpenDescentDatum.mapPath, hpath, Path.Homotopic.Quotient.mk_refl]
  have hq : Path.Homotopic.Quotient.refl
      (⟨z, by simpa using hz⟩ : CoverPiece U V b) =
      𝟙 (FundamentalGroupoid.mk (⟨z, hz⟩ : CoverPiece U V b)) := by
    rw [FundamentalGroupoid.id_eq_path_refl]
    congr
  rw [hq, CategoryTheory.Functor.map_id]
  simp

theorem mapPath_eq_of_path_eq (D : @TwoOpenDescentDatum X _ U V C _)
    {b : Bool} {a z : X} {r s : Path a z} (hrs : r = s)
    (hr : ∀ t, r t ∈ twoChart U V b) (hs : ∀ t, s t ∈ twoChart U V b) :
    D.mapPath b r hr = D.mapPath b s hs := by
  subst s
  rfl

theorem initialVerticalPath_eq_refl (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i : Fin G.N) :
    (verticalEdge H G i (rowSegmentIndex G 0).castSucc).cast
        (bottomSubdivision H G i).point_zero.symm
        (topSubdivision H G i).point_zero.symm = Path.refl x := by
  apply Path.ext
  funext t
  have hzero : G.coord (rowSegmentIndex G 0).castSucc = 0 := by
    rw [G.coord_eq_grid]
    exact gridCoord_zero G.N G.N_pos
  change H (coordSegment H G i t, G.coord (rowSegmentIndex G 0).castSucc) = x
  rw [hzero]
  exact H.source _

theorem terminalVerticalPath_eq_refl (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V) (i : Fin G.N) :
    (verticalEdge H G i (finalCell H G).succ).cast
        (bottomSubdivision H G i).point_last.symm
        (topSubdivision H G i).point_last.symm = Path.refl y := by
  apply Path.ext
  funext t
  have hone : G.coord (finalCell H G).succ = 1 := by
    rw [finalCell_succ, G.coord_eq_grid, gridCoord_last]
  change H (coordSegment H G i t, G.coord (finalCell H G).succ) = y
  rw [hone]
  exact H.target _

theorem stripVertical_zero (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) (i : Fin G.N) :
    stripVertical H G D i 0 =
      D.mapPath (G.side (i, rowSegmentIndex G 0))
        (verticalEdge H G i (rowSegmentIndex G 0).castSucc)
        (verticalEdge_left_mem H G i (rowSegmentIndex G 0)) := by
  unfold stripVertical
  exact Fin.lastCases_castSucc 0

theorem initial_stripVertical_normalized (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) (i : Fin G.N) :
    eqToHom (congrArg D.obj (bottomSubdivision H G i).point_zero.symm) ≫
        stripVertical H G D i 0 ≫
        eqToHom (congrArg D.obj (topSubdivision H G i).point_zero.symm).symm =
      𝟙 (D.obj x) := by
  let r := verticalEdge H G i (rowSegmentIndex G 0).castSucc
  let hx := (bottomSubdivision H G i).point_zero.symm
  let hy := (topSubdivision H G i).point_zero.symm
  have hp : ∀ t, r t ∈ twoChart U V (G.side (i, rowSegmentIndex G 0)) :=
    verticalEdge_left_mem H G i (rowSegmentIndex G 0)
  have hp' : ∀ t, r.cast hx hy t ∈
      twoChart U V (G.side (i, rowSegmentIndex G 0)) := by
    intro t
    rw [show r.cast hx hy = Path.refl x from initialVerticalPath_eq_refl H G i]
    simpa [r, hx] using hp 0
  have hcast := PathMapPathTransport.TwoOpenDescentDatum.mapPath_cast
    D r hx hy hp hp'
  have hr : r.cast hx hy = Path.refl x := initialVerticalPath_eq_refl H G i
  have hxmem : x ∈ twoChart U V (G.side (i, rowSegmentIndex G 0)) := by
    simpa [hr] using hp' 0
  have hleft := mapPath_eq_of_path_eq D hr hp' (fun _ ↦ hxmem)
  have hrefl := mapPath_refl D (G.side (i, rowSegmentIndex G 0)) x hxmem
  rw [hleft, hrefl] at hcast
  rw [stripVertical_zero H G D i]
  exact hcast.symm

theorem terminal_stripVertical_normalized (H : Path.Homotopy p q)
    (G : HomotopySquareGrid H.toContinuousMap U V)
    (D : @TwoOpenDescentDatum X _ U V C _) (i : Fin G.N) :
    eqToHom (congrArg D.obj (bottomSubdivision H G i).point_last.symm) ≫
        stripVertical H G D i (Fin.last (rowSubdivisionN G + 1)) ≫
        eqToHom (congrArg D.obj (topSubdivision H G i).point_last.symm).symm =
      𝟙 (D.obj y) := by
  let r := verticalEdge H G i (finalCell H G).succ
  let hx := (bottomSubdivision H G i).point_last.symm
  let hy := (topSubdivision H G i).point_last.symm
  have hp : ∀ t, r t ∈ twoChart U V (G.side (i, finalCell H G)) :=
    verticalEdge_right_mem H G i (finalCell H G)
  have hp' : ∀ t, r.cast hx hy t ∈
      twoChart U V (G.side (i, finalCell H G)) := by
    intro t
    rw [show r.cast hx hy = Path.refl y from terminalVerticalPath_eq_refl H G i]
    simpa [r, hx] using hp 0
  have hcast := PathMapPathTransport.TwoOpenDescentDatum.mapPath_cast
    D r hx hy hp hp'
  have hr : r.cast hx hy = Path.refl y := terminalVerticalPath_eq_refl H G i
  have hymem : y ∈ twoChart U V (G.side (i, finalCell H G)) := by
    simpa [hr] using hp' 0
  have hleft := mapPath_eq_of_path_eq D hr hp' (fun _ ↦ hymem)
  have hrefl := mapPath_refl D (G.side (i, finalCell H G)) y hymem
  rw [hleft, hrefl] at hcast
  rw [stripVertical_last H G D i]
  exact hcast.symm

#print axioms mapPath_refl
#print axioms initialVerticalPath_eq_refl
#print axioms terminalVerticalPath_eq_refl
#print axioms initial_stripVertical_normalized
#print axioms terminal_stripVertical_normalized

end ConstructionTargets.HomotopySquareStripEndpoints
