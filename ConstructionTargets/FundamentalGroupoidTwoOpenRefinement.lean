import ConstructionTargets.FundamentalGroupoidTwoOpenDescent

/-!
# Local refinement invariance for two-open descent

This file proves the single-segment split identity needed to compare a
subordinate path subdivision with a refinement obtained by inserting one
vertex.
-/

open Set CategoryTheory
open scoped unitInterval

noncomputable section

namespace ConstructionTargets.FundamentalGroupoidTwoOpenRefinement

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent

variable {X : Type*} [TopologicalSpace X] {U V : Set X}
variable {C : Type*} [Category C]

namespace TwoOpenDescentDatum

variable (D : @TwoOpenDescentDatum X _ U V C _)

theorem pathInPiece_trans {b : Bool} {x y z : X}
    (p : Path x y) (q : Path y z)
    (hp : ∀ t, p t ∈ twoChart U V b)
    (hq : ∀ t, q t ∈ twoChart U V b) :
    pathInPiece U V b (p.trans q) (fun t ↦ by
      rw [Path.trans_apply]
      split_ifs
      · exact hp _
      · exact hq _) =
      (pathInPiece U V b p hp).trans (pathInPiece U V b q hq) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change (p.trans q) t =
    ((pathInPiece U V b p hp).trans (pathInPiece U V b q hq) t).1
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs <;> rfl

theorem pathInPiece_subpath {b : Bool} {x y : X} (p : Path x y)
    (hp : ∀ t, p t ∈ twoChart U V b) (t₀ t₁ : unitInterval) :
    pathInPiece U V b (p.subpath t₀ t₁) (fun _s ↦ hp _) =
      (pathInPiece U V b p hp).subpath t₀ t₁ := by
  apply Path.ext
  funext t
  apply Subtype.ext
  rfl

/-- `mapPath` respects concatenation of two paths in the same cover piece. -/
theorem mapPath_trans {b : Bool} {x y z : X}
    (p : Path x y) (q : Path y z)
    (hp : ∀ t, p t ∈ twoChart U V b)
    (hq : ∀ t, q t ∈ twoChart U V b) :
    D.mapPath b (p.trans q) (fun t ↦ by
      rw [Path.trans_apply]
      split_ifs
      · exact hp _
      · exact hq _) =
      D.mapPath b p hp ≫ D.mapPath b q hq := by
  simp only [FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.mapPath,
    Category.assoc]
  rw [pathInPiece_trans p q hp hq]
  rw [Path.Homotopic.Quotient.mk_trans]
  simp only [← FundamentalGroupoid.comp_eq, Functor.map_comp]
  simp

/-- The path homotopy which removes an inserted parameter remains inside the
same cover piece when the original path does. -/
def subpathSplitHomotopyInPiece {b : Bool} {x y : X} (p : Path x y)
    (hp : ∀ t, p t ∈ twoChart U V b) (t₀ t₁ t₂ : unitInterval) :
    Path.Homotopy
      ((pathInPiece U V b (p.subpath t₀ t₁) (fun _s ↦ hp _)).trans
        (pathInPiece U V b (p.subpath t₁ t₂) (fun _s ↦ hp _)))
      (pathInPiece U V b (p.subpath t₀ t₂) (fun _s ↦ hp _)) := by
  rw [pathInPiece_subpath p hp t₀ t₁,
    pathInPiece_subpath p hp t₁ t₂,
    pathInPiece_subpath p hp t₀ t₂]
  exact Path.Homotopy.subpathTransSubpath (pathInPiece U V b p hp) t₀ t₁ t₂

/-- Splitting one path segment at an intermediate parameter does not change
its two-open descent value. -/
theorem mapPath_subpath_split {b : Bool} {x y : X} (p : Path x y)
    (hp : ∀ t, p t ∈ twoChart U V b) (t₀ t₁ t₂ : unitInterval) :
    D.mapPath b (p.subpath t₀ t₂) (fun _s ↦ hp _) =
      D.mapPath b (p.subpath t₀ t₁) (fun _s ↦ hp _) ≫
        D.mapPath b (p.subpath t₁ t₂) (fun _s ↦ hp _) := by
  have hp01 : ∀ s, p.subpath t₀ t₁ s ∈ twoChart U V b := fun s ↦ hp _
  have hp12 : ∀ s, p.subpath t₁ t₂ s ∈ twoChart U V b := fun s ↦ hp _
  let ptrans := (p.subpath t₀ t₁).trans (p.subpath t₁ t₂)
  have hptrans : ∀ s, ptrans s ∈ twoChart U V b := fun s ↦ by
    dsimp only [ptrans]
    rw [Path.trans_apply]
    split_ifs
    · exact hp01 _
    · exact hp12 _
  have hq : Path.Homotopic.Quotient.mk
      (pathInPiece U V b ptrans hptrans) =
      Path.Homotopic.Quotient.mk
        (pathInPiece U V b (p.subpath t₀ t₂) (fun s ↦ hp _)) := by
    dsimp only [ptrans]
    rw [pathInPiece_trans (p.subpath t₀ t₁) (p.subpath t₁ t₂) hp01 hp12]
    exact Quotient.sound ⟨subpathSplitHomotopyInPiece p hp t₀ t₁ t₂⟩
  calc
    D.mapPath b (p.subpath t₀ t₂) (fun s ↦ hp _) =
        D.mapPath b ptrans hptrans := by
      simp only [FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.mapPath]
      rw [hq]
    _ = _ := by
      simpa only [] using
        (mapPath_trans D (p.subpath t₀ t₁) (p.subpath t₁ t₂) hp01 hp12)

#print axioms pathInPiece_trans
#print axioms pathInPiece_subpath
#print axioms mapPath_trans
#print axioms subpathSplitHomotopyInPiece
#print axioms mapPath_subpath_split

end TwoOpenDescentDatum

end ConstructionTargets.FundamentalGroupoidTwoOpenRefinement
