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

/-- Every value of an ordered subpath lies in the range of a containing
ordered subpath. -/
theorem subpath_value_mem_range_of_ordered {x y : X} (p : Path x y)
    (t₀ t₂ a c s : unitInterval) (h02 : t₀ ≤ t₂)
    (ha : t₀ ≤ a) (hc : c ≤ t₂) (hac : a ≤ c) :
    p.subpath a c s ∈ Set.range (p.subpath t₀ t₂) := by
  have hs : p.subpath a c s ∈ Set.range (p.subpath a c) := Set.mem_range_self s
  rw [Path.range_subpath_of_le p a c hac] at hs
  rw [Path.range_subpath_of_le p t₀ t₂ h02]
  exact Set.image_mono (Set.Icc_subset_Icc ha hc) hs

/-- Under ordered parameters, the canonical split-subpath homotopy never
leaves the range of the unsplit subpath. -/
theorem subpathTransSubpath_mem_range {x y : X} (p : Path x y)
    (t₀ t₁ t₂ : unitInterval) (h01 : t₀ ≤ t₁) (h12 : t₁ ≤ t₂) :
  ∀ z, Path.Homotopy.subpathTransSubpath p t₀ t₁ t₂ z ∈
      Set.range (p.subpath t₀ t₂) := by
  intro z
  unfold Path.Homotopy.subpathTransSubpath
  rw [Path.Homotopy.trans_apply]
  split_ifs with h
  · change
      ((p.subpath t₀ (Set.Icc.convexCombo t₁ t₂ _)).trans
        (p.subpath (Set.Icc.convexCombo t₁ t₂ _) t₂)) z.2 ∈ _
    rw [Path.trans_apply]
    split_ifs
    · apply subpath_value_mem_range_of_ordered p t₀ t₂
      · exact h01.trans h12
      · exact le_rfl
      · exact Set.Icc.convexCombo_le h12 _
      · exact h01.trans (Set.Icc.le_convexCombo h12 _)
    · apply subpath_value_mem_range_of_ordered p t₀ t₂
      · exact h01.trans h12
      · exact h01.trans (Set.Icc.le_convexCombo h12 _)
      · exact le_rfl
      · exact Set.Icc.convexCombo_le h12 _
  · change p.subpath t₀ t₂ _ ∈ Set.range (p.subpath t₀ t₂)
    exact Set.mem_range_self _

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

/-- Membership of an ordered whole segment restricts to any ordered
subsegment.  This is the range-theoretic prerequisite for a localized split
homotopy and does not require membership of the ambient path outside the
segment. -/
theorem subpath_mem_of_mem_ordered_segment {b : Bool} {x y : X}
    (p : Path x y) (t₀ t₂ a c : unitInterval)
    (h02 : t₀ ≤ t₂) (ha : t₀ ≤ a) (hc : c ≤ t₂) (hac : a ≤ c)
    (hp02 : ∀ s, p.subpath t₀ t₂ s ∈ twoChart U V b) :
    ∀ s, p.subpath a c s ∈ twoChart U V b := by
  intro s
  have hrange : Set.range (p.subpath t₀ t₂) ⊆ twoChart U V b := by
    rintro _ ⟨r, rfl⟩
    exact hp02 r
  apply hrange
  have hs : p.subpath a c s ∈ Set.range (p.subpath a c) := Set.mem_range_self s
  rw [Path.range_subpath_of_le p a c hac] at hs
  rw [Path.range_subpath_of_le p t₀ t₂ h02]
  exact Set.image_mono (Set.Icc_subset_Icc ha hc) hs

/-- The split-subpath homotopy lifts to one cover piece from membership of the
whole ordered segment alone. -/
def subpathSplitHomotopyInPiece_of_subpath_mem {b : Bool} {x y : X}
    (p : Path x y) (t₀ t₁ t₂ : unitInterval)
    (h01 : t₀ ≤ t₁) (h12 : t₁ ≤ t₂)
    (hp02 : ∀ s, p.subpath t₀ t₂ s ∈ twoChart U V b) :
    Path.Homotopy
      (pathInPiece U V b
        ((p.subpath t₀ t₁).trans (p.subpath t₁ t₂)) (fun s ↦ by
          rw [Path.trans_apply]
          split_ifs
          · exact subpath_mem_of_mem_ordered_segment p t₀ t₂ t₀ t₁
              (h01.trans h12) le_rfl h12 h01 hp02 _
          · exact subpath_mem_of_mem_ordered_segment p t₀ t₂ t₁ t₂
              (h01.trans h12) h01 le_rfl h12 hp02 _))
      (pathInPiece U V b (p.subpath t₀ t₂) hp02) := by
  let H := Path.Homotopy.subpathTransSubpath p t₀ t₁ t₂
  let hrange : Set.range (p.subpath t₀ t₂) ⊆ twoChart U V b := by
    rintro _ ⟨s, rfl⟩
    exact hp02 s
  refine
    { toFun := fun z ↦ ⟨H z, hrange (subpathTransSubpath_mem_range p t₀ t₁ t₂ h01 h12 z)⟩
      continuous_toFun := H.continuous.subtype_mk _
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro s
    apply Subtype.ext
    change H.toFun (0, s) = _
    rw [H.map_zero_left]
    rfl
  · intro s
    apply Subtype.ext
    exact H.map_one_left s
  · intro t s hs
    apply Subtype.ext
    change H.toFun (t, s) = _
    exact H.prop' t s hs

/-- Localized split invariance: only the ordered whole segment, rather than
the ambient path, must lie in the selected cover piece. -/
theorem mapPath_subpath_split_of_subpath_mem {b : Bool} {x y : X}
    (p : Path x y) (t₀ t₁ t₂ : unitInterval)
    (h01 : t₀ ≤ t₁) (h12 : t₁ ≤ t₂)
    (hp02 : ∀ s, p.subpath t₀ t₂ s ∈ twoChart U V b) :
    D.mapPath b (p.subpath t₀ t₂) hp02 =
      D.mapPath b (p.subpath t₀ t₁)
          (subpath_mem_of_mem_ordered_segment p t₀ t₂ t₀ t₁
            (h01.trans h12) le_rfl h12 h01 hp02) ≫
        D.mapPath b (p.subpath t₁ t₂)
          (subpath_mem_of_mem_ordered_segment p t₀ t₂ t₁ t₂
            (h01.trans h12) h01 le_rfl h12 hp02) := by
  let hp01 := subpath_mem_of_mem_ordered_segment p t₀ t₂ t₀ t₁
    (h01.trans h12) le_rfl h12 h01 hp02
  let hp12 := subpath_mem_of_mem_ordered_segment p t₀ t₂ t₁ t₂
    (h01.trans h12) h01 le_rfl h12 hp02
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
        (pathInPiece U V b (p.subpath t₀ t₂) hp02) := by
    dsimp only [ptrans]
    exact Quotient.sound ⟨subpathSplitHomotopyInPiece_of_subpath_mem
      p t₀ t₁ t₂ h01 h12 hp02⟩
  calc
    D.mapPath b (p.subpath t₀ t₂) hp02 = D.mapPath b ptrans hptrans := by
      simp only [FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum.mapPath]
      rw [hq]
    _ = _ := by
      simpa only [hp01, hp12] using
        mapPath_trans D (p.subpath t₀ t₁) (p.subpath t₁ t₂) hp01 hp12

#print axioms pathInPiece_trans
#print axioms pathInPiece_subpath
#print axioms mapPath_trans
#print axioms subpathSplitHomotopyInPiece
#print axioms mapPath_subpath_split
#print axioms subpath_mem_of_mem_ordered_segment
#print axioms subpathSplitHomotopyInPiece_of_subpath_mem
#print axioms mapPath_subpath_split_of_subpath_mem
#print axioms FundamentalGroupoidTwoOpenRefinement.subpath_value_mem_range_of_ordered
#print axioms FundamentalGroupoidTwoOpenRefinement.subpathTransSubpath_mem_range

end TwoOpenDescentDatum

end ConstructionTargets.FundamentalGroupoidTwoOpenRefinement
