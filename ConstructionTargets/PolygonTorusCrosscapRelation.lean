import ConstructionTargets.PolygonOverlapHomotopyEquivCircle

open Set Topology
noncomputable section

namespace ConstructionTargets.PolygonTorusCrosscapRelation

open ConstructionTargets.Surfaces
open ConstructionTargets.RadialQuotientOpenSets
open ConstructionTargets.PolygonRadialOpenCover

def reverse (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

@[simp] theorem reverse_val (t : Set.Icc (0 : ℝ) 1) :
    (reverse t : ℝ) = 1 - t := rfl

@[simp] theorem reverse_reverse (t : Set.Icc (0 : ℝ) 1) :
    reverse (reverse t) = t := by
  apply Subtype.ext
  simp [reverse]

/-- The six-edge boundary word `a b a⁻¹ b⁻¹ c c`. -/
inductive TorusCrosscapRel : Disk → Disk → Prop
  | a (t : Set.Icc (0 : ℝ) 1) :
      TorusCrosscapRel (edgePoint 6 0 t) (edgePoint 6 2 (reverse t))
  | b (t : Set.Icc (0 : ℝ) 1) :
      TorusCrosscapRel (edgePoint 6 1 t) (edgePoint 6 3 (reverse t))
  | c (t : Set.Icc (0 : ℝ) 1) :
      TorusCrosscapRel (edgePoint 6 4 t) (edgePoint 6 5 t)

theorem torusCrosscapRel_norm_eq {x y : Disk}
    (h : TorusCrosscapRel x y) : ‖(x : ℂ)‖ = ‖(y : ℂ)‖ := by
  cases h <;> rw [norm_edgePoint, norm_edgePoint]

theorem torusCrosscapRel_boundary {x y : Disk}
    (h : TorusCrosscapRel x y) : radius x = 1 ∧ radius y = 1 := by
  cases h <;> exact ⟨by simp [radius, norm_edgePoint], by simp [radius, norm_edgePoint]⟩

abbrev TorusCrosscapQuotient :=
  Quotient (Relation.EqvGen.setoid TorusCrosscapRel)

def torusCrosscapQuotientMap : Disk → TorusCrosscapQuotient :=
  fun x => Quotient.mk _ x

theorem identifies_a (t : Set.Icc (0 : ℝ) 1) :
    torusCrosscapQuotientMap (edgePoint 6 0 t) =
      torusCrosscapQuotientMap (edgePoint 6 2 (reverse t)) :=
  Quotient.sound (.rel _ _ (.a t))

theorem identifies_b (t : Set.Icc (0 : ℝ) 1) :
    torusCrosscapQuotientMap (edgePoint 6 1 t) =
      torusCrosscapQuotientMap (edgePoint 6 3 (reverse t)) :=
  Quotient.sound (.rel _ _ (.b t))

theorem identifies_c (t : Set.Icc (0 : ℝ) 1) :
    torusCrosscapQuotientMap (edgePoint 6 4 t) =
      torusCrosscapQuotientMap (edgePoint 6 5 t) :=
  Quotient.sound (.rel _ _ (.c t))

end ConstructionTargets.PolygonTorusCrosscapRelation
