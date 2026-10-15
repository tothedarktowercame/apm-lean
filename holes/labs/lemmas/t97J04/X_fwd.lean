import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.GroupTheory.PresentedGroup
import ConstructionTargets.Surfaces
import ConstructionTargets.GenusTwoSurfacePiOne
import ConstructionTargets.TwoOpenAttachOneCell
import ConstructionTargets.IntegralOpenCoverMayerVietoris
import ConstructionTargets.IntegralSingularHomologyComparison
import ConstructionTargets.PolygonSurfaceHomology

open CategoryTheory Set

noncomputable section

abbrev apm_t97J04_Disk := ConstructionTargets.Surfaces.Disk

def apm_t97J04_edgePoint (n : ℕ) (j : Fin n)
    (t : Set.Icc (0 : ℝ) 1) : apm_t97J04_Disk :=
  ConstructionTargets.Surfaces.edgePoint n j t

/-- The genus-two octagon, together with a second disk attached along the
meridian represented by the fifth edge.  The first four octagon letters are
the first punctured torus and the last four are the second punctured torus;
the extra disk is its meridional disk. -/
inductive apm_t97J04_ComplexRel :
    Sum apm_t97J04_Disk apm_t97J04_Disk →
      Sum apm_t97J04_Disk apm_t97J04_Disk → Prop
  | a (t : Set.Icc (0 : ℝ) 1) :
      apm_t97J04_ComplexRel
        (.inl (apm_t97J04_edgePoint 8 0 t))
        (.inl (apm_t97J04_edgePoint 8 2 ⟨1 - t.1, by
          constructor <;> linarith [t.2.1, t.2.2]⟩))
  | b (t : Set.Icc (0 : ℝ) 1) :
      apm_t97J04_ComplexRel
        (.inl (apm_t97J04_edgePoint 8 1 t))
        (.inl (apm_t97J04_edgePoint 8 3 ⟨1 - t.1, by
          constructor <;> linarith [t.2.1, t.2.2]⟩))
  | c (t : Set.Icc (0 : ℝ) 1) :
      apm_t97J04_ComplexRel
        (.inl (apm_t97J04_edgePoint 8 4 t))
        (.inl (apm_t97J04_edgePoint 8 6 ⟨1 - t.1, by
          constructor <;> linarith [t.2.1, t.2.2]⟩))
  | d (t : Set.Icc (0 : ℝ) 1) :
      apm_t97J04_ComplexRel
        (.inl (apm_t97J04_edgePoint 8 5 t))
        (.inl (apm_t97J04_edgePoint 8 7 ⟨1 - t.1, by
          constructor <;> linarith [t.2.1, t.2.2]⟩))
  | meridian (t : Set.Icc (0 : ℝ) 1) :
      apm_t97J04_ComplexRel
        (.inl (apm_t97J04_edgePoint 8 4 t))
        (.inr (apm_t97J04_edgePoint 1 0 t))

def apm_t97J04_X :=
  Quotient (Relation.EqvGen.setoid apm_t97J04_ComplexRel)

noncomputable instance : TopologicalSpace apm_t97J04_X :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t97J04_Disk apm_t97J04_Disk ↦ Quotient.mk _ x)
    inferInstance

def apm_t97J04_basepoint : apm_t97J04_X :=
  Quotient.mk _ (.inl (0 : apm_t97J04_Disk))

def apm_t97J04_relator : FreeGroup (Fin 3) :=
  FreeGroup.of 0 * FreeGroup.of 1 *
    (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹

abbrev apm_t97J04_piOne :=
  PresentedGroup ({apm_t97J04_relator} : Set (FreeGroup (Fin 3)))

abbrev apm_t97J04_H (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of apm_t97J04_X))


/-! # Blueprint for APM t97J04 (claude-14, 2026-10-15)

`X` = genus-two octagon + a disk on the meridian edge `c` (edge 4).  Route:
`X ≅ (W ∪_word D²) ∪_c D²`, where `W` is the orbit-indexed wedge of four
circles, `word` the polygon boundary loop (`[a,b][c,d]`), and `c` the leg of
edge 4.  Part A proves, once and generically, π₁ and homology of a space with
one 2-cell attached along a loop `γ : C(Circle, Y)`; part B applies it twice.
No homotopy equivalence of `X` itself is constructed.
-/

namespace APMT97J04

open scoped ContinuousMap

open ConstructionTargets
open ConstructionTargets.PolygonSurfacePiOne
open ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient

/-! ## Part A: attaching one 2-cell along a loop -/

section AttachCell

variable {Y : Type} [TopologicalSpace Y]

/-- The boundary circle of the attached disk. -/
abbrev circleToDisk (z : Circle) : apm_t97J04_Disk :=
  PolygonSurfaceHomology.circleToPolygonDisk z

/-- `inl (γ z) ~ inr z` for `z` on the boundary circle of the disk. -/
inductive CellRel (γ : C(Circle, Y)) :
    Y ⊕ apm_t97J04_Disk → Y ⊕ apm_t97J04_Disk → Prop
  | boundary (z : Circle) : CellRel γ (.inl (γ z)) (.inr (circleToDisk z))

/-- `Y ∪_γ D²`. -/
def Cell (γ : C(Circle, Y)) : Type :=
  Quotient (Relation.EqvGen.setoid (CellRel γ))

instance (γ : C(Circle, Y)) : TopologicalSpace (Cell γ) :=
  TopologicalSpace.coinduced
    (fun x : Y ⊕ apm_t97J04_Disk ↦ Quotient.mk (Relation.EqvGen.setoid (CellRel γ)) x)
    inferInstance

def cellMk (γ : C(Circle, Y)) (x : Y ⊕ apm_t97J04_Disk) : Cell γ :=
  Quotient.mk (Relation.EqvGen.setoid (CellRel γ)) x

theorem continuous_cellMk (γ : C(Circle, Y)) : Continuous (cellMk γ) :=
  continuous_coinduced_rng

/-- The inclusion `Y → Y ∪_γ D²`. -/
def cellIncl (γ : C(Circle, Y)) : C(Y, Cell γ) :=
  ⟨fun y ↦ cellMk γ (.inl y), (continuous_cellMk γ).comp continuous_inl⟩

/-- The characteristic map of the cell. -/
def cellDisk (γ : C(Circle, Y)) : C(apm_t97J04_Disk, Cell γ) :=
  ⟨fun z ↦ cellMk γ (.inr z), (continuous_cellMk γ).comp continuous_inr⟩

/-- Outer piece: `Y` together with the annulus `1/3 < |z| ≤ 1`. -/
def cellOuter (γ : C(Circle, Y)) : Set (Cell γ) :=
  cellMk γ '' (Set.range (Sum.inl : Y → Y ⊕ apm_t97J04_Disk) ∪
    Sum.inr '' {z : apm_t97J04_Disk | (1 : ℝ) / 3 < ‖(z : ℂ)‖})

/-- Inner piece: the open disk `|z| < 2/3`. -/
def cellInner (γ : C(Circle, Y)) : Set (Cell γ) :=
  cellMk γ '' (Sum.inr '' {z : apm_t97J04_Disk | ‖(z : ℂ)‖ < (2 : ℝ) / 3})

/-- `Y` into the outer piece. -/
def cellInclOuter (γ : C(Circle, Y)) : C(Y, cellOuter γ) :=
  ⟨fun y ↦ ⟨cellIncl γ y, ⟨.inl y, Or.inl ⟨y, rfl⟩, rfl⟩⟩,
    (cellIncl γ).continuous.subtype_mk _⟩

/-- The circle of radius `1/2` in the disk. -/
def halfDisk (z : Circle) : apm_t97J04_Disk :=
  ⟨(z : ℂ) / 2, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_div, Circle.norm_coe]
    norm_num⟩

theorem norm_halfDisk (z : Circle) : ‖((halfDisk z : apm_t97J04_Disk) : ℂ)‖ = 1 / 2 := by
  change ‖(z : ℂ) / 2‖ = 1 / 2
  rw [norm_div, Circle.norm_coe]
  norm_num

theorem continuous_halfDisk : Continuous halfDisk :=
  (continuous_subtype_val.div_const 2).subtype_mk _

/-- The radius-`1/2` circle in the overlap annulus. -/
def cellOverlapCircle (γ : C(Circle, Y)) :
    C(Circle, (cellOuter γ ∩ cellInner γ : Set (Cell γ))) :=
  ⟨fun z ↦ ⟨cellMk γ (.inr (halfDisk z)),
      ⟨⟨.inr (halfDisk z), Or.inr ⟨halfDisk z, by
          change (1 : ℝ) / 3 < ‖((halfDisk z : apm_t97J04_Disk) : ℂ)‖
          rw [norm_halfDisk]; norm_num, rfl⟩, rfl⟩,
       ⟨.inr (halfDisk z), ⟨halfDisk z, by
          change ‖((halfDisk z : apm_t97J04_Disk) : ℂ)‖ < (2 : ℝ) / 3
          rw [norm_halfDisk]; norm_num, rfl⟩, rfl⟩⟩⟩,
    (((continuous_cellMk γ).comp (continuous_inr.comp continuous_halfDisk))).subtype_mk _⟩

/-- The class of `γ` in `π₁(Y, y)`, for any name `y` of `γ 1`. -/
def loopClassAt (γ : C(Circle, Y)) (y : Y) (h : γ 1 = y) : FundamentalGroup Y y :=
  Path.Homotopic.Quotient.cast
    (FundamentalGroup.map γ 1 PolygonSurfaceHomology.circleIntegerLoopOneClass)
    h.symm h.symm

/-- Integral singular homology (the problem's functor) and induced maps. -/
abbrev H (k : ℕ) (S : Type) [TopologicalSpace S] : ModuleCat ℤ :=
  PolygonSurfaceHomology.SpaceH S k

def Hmap {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    (f : C(S, T)) (k : ℕ) : H k S ⟶ H k T :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)


/-- A1. The two pieces are open and cover. Saturation: `cellMk⁻¹(outer)` is
`range inl ∪ inr '' {1/3 < |z|}` (boundary points of the disk are related only
to points of `Y`); same for inner (no boundary points). -/
lemma cell_cover (γ : C(Circle, Y)) :
    IsOpen (cellOuter γ) ∧ IsOpen (cellInner γ) ∧
      cellOuter γ ∪ cellInner γ = Set.univ := by
  sorry

/-- A2. The inner piece is homeomorphic to the open ball `|z| < 2/3`. -/
lemma cell_inner_contractible (γ : C(Circle, Y)) :
    ContractibleSpace (cellInner γ) := by
  sorry

/-- A3. The overlap annulus `1/3 < |z| < 2/3` deformation retracts to the
radius-`1/2` circle. -/
lemma cell_overlap_hequiv (γ : C(Circle, Y)) :
    ∃ e : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≃ₕ Circle,
      e.invFun = cellOverlapCircle γ := by
  sorry

/-- A4. Radial retraction of the outer piece onto `Y`:
`inr w ↦ inl (γ (w / |w|))`, homotopic to the identity through
`inr w ↦ inr ((1 - t) w + t w / |w|)` (as in t99A01's succ_retract/deform). -/
def cell_outer_hequiv_aux_scale (t : unitInterval) (z : ℂ) : ℝ :=
  t.1 + (1 - t.1) / ‖z‖

lemma cell_outer_hequiv_aux_scale_norm (t : unitInterval) (z : ℂ)
    (hz0 : z ≠ 0) (hz1 : ‖z‖ ≤ 1) :
    ‖(cell_outer_hequiv_aux_scale t z : ℂ) * z‖ ≤ 1 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hs0 : 0 ≤ (t : ℝ) + (1 - t.1) / ‖z‖ :=
    add_nonneg ht0 (div_nonneg (sub_nonneg.mpr ht1) hn.le)
  rw [norm_mul]
  change ‖(((t : ℝ) + (1 - t.1) / ‖z‖ : ℝ) : ℂ)‖ * ‖z‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
  field_simp
  nlinarith

lemma cell_outer_hequiv_aux_scale_ne (t : unitInterval) (z : ℂ) (hz0 : z ≠ 0) :
    (cell_outer_hequiv_aux_scale t z : ℂ) * z ≠ 0 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  apply mul_ne_zero
  · rw [cell_outer_hequiv_aux_scale]
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have hp : 0 < (t : ℝ) + (1 - t.1) / ‖z‖ := by
      by_cases ht : (t : ℝ) = 0
      · rw [ht]
        positivity
      · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne ht0 (Ne.symm ht))
          (div_nonneg (sub_nonneg.mpr ht1) hn.le)
    exact_mod_cast hp.ne'
  · exact hz0

def cell_outer_hequiv_aux_radial (z : ℂ) : Circle :=
  if h : z = 0 then 1 else
    ⟨z / (‖z‖ : ℂ), by
      simp [Submonoid.unitSphere, div_self (norm_ne_zero_iff.mpr h)]⟩

lemma cell_outer_hequiv_aux_radial_circle (z : Circle) :
    cell_outer_hequiv_aux_radial (z : ℂ) = z := by
  apply Subtype.ext
  have hz : (z : ℂ) ≠ 0 := by
    intro h
    have hn := Circle.norm_coe z
    rw [h, norm_zero] at hn
    norm_num at hn
  simp [cell_outer_hequiv_aux_radial, hz, Circle.norm_coe]

def cell_outer_hequiv_aux_raw (gamma : C(Circle, Y)) :
    Y ⊕ apm_t97J04_Disk → Y
  | .inl y => y
  | .inr z => gamma (cell_outer_hequiv_aux_radial (z : ℂ))

lemma cell_outer_hequiv_aux_raw_boundary (gamma : C(Circle, Y)) (z : Circle) :
    cell_outer_hequiv_aux_raw gamma (.inl (gamma z)) =
      cell_outer_hequiv_aux_raw gamma (.inr (circleToDisk z)) := by
  change gamma z = gamma (cell_outer_hequiv_aux_radial ((circleToDisk z : apm_t97J04_Disk) : ℂ))
  congr 1
  apply Subtype.ext
  simp [cell_outer_hequiv_aux_radial, PolygonSurfaceHomology.circleToPolygonDisk,
    Circle.norm_coe]

lemma cell_outer_hequiv_aux_raw_respects (gamma : C(Circle, Y))
    {x y : Y ⊕ apm_t97J04_Disk}
    (h : Relation.EqvGen (CellRel gamma) x y) :
    cell_outer_hequiv_aux_raw gamma x = cell_outer_hequiv_aux_raw gamma y := by
  induction h with
  | rel a b h =>
      cases h with
      | boundary z => exact cell_outer_hequiv_aux_raw_boundary gamma z
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def cell_outer_hequiv_aux_descend (gamma : C(Circle, Y)) : Cell gamma → Y :=
  Quotient.lift (cell_outer_hequiv_aux_raw gamma)
    (fun _ _ h => cell_outer_hequiv_aux_raw_respects gamma h)

lemma cell_outer_hequiv_aux_descend_incl (gamma : C(Circle, Y)) (y : Y) :
    cell_outer_hequiv_aux_descend gamma (cellIncl gamma y) = y := by
  rfl

/-- A4a. The descended radial retraction is continuous on the outer piece.
`cellOuter γ` is open and saturated, so `cellMk` restricted to its preimage is
a quotient map (`IsQuotientMap.restrictPreimage_isOpen`); on that preimage the
raw map is continuous (`inl`: identity; `inr` on `1/3 < |z|`: `γ ∘ radial`,
with `z ≠ 0`). -/
lemma cell_outer_hequiv_aux_continuous (γ : C(Circle, Y)) :
    Continuous (fun p : cellOuter γ ↦ cell_outer_hequiv_aux_descend γ p.1) := by
  sorry

/-- A4b. Radial homotopy from `cellInclOuter γ ∘ retraction` to the identity
of the outer piece: `H(t, inl y) = inl y`,
`H(t, inr z) = inr (cell_outer_hequiv_aux_scale t z * z)` (stays in `1/3 < |·|`,
fixes the boundary circle, so respects `CellRel`).  Continuity on
`cellOuter γ × I`: product of the restricted quotient map with the locally
compact `I` is a quotient map (`IsQuotientMap.prodMap` / `quotientMap_prod_unitInterval`
pattern in `PolygonSurfacePiOne`). -/
lemma cell_outer_hequiv_aux_homotopy (γ : C(Circle, Y))
    (hc : Continuous (fun p : cellOuter γ ↦ cell_outer_hequiv_aux_descend γ p.1)) :
    ((cellInclOuter γ).comp ⟨fun p : cellOuter γ ↦ cell_outer_hequiv_aux_descend γ p.1, hc⟩).Homotopic
      (ContinuousMap.id (cellOuter γ)) := by
  sorry

/-- A4. Assembly (sorry-free over A4a, A4b). -/
theorem cell_outer_hequiv (γ : C(Circle, Y)) :
    ∃ e : (cellOuter γ) ≃ₕ Y, e.invFun = cellInclOuter γ := by
  have hc := cell_outer_hequiv_aux_continuous γ
  refine ⟨{ toFun := ⟨fun p : cellOuter γ ↦ cell_outer_hequiv_aux_descend γ p.1, hc⟩,
             invFun := cellInclOuter γ,
             left_inv := cell_outer_hequiv_aux_homotopy γ hc,
             right_inv := ?_ }, rfl⟩
  have : (⟨fun p : cellOuter γ ↦ cell_outer_hequiv_aux_descend γ p.1, hc⟩ : C(cellOuter γ, Y)).comp
      (cellInclOuter γ) = ContinuousMap.id Y := by
    ext y
    exact cell_outer_hequiv_aux_descend_incl γ y
  rw [this]
/-- A5. The radius-`1/2` circle, pushed into the outer piece, is freely
homotopic to `γ` (radial push to the boundary circle, where `inr z = inl (γ z)`). -/
lemma cell_overlap_loop (γ : C(Circle, Y)) :
    ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
        (cellOverlapCircle γ)).Homotopic ((cellInclOuter γ).comp γ) := by
  sorry

/-- A6. Path-connectedness of the pieces and of the cell space. -/
lemma cell_pathConnected (γ : C(Circle, Y)) [PathConnectedSpace Y]
    (hA3 : ∃ e : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≃ₕ Circle,
      e.invFun = cellOverlapCircle γ)
    (hA4 : ∃ e : (cellOuter γ) ≃ₕ Y, e.invFun = cellInclOuter γ) :
    PathConnectedSpace (cellOuter γ) ∧
      PathConnectedSpace (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ∧
      PathConnectedSpace (Cell γ) := by
  sorry

/-- A7. **van Kampen for one 2-cell.**  The inclusion `Y → Y ∪_γ D²` is onto
on π₁ with kernel the normal closure of `[γ]`.  Apply
`apm_t92J05_twoOpen_simplyConnectedRight_kernel` to the cover (A1, A2, A6) at
the overlap point `cellOverlapCircle γ 1`; transfer from the outer piece to
`Y` by A4, identify the overlap image with a conjugate of `[γ]` by A3 + A5
(a free homotopy conjugates; normal closures absorb conjugation), and move the
basepoint along any path (again a conjugation). -/
lemma cell_piOne (γ : C(Circle, Y)) [PathConnectedSpace Y] (y : Y) (h : γ 1 = y)
    (hA1 : IsOpen (cellOuter γ) ∧ IsOpen (cellInner γ) ∧
      cellOuter γ ∪ cellInner γ = Set.univ)
    (hA2 : ContractibleSpace (cellInner γ))
    (hA3 : ∃ e : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≃ₕ Circle,
      e.invFun = cellOverlapCircle γ)
    (hA4 : ∃ e : (cellOuter γ) ≃ₕ Y, e.invFun = cellInclOuter γ)
    (hA5 : ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
        (cellOverlapCircle γ)).Homotopic ((cellInclOuter γ).comp γ))
    (hA6 : PathConnectedSpace (cellOuter γ) ∧
      PathConnectedSpace (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ∧
      PathConnectedSpace (Cell γ)) :
    Function.Surjective (FundamentalGroup.map (cellIncl γ) y) ∧
      (FundamentalGroup.map (cellIncl γ) y).ker =
        Subgroup.normalClosure {loopClassAt γ y h} := by
  sorry

/-- A8. **H₁ of a 2-cell attachment.**  Integral Mayer–Vietoris
(`IntegralMV.integralMayerVietoris`, transported to the `singularHomologyFunctor`
form by `IntegralSingularHomologyComparison`) for the cover A1: `H₁(inner) = 0`,
`H₀(overlap) → H₀(outer) ⊕ H₀(inner)` injective, `H₁(overlap) ≅ H₁(Circle)` by
A3 and its image is `γ_*` by A5, `H₁(outer) ≅ H₁(Y)` by A4. -/
lemma cell_H1 (γ : C(Circle, Y)) [PathConnectedSpace Y]
    (hA1 : IsOpen (cellOuter γ) ∧ IsOpen (cellInner γ) ∧
      cellOuter γ ∪ cellInner γ = Set.univ)
    (hA2 : ContractibleSpace (cellInner γ))
    (hA3 : ∃ e : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≃ₕ Circle,
      e.invFun = cellOverlapCircle γ)
    (hA4 : ∃ e : (cellOuter γ) ≃ₕ Y, e.invFun = cellInclOuter γ)
    (hA5 : ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
        (cellOverlapCircle γ)).Homotopic ((cellInclOuter γ).comp γ)) :
    Function.Surjective (Hmap (cellIncl γ) 1).hom ∧
      LinearMap.ker (Hmap (cellIncl γ) 1).hom = LinearMap.range (Hmap γ 1).hom := by
  sorry

/-- A9. If `γ_*` is injective on `H₁`, then `H₂(Y) → H₂(Y ∪_γ D²)` is bijective
(Mayer–Vietoris at degree 2: `H₂(overlap) = 0`, connecting map lands in
`ker γ_* = 0`). -/
lemma cell_H2_of_injective (γ : C(Circle, Y))
    (hA1 : IsOpen (cellOuter γ) ∧ IsOpen (cellInner γ) ∧
      cellOuter γ ∪ cellInner γ = Set.univ)
    (hA2 : ContractibleSpace (cellInner γ))
    (hA3 : ∃ e : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≃ₕ Circle,
      e.invFun = cellOverlapCircle γ)
    (hA4 : ∃ e : (cellOuter γ) ≃ₕ Y, e.invFun = cellInclOuter γ)
    (hA5 : ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
        (cellOverlapCircle γ)).Homotopic ((cellInclOuter γ).comp γ))
    (hinj : Function.Injective (Hmap γ 1).hom) :
    Function.Bijective (Hmap (cellIncl γ) 2).hom := by
  sorry

/-- A10. If `H₂(Y) = 0` and `γ_* = 0` on `H₁`, then `H₂(Y ∪_γ D²) ≅ ℤ`
(the connecting map is an iso onto `H₁(overlap) ≅ H₁(Circle) ≅ ℤ`). -/
lemma cell_H2_of_zero (γ : C(Circle, Y))
    (hA1 : IsOpen (cellOuter γ) ∧ IsOpen (cellInner γ) ∧
      cellOuter γ ∪ cellInner γ = Set.univ)
    (hA2 : ContractibleSpace (cellInner γ))
    (hA3 : ∃ e : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≃ₕ Circle,
      e.invFun = cellOverlapCircle γ)
    (hA4 : ∃ e : (cellOuter γ) ≃ₕ Y, e.invFun = cellInclOuter γ)
    (hA5 : ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
        (cellOverlapCircle γ)).Homotopic ((cellInclOuter γ).comp γ))
    (hY2 : Limits.IsZero (H 2 Y)) (hγ : Hmap γ 1 = 0) :
    Nonempty (H 2 (Cell γ) ≅ ModuleCat.of ℤ ℤ) := by
  sorry

/-- A11. In degrees `k ≥ 3` the inclusion is an isomorphism on homology
(`H_k` and `H_{k-1}` of the overlap and `H_k` of the inner piece vanish). -/
lemma cell_H_high (γ : C(Circle, Y))
    (hA1 : IsOpen (cellOuter γ) ∧ IsOpen (cellInner γ) ∧
      cellOuter γ ∪ cellInner γ = Set.univ)
    (hA2 : ContractibleSpace (cellInner γ))
    (hA3 : ∃ e : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≃ₕ Circle,
      e.invFun = cellOverlapCircle γ)
    (hA4 : ∃ e : (cellOuter γ) ≃ₕ Y, e.invFun = cellInclOuter γ)
    (k : ℕ) (hk : 3 ≤ k) :
    Function.Bijective (Hmap (cellIncl γ) k).hom := by
  sorry

end AttachCell

/-! ## Part B: the space of t97J04 -/

abbrev P : PairingData := apm_t92J05_genusTwo_polygon_attach_specialization_aux_P

/-- The orbit-indexed wedge of four circles. -/
abbrev W := FiniteWedge (PairingOrbit P.pair)

/-- The polygon boundary loop in `W` (the word `[a₁,b₁][a₂,b₂]`). -/
def word : C(Circle, W) := PolygonSurfaceHomology.polygonBoundaryWedgeLoop P

/-- `W ∪_word D²` (the genus-two surface). -/
abbrev Sigma := Cell word

/-- The edge-4 (meridian `c`) orbit. -/
def cEdge : Fin P.edgeCount := ⟨4, by decide⟩

def cOrbit : PairingOrbit P.pair := P.orbit cEdge

/-- The meridian loop `c` in `Sigma`. -/
def cLoop : C(Circle, Sigma) :=
  (cellIncl word).comp ⟨wedgeCircle cOrbit, continuous_wedgeCircle cOrbit⟩

/-- `Sigma ∪_c D²`, the model of `X`. -/
abbrev Xc := Cell cLoop

/-- Base points: the wedge point, its images. -/
def wBase : W := PolygonSurfaceHomology.orbitWedgeBase P

def sBase : Sigma := cellIncl word wBase

def xBase : Xc := cellIncl cLoop sBase

/-- Wedge coordinates on `π₁(W)` (banked from t92J05, B8). -/
abbrev wedgeCoords :
    FundamentalGroup W wBase ≃* FreeGroup (Fin 4) :=
  apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedgeCoordinates

abbrev orbitLabel : PairingOrbit P.pair ≃ Fin 4 :=
  apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_orbitEquiv

/-- B1. **The model.**  `X ≅ Xc`, sending the octagon centre to the centre of
the first cell.  Maps: octagon point `z ↦ cellIncl cLoop (cellDisk word z)`,
meridian-disk point `z ↦ cellDisk cLoop (conj z)` (edge 4 has `P.sign = false`,
so `signedWedgeArc 4 t = wedgeCircle cOrbit (circleArc (1 - t))`: the octagon
runs `c` backwards; `edgePoint 1 0 t = circleToDisk (circleArc t)`); inverse on `W` via
`P.skeletonHomeomorphWedge.symm`.  Boundary compatibility:
`PolygonSurfaceHomology.polygonBoundaryWedgeLoop_edgePoint` (octagon edges)
and `edgePoint 1 0 t = circleToDisk (circleArc t)` (meridian). Both directions
are continuous as lifts through quotient maps (no Hausdorffness needed). -/
lemma X_homeomorph_aux_edgeCount : P.edgeCount = 8 := by
  rfl

lemma X_homeomorph_aux_cEdge_sign : P.sign cEdge = false := by
  decide

lemma X_homeomorph_aux_word_cEdge (t : Set.Icc (0 : ℝ) 1) :
    word (PolygonSurfacePiOne.edgePointCircle P.edgeCount cEdge t) =
      wedgeCircle cOrbit
        (PolygonSurfacePiOne.circleArc (PolygonSurfacePiOne.reverseIcc t)) := by
  change PolygonSurfaceHomology.polygonBoundaryWedgeLoop P
      (PolygonSurfacePiOne.edgePointCircle P.edgeCount cEdge t) = _
  rw [PolygonSurfaceHomology.polygonBoundaryWedgeLoop_edgePoint]
  exact P.signedWedgeArc_of_not_sign cEdge t X_homeomorph_aux_cEdge_sign

lemma X_homeomorph_aux_oneDisk_boundary (t : Set.Icc (0 : ℝ) 1) :
    apm_t97J04_edgePoint 1 0 t =
      circleToDisk (PolygonSurfacePiOne.circleArc t) := by
  apply Subtype.ext
  simp only [apm_t97J04_edgePoint, circleToDisk,
    PolygonSurfacePiOne.circleArc,
    PolygonSurfaceHomology.circleToPolygonDisk,
    ConstructionTargets.Surfaces.edgePoint]
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 1
  norm_num
  ring

/-- Complex conjugation on the disk (the octagon runs `c` backwards). -/
def conjDisk (z : apm_t97J04_Disk) : apm_t97J04_Disk :=
  ⟨(starRingEnd ℂ) (z : ℂ), by
    have h := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at h ⊢
    rwa [Complex.norm_conj]⟩

theorem conjDisk_conjDisk (z : apm_t97J04_Disk) : conjDisk (conjDisk z) = z := by
  apply Subtype.ext
  simp [conjDisk]

/-- The quotient map of `X`. -/
def xMk (x : apm_t97J04_Disk ⊕ apm_t97J04_Disk) : apm_t97J04_X :=
  Quotient.mk (Relation.EqvGen.setoid apm_t97J04_ComplexRel) x

/-- B1a. Forward map `X → Xc`: octagon `z ↦ cellIncl cLoop (cellDisk word z)`,
meridian disk `z ↦ cellDisk cLoop (conjDisk z)`.  Respecting `ComplexRel`:
octagon pairs `a,b,c,d` go to the same point of `W` via
`polygonBoundaryWedgeLoop_edgePoint` (the `word` relation of `Sigma`);
`meridian`: `X_homeomorph_aux_word_cEdge` + `X_homeomorph_aux_oneDisk_boundary`
(conjugation turns `circleArc t` into `circleArc (1 - t)`).  Continuous as a
lift through the coinduced topology. -/
-- BEGIN SEAT AREA
lemma X_fwd :
    ∃ f : C(apm_t97J04_X, Xc),
      (∀ z, f (xMk (.inl z)) = cellIncl cLoop (cellDisk word z)) ∧
      (∀ z, f (xMk (.inr z)) = cellDisk cLoop (conjDisk z)) := by
  sorry
-- END SEAT AREA

/-- B1b. Backward map `Xc → X`: on `Sigma = Cell word`, `W`-points go through
`P.skeletonHomeomorphWedge.symm` and the octagon quotient (`P.Rel` generated
classes are `ComplexRel` classes on `inl`), disk points `z ↦ xMk (.inl z)`; on
the `cLoop` disk, `z ↦ xMk (.inr (conjDisk z))`.  Two nested quotient lifts;
both continuous via `continuous_coinduced_dom`. -/
lemma X_bwd :
    ∃ g : C(Xc, apm_t97J04_X),
      (∀ z, g (cellIncl cLoop (cellDisk word z)) = xMk (.inl z)) ∧
      (∀ z, g (cellDisk cLoop z) = xMk (.inr (conjDisk z))) := by
  sorry

/-- B1c. Every point of `Xc` lies on one of the two disks
(`W`-points are on the `word` boundary: `polygonBoundaryWedgeLoop` is onto;
`cellIncl word (word z) = cellDisk word (circleToDisk z)` by `CellRel`). -/
lemma Xc_points (p : Xc) :
    (∃ z, p = cellIncl cLoop (cellDisk word z)) ∨ ∃ z, p = cellDisk cLoop z := by
  sorry

/-- B1. Assembly (sorry-free over B1a–c). -/
theorem X_homeomorph :
    ∃ h : apm_t97J04_X ≃ₜ Xc,
      h apm_t97J04_basepoint = cellIncl cLoop (cellDisk word 0) := by
  obtain ⟨f, hf1, hf2⟩ := X_fwd
  obtain ⟨g, hg1, hg2⟩ := X_bwd
  have hgf : ∀ x, g (f x) = x := by
    intro x
    induction x using Quotient.inductionOn with
    | h a =>
      rcases a with z | z
      · change g (f (xMk (.inl z))) = xMk (.inl z)
        rw [hf1, hg1]
      · change g (f (xMk (.inr z))) = xMk (.inr z)
        rw [hf2, hg2, conjDisk_conjDisk]
  have hfg : ∀ p, f (g p) = p := by
    intro p
    rcases Xc_points p with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · rw [hg1, hf1]
    · rw [hg2, hf2, conjDisk_conjDisk]
  refine ⟨{ toFun := f, invFun := g, left_inv := hgf, right_inv := hfg,
            continuous_toFun := f.continuous, continuous_invFun := g.continuous }, ?_⟩
  exact hf1 0
/-- B2. The word's loop class in wedge coordinates is a conjugate of the
genus-two relator or its inverse (W1, banked). -/
lemma word_loopClass_coords :
    IsConj (wedgeCoords (loopClassAt word wBase
        (PolygonSurfaceHomology.polygonBoundaryWedgeLoop_one P)))
        apm_t92J05_genusTwoRelator ∨
      IsConj (wedgeCoords (loopClassAt word wBase
        (PolygonSurfaceHomology.polygonBoundaryWedgeLoop_one P)))
        apm_t92J05_genusTwoRelator⁻¹ := by
  sorry

/-- `cLoop 1 = sBase`. -/
theorem cLoop_one : cLoop 1 = sBase := by
  change cellIncl word (wedgeCircle cOrbit 1) = cellIncl word wBase
  congr 1
  exact wedgeCircle_base_eq _ _

/-- B3. The loop class of `c` is the image of the `cOrbit` leg
(`finiteWedgeExplicitLegClassAtBase P cOrbit`, whose wedge coordinate is
`FreeGroup.of (orbitLabel cOrbit)` by the banked `..._wedge_hcoord`). -/
lemma cLoop_loopClass :
    loopClassAt cLoop sBase cLoop_one =
      FundamentalGroup.map (cellIncl word) wBase
        (wedgeCoords.symm (FreeGroup.of (orbitLabel cOrbit))) := by
  sorry

/-- B3'. Edge 4 lies in handle 1 at position 0: label `(1, false) ↦ 2`
(`orientableOrbitEquiv`, `finTwoEquiv`, `finProdFinEquiv`). -/
lemma cOrbit_label : orbitLabel cOrbit = 2 := by
  sorry

/-- B4. Two successive one-relator quotients (pure group theory). -/
lemma two_step_quotient {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (a b : G)
    (hkf : f.ker = Subgroup.normalClosure {a})
    (hkg : g.ker = Subgroup.normalClosure {f b}) :
    Nonempty (K ≃* G ⧸ Subgroup.normalClosure ({a, b} : Set G)) := by
  sorry

/-- B5. Tietze: kill `c` (generator 2) in the genus-two group; generators
`a, b, d` ↦ `0, 1, 2`.  The relator may enter up to conjugacy/inversion. -/
lemma presentation_algebra (r : FreeGroup (Fin 4))
    (hr : IsConj r apm_t92J05_genusTwoRelator ∨
      IsConj r apm_t92J05_genusTwoRelator⁻¹) :
    Nonempty (FreeGroup (Fin 4) ⧸
        Subgroup.normalClosure ({r, FreeGroup.of 2} : Set (FreeGroup (Fin 4))) ≃*
      apm_t97J04_piOne) := by
  sorry

/-- B6. Homology of the wedge: path connected, and zero in degrees `≥ 2`
(`PolygonSurfaceHomology.finiteWedgeHigherHomologyIsZero`). -/
lemma W_homology : PathConnectedSpace W ∧ ∀ k, 2 ≤ k → Limits.IsZero (H k W) := by
  sorry

/-- B7. `word_* = 0` on `H₁`: Hurewicz naturality
(`PolygonSurfaceHomology.moduleHurewicz_naturality`) sends the circle class to
the Hurewicz image of the word's loop class, a product of commutators. -/
lemma word_H1_zero : Hmap word 1 = 0 := by
  sorry

/-- B8. `c_*` is injective on `H₁`: `c = incl ∘ leg`, `incl_*` is injective on
`H₁` (A8 with `word_* = 0`), and `leg_*` has the left inverse
`finiteWedgeCollapse` (`finiteWedgeLegH1_collapse_self`). -/
lemma cLoop_H1_injective
    (hA8 : Function.Surjective (Hmap (cellIncl word) 1).hom ∧
      LinearMap.ker (Hmap (cellIncl word) 1).hom = LinearMap.range (Hmap word 1).hom)
    (hB7 : Hmap word 1 = 0) :
    Function.Injective (Hmap cLoop 1).hom := by
  sorry

/-- B9. `H₁(Xc) ≅ ℤ³`: `H₁(Xc) ≅ H₁(Sigma)/range c_*` (A8 for `cLoop`),
`H₁(Sigma) ≅ H₁(W)` (A8 for `word`, B7), and `H₁(W) ≅ (PairingOrbit → ℤ)` by the
collapse coordinates (`finiteWedgeH1CoordinateMap`), under which the `cOrbit`
leg is a basis vector. -/
lemma Xc_H1
    (hA8w : Function.Surjective (Hmap (cellIncl word) 1).hom ∧
      LinearMap.ker (Hmap (cellIncl word) 1).hom = LinearMap.range (Hmap word 1).hom)
    (hA8c : Function.Surjective (Hmap (cellIncl cLoop) 1).hom ∧
      LinearMap.ker (Hmap (cellIncl cLoop) 1).hom = LinearMap.range (Hmap cLoop 1).hom)
    (hB7 : Hmap word 1 = 0) :
    Nonempty (H 1 Xc ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) := by
  sorry

/-- B10. `H₀` of a path-connected space is `ℤ`. -/
lemma H0_of_pathConnected (S : Type) [TopologicalSpace S] [PathConnectedSpace S] :
    Nonempty (H 0 S ≅ ModuleCat.of ℤ ℤ) := by
  sorry

/-- B11. A homeomorphism induces isomorphisms on the problem's homology. -/
lemma H_of_homeomorph {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    (h : S ≃ₜ T) (k : ℕ) : Nonempty (H k S ≅ H k T) := by
  sorry


/-! ## Assembly -/

theorem cell_facts {Y : Type} [TopologicalSpace Y] (γ : C(Circle, Y)) :
    (IsOpen (cellOuter γ) ∧ IsOpen (cellInner γ) ∧
      cellOuter γ ∪ cellInner γ = Set.univ) ∧
    ContractibleSpace (cellInner γ) ∧
    (∃ e : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≃ₕ Circle,
      e.invFun = cellOverlapCircle γ) ∧
    (∃ e : (cellOuter γ) ≃ₕ Y, e.invFun = cellInclOuter γ) ∧
    ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
        (cellOverlapCircle γ)).Homotopic ((cellInclOuter γ).comp γ) :=
  ⟨cell_cover γ, cell_inner_contractible γ, cell_overlap_hequiv γ,
    cell_outer_hequiv γ, cell_overlap_loop γ⟩

theorem cell_pc {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y]
    (γ : C(Circle, Y)) : PathConnectedSpace (Cell γ) :=
  (cell_pathConnected γ (cell_overlap_hequiv γ) (cell_outer_hequiv γ)).2.2

instance : PathConnectedSpace W := W_homology.1

instance : PathConnectedSpace Sigma := cell_pc word

instance : PathConnectedSpace Xc := cell_pc cLoop

theorem Xc_piOne : Nonempty (FundamentalGroup Xc xBase ≃* apm_t97J04_piOne) := by
  obtain ⟨hA1w, hA2w, hA3w, hA4w, hA5w⟩ := cell_facts word
  obtain ⟨hA1c, hA2c, hA3c, hA4c, hA5c⟩ := cell_facts cLoop
  obtain ⟨hfs, hfk⟩ := cell_piOne word wBase
    (PolygonSurfaceHomology.polygonBoundaryWedgeLoop_one P) hA1w hA2w hA3w hA4w hA5w
    (cell_pathConnected word hA3w hA4w)
  obtain ⟨hgs, hgk⟩ := cell_piOne cLoop sBase cLoop_one hA1c hA2c hA3c hA4c hA5c
    (cell_pathConnected cLoop hA3c hA4c)
  rw [cLoop_loopClass, cOrbit_label] at hgk
  obtain ⟨e1⟩ := two_step_quotient _ _ hfs hgs _ _ hfk hgk
  let r := wedgeCoords (loopClassAt word wBase
    (PolygonSurfaceHomology.polygonBoundaryWedgeLoop_one P))
  obtain ⟨e2⟩ := presentation_algebra r word_loopClass_coords
  refine ⟨e1.trans ((QuotientGroup.congr _ _ wedgeCoords ?_).trans e2)⟩
  rw [Subgroup.map_normalClosure _ _ wedgeCoords.surjective]
  congr 1
  simp [r, Set.image_insert_eq, Set.image_singleton]

end APMT97J04

open APMT97J04 in
theorem apm_t97j04 :
    Nonempty
      (FundamentalGroup apm_t97J04_X apm_t97J04_basepoint ≃*
        apm_t97J04_piOne) ∧
    Nonempty (apm_t97J04_H 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97J04_H 1 ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    Nonempty (apm_t97J04_H 2 ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k : ℕ, 3 ≤ k → Limits.IsZero (apm_t97J04_H k) := by
  obtain ⟨h, hbase⟩ := X_homeomorph
  obtain ⟨hA1w, hA2w, hA3w, hA4w, hA5w⟩ := cell_facts word
  obtain ⟨hA1c, hA2c, hA3c, hA4c, hA5c⟩ := cell_facts cLoop
  have hA8w := cell_H1 word hA1w hA2w hA3w hA4w hA5w
  have hA8c := cell_H1 cLoop hA1c hA2c hA3c hA4c hA5c
  have hX : ∀ k, Nonempty (apm_t97J04_H k ≅ H k Xc) := fun k => H_of_homeomorph h k
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨e⟩ := Xc_piOne
    exact ⟨(ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph
      h apm_t97J04_basepoint).trans
        ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected _ xBase).trans e)⟩
  · obtain ⟨e⟩ := hX 0
    obtain ⟨f⟩ := H0_of_pathConnected Xc
    exact ⟨e ≪≫ f⟩
  · obtain ⟨e⟩ := hX 1
    obtain ⟨f⟩ := Xc_H1 hA8w hA8c word_H1_zero
    exact ⟨e ≪≫ f⟩
  · obtain ⟨e⟩ := hX 2
    have hinj := cLoop_H1_injective hA8w word_H1_zero
    have hbij := cell_H2_of_injective cLoop hA1c hA2c hA3c hA4c hA5c hinj
    obtain ⟨f⟩ := cell_H2_of_zero word hA1w hA2w hA3w hA4w hA5w
      (W_homology.2 2 le_rfl) word_H1_zero
    exact ⟨e ≪≫ (LinearEquiv.toModuleIso
      (LinearEquiv.ofBijective (Hmap (cellIncl cLoop) 2).hom hbij)).symm ≪≫ f⟩
  · intro k hk
    obtain ⟨e⟩ := hX k
    have hc := cell_H_high cLoop hA1c hA2c hA3c hA4c k hk
    have hw := cell_H_high word hA1w hA2w hA3w hA4w k hk
    have hW := W_homology.2 k (by omega)
    refine Limits.IsZero.of_iso ?_ e
    refine Limits.IsZero.of_iso ?_ (LinearEquiv.toModuleIso
      (LinearEquiv.ofBijective (Hmap (cellIncl cLoop) k).hom hc)).symm
    exact Limits.IsZero.of_iso hW (LinearEquiv.toModuleIso
      (LinearEquiv.ofBijective (Hmap (cellIncl word) k).hom hw)).symm
