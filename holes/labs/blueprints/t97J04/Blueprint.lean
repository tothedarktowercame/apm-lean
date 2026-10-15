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
lemma cell_cover_aux_circle_norm (z : Circle) :
    ‖((circleToDisk z : apm_t97J04_Disk) : ℂ)‖ = 1 := by
  exact Circle.norm_coe z

lemma cell_cover_aux_outer_invariant (gamma : C(Circle, Y))
    {x y : Y ⊕ apm_t97J04_Disk}
    (h : Relation.EqvGen (CellRel gamma) x y) :
    (x ∈ Set.range (Sum.inl : Y → Y ⊕ apm_t97J04_Disk) ∪
        Sum.inr '' {z : apm_t97J04_Disk | (1 : ℝ) / 3 < ‖(z : ℂ)‖} ↔
      y ∈ Set.range (Sum.inl : Y → Y ⊕ apm_t97J04_Disk) ∪
        Sum.inr '' {z : apm_t97J04_Disk | (1 : ℝ) / 3 < ‖(z : ℂ)‖}) := by
  induction h with
  | rel x y h =>
      cases h with
      | boundary z =>
          simp only [Set.mem_union, Set.mem_range, Set.mem_image]
          constructor
          · intro _
            right
            refine ⟨circleToDisk z, ?_, rfl⟩
            change (1 : ℝ) / 3 < ‖((circleToDisk z : apm_t97J04_Disk) : ℂ)‖
            rw [cell_cover_aux_circle_norm]
            norm_num
          · intro _
            left
            exact ⟨gamma z, rfl⟩
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma cell_cover_aux_inner_invariant (gamma : C(Circle, Y))
    {x y : Y ⊕ apm_t97J04_Disk}
    (h : Relation.EqvGen (CellRel gamma) x y) :
    (x ∈ Sum.inr '' {z : apm_t97J04_Disk | ‖(z : ℂ)‖ < (2 : ℝ) / 3} ↔
      y ∈ Sum.inr '' {z : apm_t97J04_Disk | ‖(z : ℂ)‖ < (2 : ℝ) / 3}) := by
  induction h with
  | rel x y h =>
      cases h with
      | boundary z =>
          simp only [Set.mem_image]
          constructor
          · rintro ⟨w, _, hw⟩
            cases hw
          · rintro ⟨w, hw, hzw⟩
            have : w = circleToDisk z := Sum.inr.inj hzw
            subst w
            change ‖((circleToDisk z : apm_t97J04_Disk) : ℂ)‖ < (2 : ℝ) / 3 at hw
            rw [cell_cover_aux_circle_norm] at hw
            norm_num at hw
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma cell_cover (γ : C(Circle, Y)) :
    IsOpen (cellOuter γ) ∧ IsOpen (cellInner γ) ∧
      cellOuter γ ∪ cellInner γ = Set.univ := by
  let Uo : Set (Y ⊕ apm_t97J04_Disk) :=
    Set.range (Sum.inl : Y → Y ⊕ apm_t97J04_Disk) ∪
      Sum.inr '' {z : apm_t97J04_Disk | (1 : ℝ) / 3 < ‖(z : ℂ)‖}
  let Ui : Set (Y ⊕ apm_t97J04_Disk) :=
    Sum.inr '' {z : apm_t97J04_Disk | ‖(z : ℂ)‖ < (2 : ℝ) / 3}
  have hpre_o : cellMk γ ⁻¹' (cellMk γ '' Uo) = Uo := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (cell_cover_aux_outer_invariant γ (Quotient.exact hxy)).mp hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hpre_i : cellMk γ ⁻¹' (cellMk γ '' Ui) = Ui := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (cell_cover_aux_inner_invariant γ (Quotient.exact hxy)).mp hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hopen_o : IsOpen Uo := by
    exact IsOpen.union isOpen_range_inl
      (isOpenMap_inr _ (isOpen_lt continuous_const
        (continuous_norm.comp continuous_subtype_val)))
  have hopen_i : IsOpen Ui := by
    exact isOpenMap_inr _ (isOpen_lt
      (continuous_norm.comp continuous_subtype_val) continuous_const)
  constructor
  · change IsOpen (cellMk γ '' Uo)
    rw [isOpen_coinduced]
    have hp : (fun x : Y ⊕ apm_t97J04_Disk ↦
        Quotient.mk (Relation.EqvGen.setoid (CellRel γ)) x) ⁻¹'
          (cellMk γ '' Uo) = Uo := by
      simpa only [cellMk] using hpre_o
    exact hp.symm ▸ hopen_o
  constructor
  · change IsOpen (cellMk γ '' Ui)
    rw [isOpen_coinduced]
    have hp : (fun x : Y ⊕ apm_t97J04_Disk ↦
        Quotient.mk (Relation.EqvGen.setoid (CellRel γ)) x) ⁻¹'
          (cellMk γ '' Ui) = Ui := by
      simpa only [cellMk] using hpre_i
    exact hp.symm ▸ hopen_i
  · apply Set.eq_univ_of_forall
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    cases x with
    | inl y =>
        left
        exact ⟨Sum.inl y, Or.inl ⟨y, rfl⟩, rfl⟩
    | inr z =>
        by_cases hz : (1 : ℝ) / 3 < ‖(z : ℂ)‖
        · left
          exact ⟨Sum.inr z, Or.inr ⟨z, hz, rfl⟩, rfl⟩
        · right
          refine ⟨Sum.inr z, ⟨z, ?_, rfl⟩, rfl⟩
          change ‖(z : ℂ)‖ < (2 : ℝ) / 3
          linarith

/-- A2. The inner piece is homeomorphic to the open ball `|z| < 2/3`. -/
noncomputable def cell_inner_contractible_aux_diskOfBall
    (z : Metric.ball (0 : ℂ) ((2 : ℝ) / 3)) : apm_t97J04_Disk :=
  ⟨z, by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hz : ‖(z : ℂ)‖ < (2 : ℝ) / 3 := by
      simpa only [Metric.mem_ball, dist_zero_right] using z.2
    linarith⟩

lemma cell_inner_contractible_aux_eqv (gamma : C(Circle, Y))
    {z w : apm_t97J04_Disk}
    (hz : ‖(z : ℂ)‖ < (2 : ℝ) / 3)
    (h : Relation.EqvGen (CellRel gamma) (Sum.inr z) (Sum.inr w)) : z = w := by
  let P := fun x : Y ⊕ apm_t97J04_Disk => x = Sum.inr z
  have hrel : ∀ a b, CellRel gamma a b → (P a ↔ P b) := by
    intro a b hab
    cases hab with
    | boundary u =>
      constructor
      · intro bad
        cases bad
      · intro bad
        have he : circleToDisk u = z := Sum.inr.inj bad
        have hn := congrArg (fun v : apm_t97J04_Disk => ‖(v : ℂ)‖) he
        change ‖((circleToDisk u : apm_t97J04_Disk) : ℂ)‖ = ‖(z : ℂ)‖ at hn
        rw [cell_cover_aux_circle_norm] at hn
        linarith
  have hinv : ∀ a b, Relation.EqvGen (CellRel gamma) a b → (P a ↔ P b) := by
    intro a b hab
    induction hab with
    | rel a b hab => exact hrel a b hab
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact Sum.inr.inj ((hinv _ _ h).mp rfl).symm

noncomputable def cell_inner_contractible_aux_g (gamma : C(Circle, Y))
    (z : Metric.ball (0 : ℂ) ((2 : ℝ) / 3)) : cellInner gamma :=
  ⟨cellMk gamma (.inr (cell_inner_contractible_aux_diskOfBall z)),
    ⟨.inr (cell_inner_contractible_aux_diskOfBall z),
      ⟨cell_inner_contractible_aux_diskOfBall z, by
        simpa only [cell_inner_contractible_aux_diskOfBall,
          Metric.mem_ball, dist_zero_right] using z.2, rfl⟩, rfl⟩⟩

lemma cell_inner_contractible_aux_g_cont_bij (gamma : C(Circle, Y)) :
    Continuous (cell_inner_contractible_aux_g gamma) ∧
      Function.Bijective (cell_inner_contractible_aux_g gamma) := by
  constructor
  · apply Continuous.subtype_mk
    exact (continuous_cellMk gamma).comp
      (continuous_inr.comp (Continuous.subtype_mk continuous_subtype_val _))
  constructor
  · intro z w h
    have he := Quotient.exact (congrArg Subtype.val h)
    have hi := cell_inner_contractible_aux_eqv gamma
      (by simpa only [cell_inner_contractible_aux_diskOfBall,
        Metric.mem_ball, dist_zero_right] using z.2) he
    apply Subtype.ext
    exact congrArg (fun x : apm_t97J04_Disk => (x : ℂ)) hi
  · rintro ⟨q, x, ⟨z, hz, rfl⟩, rfl⟩
    let w : Metric.ball (0 : ℂ) ((2 : ℝ) / 3) :=
      ⟨z, by simpa [Metric.mem_ball, dist_zero_right] using hz⟩
    refine ⟨w, Subtype.ext ?_⟩
    rfl

lemma cell_inner_contractible_aux_g_open (gamma : C(Circle, Y)) :
    IsOpenMap (cell_inner_contractible_aux_g gamma) := by
  intro U hU
  let d := cell_inner_contractible_aux_diskOfBall
  let F : Metric.ball (0 : ℂ) ((2 : ℝ) / 3) →
      Y ⊕ apm_t97J04_Disk := fun z => Sum.inr (d z)
  have hopenC : IsOpen
      ((fun z : Metric.ball (0 : ℂ) ((2 : ℝ) / 3) => (z : ℂ)) '' U) :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal.isOpenMap U hU
  have hopenD : IsOpen (d '' U) := by
    have heq : d '' U = Subtype.val ⁻¹'
        ((fun z : Metric.ball (0 : ℂ) ((2 : ℝ) / 3) => (z : ℂ)) '' U) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, rfl⟩
      · rintro ⟨w, hw, he⟩
        exact ⟨w, hw, Subtype.ext he⟩
    rw [heq]
    exact hopenC.preimage continuous_subtype_val
  have hopenF : IsOpen (F '' U) := by
    rw [isOpen_sum_iff]
    constructor
    · convert (isOpen_empty : IsOpen (∅ : Set Y)) using 1
      ext x
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
      rintro ⟨z, -, h⟩
      cases h
    · have heq : Sum.inr ⁻¹' (F '' U) = d '' U := by
        ext z
        constructor
        · rintro ⟨w, hw, he⟩
          exact ⟨w, hw, Sum.inr.inj he⟩
        · rintro ⟨w, hw, rfl⟩
          exact ⟨w, hw, rfl⟩
      rw [heq]
      exact hopenD
  have hsat : (cellMk gamma) ⁻¹' (cellMk gamma '' (F '' U)) = F '' U := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hzU, rfl⟩, hxy⟩
      have hr := Quotient.exact hxy
      have hz : ‖(d z : ℂ)‖ < (2 : ℝ) / 3 := by
        simpa only [d, cell_inner_contractible_aux_diskOfBall,
          Metric.mem_ball, dist_zero_right] using z.2
      have he : x = F z := by
        let P := fun v : Y ⊕ apm_t97J04_Disk => v = F z
        have hrel : ∀ a b, CellRel gamma a b → (P a ↔ P b) := by
          intro a b hab
          cases hab with
          | boundary u =>
            constructor
            · intro bad; cases bad
            · intro bad
              have hd : circleToDisk u = d z := Sum.inr.inj bad
              have hn := congrArg (fun v : apm_t97J04_Disk => ‖(v : ℂ)‖) hd
              change ‖((circleToDisk u : apm_t97J04_Disk) : ℂ)‖ = ‖(d z : ℂ)‖ at hn
              rw [cell_cover_aux_circle_norm] at hn
              linarith
        have hinv : ∀ a b, Relation.EqvGen (CellRel gamma) a b → (P a ↔ P b) := by
          intro a b hab
          induction hab with
          | rel a b hab => exact hrel a b hab
          | refl => exact Iff.rfl
          | symm _ _ _ ih => exact ih.symm
          | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
        exact (hinv _ _ hr).mp rfl
      exact ⟨z, hzU, he.symm⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨F z, ⟨z, hz, rfl⟩, rfl⟩
  have hquot : IsOpen (cellMk gamma '' (F '' U) : Set (Cell gamma)) := by
    rw [isOpen_coinduced]
    change IsOpen ((cellMk gamma) ⁻¹' (cellMk gamma '' (F '' U)))
    rw [hsat]
    exact hopenF
  have heq : cell_inner_contractible_aux_g gamma '' U =
      Subtype.val ⁻¹' (cellMk gamma '' (F '' U) : Set (Cell gamma)) := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨F z, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨z, hz, hx⟩, hxq⟩
      refine ⟨z, hz, Subtype.ext ?_⟩
      exact (congrArg (cellMk gamma) hx).trans hxq
  rw [heq]
  exact hquot.preimage continuous_subtype_val

noncomputable def cell_inner_contractible_aux_homeomorph (gamma : C(Circle, Y)) :
    Metric.ball (0 : ℂ) ((2 : ℝ) / 3) ≃ₜ cellInner gamma := by
  obtain ⟨hc, hb⟩ := cell_inner_contractible_aux_g_cont_bij gamma
  exact (Equiv.ofBijective _ hb).toHomeomorphOfContinuousOpen hc
    (cell_inner_contractible_aux_g_open gamma)

lemma cell_inner_contractible (γ : C(Circle, Y)) :
    ContractibleSpace (cellInner γ) := by
  letI : ContractibleSpace (Metric.ball (0 : ℂ) ((2 : ℝ) / 3)) :=
    Metric.contractibleSpace_ball (by norm_num)
  exact (cell_inner_contractible_aux_homeomorph γ).symm.contractibleSpace

/-- The open annulus `1/3 < |z| < 2/3`. -/
abbrev Annulus13 := {z : ℂ // (1 : ℝ) / 3 < ‖z‖ ∧ ‖z‖ < (2 : ℝ) / 3}

/-- A3a. `CellRel` only relates disk points on the boundary circle: two disk
points with one of norm `< 1` are related only if equal (cf. the saturation
argument in `cell_cover`). -/
lemma cell_overlap_hequiv_aux_eq_of_eqvGen_aux_interior
    (gamma : C(Circle, Y)) {x y : Y ⊕ apm_t97J04_Disk}
    (h : Relation.EqvGen (CellRel gamma) x y)
    (z : apm_t97J04_Disk) (hz : ‖(z : ℂ)‖ < 1) :
    (x = .inr z ↔ y = .inr z) := by
  induction h with
  | rel x y h =>
      cases h with
      | boundary u =>
          constructor
          · intro hx
            cases hx
          · intro hy
            have huz : circleToDisk u = z := Sum.inr.inj hy
            subst z
            rw [cell_cover_aux_circle_norm] at hz
            linarith
  | refl x => exact Iff.rfl
  | symm x y h ih => exact ih.symm
  | trans x y u hxy hyu ih₁ ih₂ => exact ih₁.trans ih₂

lemma cell_overlap_hequiv_aux_eq_of_eqvGen
    (γ : C(Circle, Y)) {z w : apm_t97J04_Disk}
    (h : Relation.EqvGen (CellRel γ) (.inr z) (.inr w))
    (hz : ‖(z : ℂ)‖ < 1) : z = w := by
  have hw : (Sum.inr w : Y ⊕ apm_t97J04_Disk) = .inr z :=
    (cell_overlap_hequiv_aux_eq_of_eqvGen_aux_interior γ h z hz).mp rfl
  exact (Sum.inr.inj hw).symm

/-- A3b. The overlap is homeomorphic to the literal annulus, sending
`cellMk γ (.inr z) ↦ z` (A3a gives injectivity; openness of `cellMk` on the
saturated open set `inr '' {1/3 < |z| < 2/3}` gives continuity of the inverse). -/
noncomputable def cell_overlap_hequiv_aux_homeomorph_aux_disk
    (z : Annulus13) : apm_t97J04_Disk :=
  ⟨z, by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans (le_of_lt z.2.2) (by norm_num)⟩

noncomputable def cell_overlap_hequiv_aux_homeomorph_aux_g
    (γ : C(Circle, Y)) (z : Annulus13) :
    (cellOuter γ ∩ cellInner γ : Set (Cell γ)) :=
  ⟨cellMk γ (.inr (cell_overlap_hequiv_aux_homeomorph_aux_disk z)),
    ⟨⟨.inr (cell_overlap_hequiv_aux_homeomorph_aux_disk z),
        Or.inr ⟨_, z.2.1, rfl⟩, rfl⟩,
      ⟨.inr (cell_overlap_hequiv_aux_homeomorph_aux_disk z),
        ⟨_, z.2.2, rfl⟩, rfl⟩⟩⟩

lemma cell_overlap_hequiv_aux_homeomorph_aux_cont_bij (γ : C(Circle, Y))
    (heq : ∀ {z w : apm_t97J04_Disk}, Relation.EqvGen (CellRel γ) (.inr z) (.inr w) →
      ‖(z : ℂ)‖ < 1 → z = w) :
    Continuous (cell_overlap_hequiv_aux_homeomorph_aux_g γ) ∧
      Function.Bijective (cell_overlap_hequiv_aux_homeomorph_aux_g γ) := by
  constructor
  · apply Continuous.subtype_mk
    exact (continuous_cellMk γ).comp
      (continuous_inr.comp (Continuous.subtype_mk continuous_subtype_val _))
  constructor
  · intro z w h
    have hr := Quotient.exact (congrArg Subtype.val h)
    have hd := heq hr (lt_trans z.2.2 (by norm_num))
    apply Subtype.ext
    exact congrArg (fun x : apm_t97J04_Disk ↦ (x : ℂ)) hd
  · rintro ⟨q, ho, hi⟩
    rcases hi with ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rcases ho with ⟨x, hx, hqx⟩
    have hr := Quotient.exact hqx
    have hzouter := (cell_cover_aux_outer_invariant γ hr).mp hx
    have hzlow : (1 : ℝ) / 3 < ‖(z : ℂ)‖ := by
      rcases hzouter with (⟨y, hy⟩ | ⟨w, hw, he⟩)
      · cases hy
      · exact Sum.inr.inj he ▸ hw
    let a : Annulus13 := ⟨(z : ℂ), hzlow, hz⟩
    refine ⟨a, Subtype.ext ?_⟩
    rfl

lemma cell_overlap_hequiv_aux_homeomorph_aux_open (γ : C(Circle, Y))
    (heq : ∀ {z w : apm_t97J04_Disk}, Relation.EqvGen (CellRel γ) (.inr z) (.inr w) →
      ‖(z : ℂ)‖ < 1 → z = w) :
    IsOpenMap (cell_overlap_hequiv_aux_homeomorph_aux_g γ) := by
  intro U hU
  let d := cell_overlap_hequiv_aux_homeomorph_aux_disk
  let F : Annulus13 → Y ⊕ apm_t97J04_Disk := fun z => .inr (d z)
  have hopenC : IsOpen ((fun z : Annulus13 => (z : ℂ)) '' U) := by
    have ha : IsOpen {z : ℂ | (1 : ℝ) / 3 < ‖z‖ ∧ ‖z‖ < (2 : ℝ) / 3} :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    exact ha.isOpenEmbedding_subtypeVal.isOpenMap U hU
  have hopenD : IsOpen (d '' U) := by
    have he : d '' U = Subtype.val ⁻¹'
        ((fun z : Annulus13 => (z : ℂ)) '' U) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, rfl⟩
      · rintro ⟨w, hw, e⟩
        exact ⟨w, hw, Subtype.ext e⟩
    rw [he]
    exact hopenC.preimage continuous_subtype_val
  have hopenF : IsOpen (F '' U) := by
    rw [isOpen_sum_iff]
    constructor
    · have he : Sum.inl ⁻¹' (F '' U) = (∅ : Set Y) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨z, -, bad⟩
        cases bad
      rw [he]
      exact isOpen_empty
    · have he : Sum.inr ⁻¹' (F '' U) = d '' U := by
        ext z
        constructor
        · rintro ⟨w, hw, e⟩
          exact ⟨w, hw, Sum.inr.inj e⟩
        · rintro ⟨w, hw, rfl⟩
          exact ⟨w, hw, rfl⟩
      rw [he]
      exact hopenD
  have hsat : cellMk γ ⁻¹' (cellMk γ '' (F '' U)) = F '' U := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, h⟩
      have hr := Quotient.exact h
      have hi := (cell_cover_aux_inner_invariant γ hr).mp
        ⟨d z, z.2.2, rfl⟩
      rcases hi with ⟨w, hw, rfl⟩
      have hd := heq hr (lt_trans z.2.2 (by norm_num))
      exact ⟨z, hz, congrArg Sum.inr hd⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨F z, ⟨z, hz, rfl⟩, rfl⟩
  have hquot : IsOpen (cellMk γ '' (F '' U) : Set (Cell γ)) := by
    rw [isOpen_coinduced]
    change IsOpen (cellMk γ ⁻¹' (cellMk γ '' (F '' U)))
    rw [hsat]
    exact hopenF
  have himage : cell_overlap_hequiv_aux_homeomorph_aux_g γ '' U =
      Subtype.val ⁻¹' (cellMk γ '' (F '' U) : Set (Cell γ)) := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨F z, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, hz, e⟩, eq⟩
      refine ⟨z, hz, Subtype.ext ?_⟩
      exact (congrArg (cellMk γ) e).trans eq
  rw [himage]
  exact hquot.preimage continuous_subtype_val

lemma cell_overlap_hequiv_aux_homeomorph (γ : C(Circle, Y))
    (heq : ∀ {z w : apm_t97J04_Disk}, Relation.EqvGen (CellRel γ) (.inr z) (.inr w) →
      ‖(z : ℂ)‖ < 1 → z = w) :
    ∃ h : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≃ₜ Annulus13,
      ∀ z : Circle, ((h (cellOverlapCircle γ z) : Annulus13) : ℂ) = (z : ℂ) / 2 := by
  obtain ⟨hc, hb⟩ := cell_overlap_hequiv_aux_homeomorph_aux_cont_bij γ heq
  let e : Annulus13 ≃ₜ (cellOuter γ ∩ cellInner γ : Set (Cell γ)) :=
    (Equiv.ofBijective _ hb).toHomeomorphOfContinuousOpen hc
      (cell_overlap_hequiv_aux_homeomorph_aux_open γ heq)
  refine ⟨e.symm, ?_⟩
  intro z
  let a : Annulus13 := ⟨(z : ℂ) / 2, by
    constructor <;> rw [norm_div, Circle.norm_coe] <;> norm_num⟩
  have ha : e.symm (cellOverlapCircle γ z) = a := by
    rw [Homeomorph.symm_apply_eq]
    rfl
  exact congrArg (fun w : Annulus13 => (w : ℂ)) ha

/-- A3c. The annulus deformation retracts radially onto the radius-`1/2`
circle: `Annulus13 ≃ₕ Circle`, `w ↦ w / |w|`, inverse `z ↦ z / 2`. -/
def cell_overlap_hequiv_aux_annulus_half : C(Circle, Annulus13) where
  toFun z := ⟨(z : ℂ) / 2, by
    rw [norm_div, Circle.norm_coe]
    constructor <;> norm_num⟩
  continuous_toFun := by
    exact (continuous_subtype_val.div_const 2).subtype_mk _

def cell_overlap_hequiv_aux_annulus_radial : C(Annulus13, Circle) where
  toFun z := ⟨((‖(z : ℂ)‖⁻¹ : ℝ) : ℂ) * (z : ℂ), by
    show ((‖(z : ℂ)‖⁻¹ : ℝ) : ℂ) * (z : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    rw [Metric.mem_sphere, dist_zero_right, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (ne_of_gt (lt_trans (by norm_num) z.2.1))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hn : Continuous (fun z : Annulus13 => ‖(z : ℂ)‖) :=
      continuous_norm.comp continuous_subtype_val
    have hz : ∀ z : Annulus13, ‖(z : ℂ)‖ ≠ 0 := fun z =>
      ne_of_gt (lt_trans (by norm_num) z.2.1)
    exact (Complex.continuous_ofReal.comp (hn.inv₀ hz)).mul continuous_subtype_val

lemma cell_overlap_hequiv_aux_annulus_radial_half (z : Circle) :
    cell_overlap_hequiv_aux_annulus_radial
        (cell_overlap_hequiv_aux_annulus_half z) = z := by
  apply Subtype.ext
  dsimp [cell_overlap_hequiv_aux_annulus_radial,
    cell_overlap_hequiv_aux_annulus_half]
  change ((‖(z : ℂ) / 2‖⁻¹ : ℝ) : ℂ) * ((z : ℂ) / 2) = (z : ℂ)
  rw [norm_div, Circle.norm_coe]
  norm_num
  ring

def cell_overlap_hequiv_aux_annulus_homotopy : ContinuousMap.Homotopy
    (cell_overlap_hequiv_aux_annulus_half.comp
      cell_overlap_hequiv_aux_annulus_radial)
    (ContinuousMap.id Annulus13) where
  toFun tz := by
    let t : ℝ := tz.1
    let z : ℂ := tz.2
    let a : ℝ := (1 - t) * (1 / (2 * ‖z‖)) + t
    refine ⟨(a : ℂ) * z, ?_⟩
    have ht0 : 0 ≤ t := tz.1.2.1
    have ht1 : t ≤ 1 := tz.1.2.2
    have hz0 : 0 < ‖z‖ := lt_trans (by norm_num) tz.2.2.1
    have ha0 : 0 ≤ a := by
      dsimp [a]
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr ht1)
          (one_div_nonneg.mpr (mul_nonneg (by norm_num) hz0.le))) ht0
    have hamul : a * ‖z‖ = (1 - t) / 2 + t * ‖z‖ := by
      dsimp [a]
      field_simp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0, hamul]
    constructor
    · have hzlow := tz.2.2.1
      by_cases ht : t = 0
      · norm_num [ht]
      · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
        nlinarith
    · have hzhigh := tz.2.2.2
      by_cases ht : t = 0
      · norm_num [ht]
      · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
        nlinarith
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hn : Continuous (fun tz : unitInterval × Annulus13 => ‖(tz.2 : ℂ)‖) :=
      continuous_norm.comp (continuous_subtype_val.comp continuous_snd)
    have hne : ∀ tz : unitInterval × Annulus13, 2 * ‖(tz.2 : ℂ)‖ ≠ 0 := by
      intro tz
      exact mul_ne_zero (by norm_num)
        (ne_of_gt (lt_trans (by norm_num) tz.2.2.1))
    have ht : Continuous (fun tz : unitInterval × Annulus13 => (tz.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hz : Continuous (fun tz : unitInterval × Annulus13 => (tz.2 : ℂ)) :=
      continuous_subtype_val.comp continuous_snd
    exact (Complex.continuous_ofReal.comp
      (((continuous_const.sub ht).mul
        (continuous_const.div (continuous_const.mul hn) hne)).add ht)).mul hz
  map_zero_left z := by
    apply Subtype.ext
    dsimp [cell_overlap_hequiv_aux_annulus_half,
      cell_overlap_hequiv_aux_annulus_radial]
    change (((1 - (0 : ℝ)) * (1 / (2 * ‖(z : ℂ)‖)) + 0 : ℝ) : ℂ) *
      (z : ℂ) = ((‖(z : ℂ)‖⁻¹ : ℝ) : ℂ) * (z : ℂ) / 2
    push_cast
    ring
  map_one_left z := by
    apply Subtype.ext
    simp

lemma cell_overlap_hequiv_aux_annulus :
    ∃ e : Annulus13 ≃ₕ Circle, ∀ z : Circle, ((e.invFun z : Annulus13) : ℂ) = (z : ℂ) / 2 := by
  let e : Annulus13 ≃ₕ Circle :=
    { toFun := cell_overlap_hequiv_aux_annulus_radial
      invFun := cell_overlap_hequiv_aux_annulus_half
      left_inv := ⟨cell_overlap_hequiv_aux_annulus_homotopy⟩
      right_inv := by
        rw [show cell_overlap_hequiv_aux_annulus_radial.comp
            cell_overlap_hequiv_aux_annulus_half = ContinuousMap.id Circle by
          apply ContinuousMap.ext
          exact cell_overlap_hequiv_aux_annulus_radial_half] }
  exact ⟨e, fun z => rfl⟩

/-- A3. Assembly (sorry-free over A3a–c). -/
theorem cell_overlap_hequiv (γ : C(Circle, Y)) :
    ∃ e : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≃ₕ Circle,
      e.invFun = cellOverlapCircle γ := by
  obtain ⟨h, hh⟩ := cell_overlap_hequiv_aux_homeomorph γ
    (fun hzw hz => cell_overlap_hequiv_aux_eq_of_eqvGen γ hzw hz)
  obtain ⟨e, he⟩ := cell_overlap_hequiv_aux_annulus
  refine ⟨h.toHomotopyEquiv.trans e, ?_⟩
  ext1 z
  change h.symm (e.invFun z) = cellOverlapCircle γ z
  rw [Homeomorph.symm_apply_eq]
  apply Subtype.ext
  rw [hh, he]

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
lemma cell_outer_hequiv_aux_continuous_aux_mem
    (γ : C(Circle, Y)) (x : Y ⊕ apm_t97J04_Disk) :
    cellMk γ x ∈ cellOuter γ ↔
      x ∈ (Set.range (Sum.inl : Y → Y ⊕ apm_t97J04_Disk) ∪
        Sum.inr '' {z : apm_t97J04_Disk | (1 : ℝ) / 3 < ‖(z : ℂ)‖}) := by
  let P : Y ⊕ apm_t97J04_Disk → Prop := fun x =>
    x ∈ (Set.range (Sum.inl : Y → Y ⊕ apm_t97J04_Disk) ∪
      Sum.inr '' {z : apm_t97J04_Disk | (1 : ℝ) / 3 < ‖(z : ℂ)‖})
  have hP : ∀ {a b}, Relation.EqvGen (CellRel γ) a b → (P a ↔ P b) := by
    intro a b h
    induction h with
    | rel a b h =>
        cases h with
        | boundary z =>
            simp [P, circleToDisk, PolygonSurfaceHomology.circleToPolygonDisk,
              Circle.norm_coe]
            norm_num
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  constructor
  · rintro ⟨y, hy, heq⟩
    change Quotient.mk _ y = Quotient.mk _ x at heq
    have hrel : Relation.EqvGen (CellRel γ) y x := Quotient.exact heq
    exact (hP hrel).mp hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma cell_outer_hequiv_aux_continuous_aux_open (γ : C(Circle, Y)) :
    IsOpen (cellOuter γ) := by
  have hq : Topology.IsQuotientMap (cellMk γ) := ⟨Quotient.mk_surjective, rfl⟩
  rw [← hq.isOpen_preimage]
  rw [show (cellMk γ) ⁻¹' cellOuter γ =
      (Set.range (Sum.inl : Y → Y ⊕ apm_t97J04_Disk) ∪
        Sum.inr '' {z : apm_t97J04_Disk | (1 : ℝ) / 3 < ‖(z : ℂ)‖}) by
    ext x
    exact cell_outer_hequiv_aux_continuous_aux_mem γ x]
  apply IsOpen.union
  · exact isOpen_range_inl
  · exact isOpenMap_inr _
      (isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val))

lemma cell_outer_hequiv_aux_continuous_aux_radial {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt cell_outer_hequiv_aux_radial z := by
  apply (tendsto_subtype_rng).2
  rw [show ((cell_outer_hequiv_aux_radial z : Circle) : ℂ) =
      z / (‖z‖ : ℂ) by simp [cell_outer_hequiv_aux_radial, hz]]
  refine Filter.Tendsto.congr' ?_ ((continuousAt_id.div
    (Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt)
    (by
      change ((‖z‖ : ℝ) : ℂ) ≠ 0
      exact_mod_cast norm_ne_zero_iff.mpr hz)).tendsto)
  filter_upwards [eventually_ne_nhds hz] with w hw
  simp [cell_outer_hequiv_aux_radial, hw]

lemma cell_outer_hequiv_aux_continuous_aux_raw_at (γ : C(Circle, Y))
    (x : Y ⊕ apm_t97J04_Disk)
    (hx : x ∈ (Set.range (Sum.inl : Y → Y ⊕ apm_t97J04_Disk) ∪
      Sum.inr '' {z : apm_t97J04_Disk | (1 : ℝ) / 3 < ‖(z : ℂ)‖})) :
    ContinuousAt (cell_outer_hequiv_aux_raw γ) x := by
  cases x with
  | inl y =>
      rw [ContinuousAt, nhds_inl]
      simpa [cell_outer_hequiv_aux_raw] using continuousAt_id.tendsto
  | inr z =>
      have hzpos : (0 : ℝ) < ‖(z : ℂ)‖ := by
        rcases hx with (⟨y, h⟩ | ⟨w, hw, h⟩)
        · cases h
        · injection h with hzw
          subst w
          norm_num at hw ⊢
          intro hz
          simp [hz] at hw
          norm_num at hw
      have hz : (z : ℂ) ≠ 0 := norm_pos_iff.mp hzpos
      rw [ContinuousAt, nhds_inr]
      change Filter.Tendsto (fun z : apm_t97J04_Disk =>
        γ (cell_outer_hequiv_aux_radial (z : ℂ))) (nhds z) _
      exact
        (γ.continuous.continuousAt.comp
          ((cell_outer_hequiv_aux_continuous_aux_radial hz).comp
            continuousAt_subtype_val)).tendsto

lemma cell_outer_hequiv_aux_continuous (γ : C(Circle, Y)) :
    Continuous (fun p : cellOuter γ ↦ cell_outer_hequiv_aux_descend γ p.1) := by
  have hq : Topology.IsQuotientMap (cellMk γ) := ⟨Quotient.mk_surjective, rfl⟩
  have hqr := hq.restrictPreimage_isOpen
    (cell_outer_hequiv_aux_continuous_aux_open γ)
  rw [hqr.continuous_iff]
  rw [continuous_iff_continuousAt]
  intro x
  change ContinuousAt
    (fun x : (cellMk γ) ⁻¹' cellOuter γ => cell_outer_hequiv_aux_raw γ x.1) x
  apply (cell_outer_hequiv_aux_continuous_aux_raw_at γ x.1
    ((cell_outer_hequiv_aux_continuous_aux_mem γ x.1).mp x.2)).comp
    continuousAt_subtype_val

/-- A4b. Radial homotopy from `cellInclOuter γ ∘ retraction` to the identity
of the outer piece: `H(t, inl y) = inl y`,
`H(t, inr z) = inr (cell_outer_hequiv_aux_scale t z * z)` (stays in `1/3 < |·|`,
fixes the boundary circle, so respects `CellRel`).  Continuity on
`cellOuter γ × I`: product of the restricted quotient map with the locally
compact `I` is a quotient map (`IsQuotientMap.prodMap` / `quotientMap_prod_unitInterval`
pattern in `PolygonSurfacePiOne`). -/
def cell_outer_hequiv_aux_homotopy_aux_raw (γ : C(Circle, Y))
    (p : unitInterval × (cellMk γ) ⁻¹' cellOuter γ) :
    Y ⊕ apm_t97J04_Disk :=
  match hx : p.2.1 with
  | .inl y => .inl y
  | .inr z => .inr ⟨
      (cell_outer_hequiv_aux_scale p.1 (z : ℂ) : ℂ) * z,
      by
        rw [Metric.mem_closedBall, dist_zero_right]
        apply cell_outer_hequiv_aux_scale_norm
        · have hm := (cell_outer_hequiv_aux_continuous_aux_mem γ p.2.1).mp p.2.2
          rw [hx] at hm
          rcases hm with (⟨_, h⟩ | ⟨w, hw, h⟩)
          · cases h
          · have : w = z := Sum.inr.inj h
            subst w
            intro hz
            change (1 : ℝ) / 3 < ‖(z : ℂ)‖ at hw
            rw [hz, norm_zero] at hw
            norm_num at hw
        · have hz := z.property
          rw [Metric.mem_closedBall, dist_zero_right] at hz
          exact hz⟩

lemma cell_outer_hequiv_aux_homotopy_aux_raw_mem (γ : C(Circle, Y))
    (p : unitInterval × (cellMk γ) ⁻¹' cellOuter γ) :
    cellMk γ (cell_outer_hequiv_aux_homotopy_aux_raw γ p) ∈ cellOuter γ := by
  rcases p with ⟨t, ⟨x, hx⟩⟩
  cases x with
  | inl y =>
      exact ⟨.inl y, Or.inl ⟨y, rfl⟩, rfl⟩
  | inr z =>
      have hm := (cell_outer_hequiv_aux_continuous_aux_mem γ (.inr z)).mp hx
      have hz : (1 : ℝ) / 3 < ‖(z : ℂ)‖ := by
        rcases hm with (⟨_, h⟩ | ⟨w, hw, h⟩)
        · cases h
        · exact Sum.inr.inj h ▸ hw
      have hz0 : (z : ℂ) ≠ 0 := by
        intro h
        rw [h, norm_zero] at hz
        norm_num at hz
      refine ⟨.inr ⟨_, by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact cell_outer_hequiv_aux_scale_norm t _ hz0 (by
            have h := z.property
            rw [Metric.mem_closedBall, dist_zero_right] at h
            exact h)⟩,
        Or.inr ⟨_, ?_, rfl⟩, rfl⟩
      change (1 : ℝ) / 3 < ‖(cell_outer_hequiv_aux_scale t (z : ℂ) : ℂ) * z‖
      rw [norm_mul]
      have hn : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr hz0
      have hs : 0 ≤ cell_outer_hequiv_aux_scale t (z : ℂ) := by
        dsimp [cell_outer_hequiv_aux_scale]
        exact add_nonneg t.2.1 (div_nonneg (sub_nonneg.mpr t.2.2) hn.le)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
      dsimp [cell_outer_hequiv_aux_scale]
      rw [add_mul, div_mul_cancel₀ _ hn.ne']
      have hzle : ‖(z : ℂ)‖ ≤ 1 := by
        have h := z.property
        rw [Metric.mem_closedBall, dist_zero_right] at h
        exact h
      nlinarith [t.2.1, t.2.2]

lemma cell_outer_hequiv_aux_homotopy_aux_raw_continuous (γ : C(Circle, Y)) :
    Continuous (cell_outer_hequiv_aux_homotopy_aux_raw γ) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t, ⟨x, hx⟩⟩
  cases x with
  | inl y =>
      let getY : (cellMk γ) ⁻¹' cellOuter γ → Y :=
        fun u => Sum.elim id (fun _ => y) u.1
      have hget : Continuous getY :=
        (continuous_sumElim.2 ⟨continuous_id, continuous_const⟩).comp continuous_subtype_val
      apply (continuous_inl.comp (hget.comp continuous_snd)).continuousAt.congr_of_eventuallyEq
      filter_upwards [((isOpen_range_inl.preimage
        (continuous_subtype_val.comp continuous_snd)).mem_nhds ⟨y, rfl⟩)] with p hp
      rcases p with ⟨s, ⟨u, hu⟩⟩
      rcases hp with ⟨v, hv⟩
      dsimp at hv ⊢
      cases u <;> simp_all [cell_outer_hequiv_aux_homotopy_aux_raw, getY]
  | inr z =>
      have hzpos : (0 : ℝ) < ‖(z : ℂ)‖ := by
        have hm := (cell_outer_hequiv_aux_continuous_aux_mem γ (.inr z)).mp hx
        rcases hm with (⟨_, h⟩ | ⟨w, hw, h⟩)
        · cases h
        · injection h with hzw
          subst w
          change (1 : ℝ) / 3 < ‖(z : ℂ)‖ at hw
          nlinarith
      let getZ : (cellMk γ) ⁻¹' cellOuter γ → apm_t97J04_Disk :=
        fun u => Sum.elim (fun _ => z) id u.1
      have hget : Continuous getZ :=
        (continuous_sumElim.2 ⟨continuous_const, continuous_id⟩).comp continuous_subtype_val
      let diskMap : unitInterval × (cellMk γ) ⁻¹' cellOuter γ → apm_t97J04_Disk :=
        fun p => ⟨(cell_outer_hequiv_aux_scale p.1 (getZ p.2 : ℂ) : ℂ) * getZ p.2,
          by
            rw [Metric.mem_closedBall, dist_zero_right]
            apply cell_outer_hequiv_aux_scale_norm
            · cases hv : p.2.1 with
              | inl a => simpa [getZ, hv] using norm_pos_iff.mp hzpos
              | inr w =>
                  have hm := (cell_outer_hequiv_aux_continuous_aux_mem γ p.2.1).mp p.2.2
                  rcases hm with (⟨_, h⟩ | ⟨v, hv', h⟩)
                  · rw [hv] at h; cases h
                  · have hvw : v = w := Sum.inr.inj (h.trans hv)
                    subst v
                    simpa [getZ, hv] using
                      (show (w : ℂ) ≠ 0 by
                        intro h; change (1 : ℝ) / 3 < ‖(w : ℂ)‖ at hv'
                        rw [h, norm_zero] at hv'; norm_num at hv')
            · have h := (getZ p.2).property
              rw [Metric.mem_closedBall, dist_zero_right] at h
              exact h⟩
      have hdisk : Continuous diskMap := by
        apply Continuous.subtype_mk
        dsimp [diskMap, cell_outer_hequiv_aux_scale]
        have hv : Continuous (fun p : unitInterval × (cellMk γ) ⁻¹' cellOuter γ =>
            ((getZ p.2 : apm_t97J04_Disk) : ℂ)) :=
          continuous_subtype_val.comp (hget.comp continuous_snd)
        have hn0 : ∀ p : unitInterval × (cellMk γ) ⁻¹' cellOuter γ,
            ‖((getZ p.2 : apm_t97J04_Disk) : ℂ)‖ ≠ 0 := by
          intro p
          cases hp : p.2.1 with
          | inl a => simpa [getZ, hp] using (norm_ne_zero_iff.mpr (norm_pos_iff.mp hzpos))
          | inr w =>
              have hm := (cell_outer_hequiv_aux_continuous_aux_mem γ p.2.1).mp p.2.2
              rcases hm with (⟨_, h⟩ | ⟨v, hv', h⟩)
              · rw [hp] at h; cases h
              · have hvw : v = w := Sum.inr.inj (h.trans hp)
                subst v
                simpa [getZ, hp] using (show ‖(w : ℂ)‖ ≠ 0 by
                  intro h; change (1 : ℝ) / 3 < ‖(w : ℂ)‖ at hv'
                  rw [h] at hv'; norm_num at hv')
        exact (Complex.continuous_ofReal.comp
          ((continuous_subtype_val.comp continuous_fst).add
            ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div
              hv.norm hn0))).mul hv
      apply (continuous_inr.comp hdisk).continuousAt.congr_of_eventuallyEq
      filter_upwards [((isOpen_range_inr.preimage
        (continuous_subtype_val.comp continuous_snd)).mem_nhds ⟨z, rfl⟩)] with p hp
      rcases p with ⟨s, ⟨u, hu⟩⟩
      rcases hp with ⟨w, hw⟩
      dsimp at hw ⊢
      cases u <;> simp_all [cell_outer_hequiv_aux_homotopy_aux_raw, diskMap, getZ]

lemma cell_outer_hequiv_aux_homotopy_aux_respects (γ : C(Circle, Y))
    (t : unitInterval) (x y : (cellMk γ) ⁻¹' cellOuter γ)
    (hxy : cellMk γ x.1 = cellMk γ y.1) :
    cellMk γ (cell_outer_hequiv_aux_homotopy_aux_raw γ (t, x)) =
      cellMk γ (cell_outer_hequiv_aux_homotopy_aux_raw γ (t, y)) := by
  have hrel : Relation.EqvGen (CellRel γ) x.1 y.1 := Quotient.exact hxy
  have hgen : ∀ a b, Relation.EqvGen (CellRel γ) a b →
      ∀ (ha : cellMk γ a ∈ cellOuter γ) (hb : cellMk γ b ∈ cellOuter γ),
      cellMk γ (cell_outer_hequiv_aux_homotopy_aux_raw γ (t, ⟨a, ha⟩)) =
        cellMk γ (cell_outer_hequiv_aux_homotopy_aux_raw γ (t, ⟨b, hb⟩)) := by
    intro a b hab
    induction hab with
    | rel a b h =>
        intro ha hb
        cases h with
        | boundary z =>
            apply Quotient.sound
            have hs : cell_outer_hequiv_aux_scale t (circleToDisk z : ℂ) = 1 := by
              simp [cell_outer_hequiv_aux_scale, circleToDisk,
                PolygonSurfaceHomology.circleToPolygonDisk, Circle.norm_coe]
            simpa [cell_outer_hequiv_aux_homotopy_aux_raw, hs] using
              (Relation.EqvGen.rel _ _ (CellRel.boundary (γ := γ) z))
    | refl a => intro ha hb; rfl
    | symm a b h ih => intro ha hb; exact (ih hb ha).symm
    | trans a b c hab hbc ih₁ ih₂ =>
        intro ha hc
        have hb : cellMk γ b ∈ cellOuter γ := by
          change Quotient.mk _ b ∈ cellOuter γ
          rw [← Quotient.sound hab]
          exact ha
        exact (ih₁ ha hb).trans (ih₂ hb hc)
  exact hgen x.1 y.1 hrel x.2 y.2

lemma cell_outer_hequiv_aux_homotopy (γ : C(Circle, Y))
    (hc : Continuous (fun p : cellOuter γ ↦ cell_outer_hequiv_aux_descend γ p.1)) :
    ((cellInclOuter γ).comp ⟨fun p : cellOuter γ ↦ cell_outer_hequiv_aux_descend γ p.1, hc⟩).Homotopic
      (ContinuousMap.id (cellOuter γ)) := by
  let q : (cellMk γ) ⁻¹' cellOuter γ → cellOuter γ :=
    fun x => ⟨cellMk γ x.1, x.2⟩
  have hq0 : Topology.IsQuotientMap (cellMk γ) := ⟨Quotient.mk_surjective, rfl⟩
  have hq : Topology.IsQuotientMap q :=
    hq0.restrictPreimage_isOpen (cell_outer_hequiv_aux_continuous_aux_open γ)
  let s : cellOuter γ → (cellMk γ) ⁻¹' cellOuter γ :=
    fun x => Classical.choose (hq.surjective x)
  have hs (x : cellOuter γ) : q (s x) = x := Classical.choose_spec (hq.surjective x)
  let F : unitInterval × cellOuter γ → cellOuter γ := fun p =>
    ⟨cellMk γ (cell_outer_hequiv_aux_homotopy_aux_raw γ (p.1, s p.2)),
      cell_outer_hequiv_aux_homotopy_aux_raw_mem γ (p.1, s p.2)⟩
  have hFq (p : unitInterval × (cellMk γ) ⁻¹' cellOuter γ) :
      F (p.1, q p.2) =
        ⟨cellMk γ (cell_outer_hequiv_aux_homotopy_aux_raw γ p),
          cell_outer_hequiv_aux_homotopy_aux_raw_mem γ p⟩ := by
    apply Subtype.ext
    exact cell_outer_hequiv_aux_homotopy_aux_respects γ p.1 (s (q p.2)) p.2
      (congrArg Subtype.val (hs (q p.2)))
  have hF : Continuous F := by
    apply hq.continuous_lift_prod_right
    have hcont : Continuous (fun p : unitInterval × (cellMk γ) ⁻¹' cellOuter γ =>
        (⟨cellMk γ (cell_outer_hequiv_aux_homotopy_aux_raw γ p),
          cell_outer_hequiv_aux_homotopy_aux_raw_mem γ p⟩ : cellOuter γ)) :=
      Continuous.subtype_mk ((continuous_cellMk γ).comp
        (cell_outer_hequiv_aux_homotopy_aux_raw_continuous γ)) _
    convert hcont using 1
    funext p
    exact hFq p
  refine ⟨ContinuousMap.Homotopy.mk
    ⟨F, hF⟩ ?_ ?_⟩
  · intro x
    apply Subtype.ext
    change (F (0, x)).1 = _
    rw [show F (0, x) = F (0, q (s x)) by rw [hs x]]
    rw [congrArg Subtype.val (hFq (0, s x))]
    generalize he : s x = u
    rcases u with ⟨u, hu⟩
    cases u with
    | inl y =>
        change cellMk γ (.inl y) = cellIncl γ (cell_outer_hequiv_aux_descend γ x.1)
        rw [show x = q (s x) by rw [hs x], he]
        rfl
    | inr z =>
        have hz : (z : ℂ) ≠ 0 := by
          have hm := (cell_outer_hequiv_aux_continuous_aux_mem γ (.inr z)).mp hu
          rcases hm with (⟨_, h⟩ | ⟨w, hw, h⟩)
          · cases h
          · injection h with hzw
            subst w
            intro hz
            change (1 : ℝ) / 3 < ‖(z : ℂ)‖ at hw
            rw [hz, norm_zero] at hw
            norm_num at hw
        let w : Circle := ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
          simp [Submonoid.unitSphere, div_self (norm_ne_zero_iff.mpr hz)]⟩
        have hb := (Relation.EqvGen.rel _ _ (CellRel.boundary (γ := γ) w)).symm
        change cellMk γ _ = cellIncl γ (cell_outer_hequiv_aux_descend γ x.1)
        rw [show x = q (s x) by rw [hs x]]
        rw [he]
        change cellMk γ _ = cellMk γ (.inl (γ (cell_outer_hequiv_aux_radial (z : ℂ))))
        apply Quotient.sound
        convert hb using 1
        · apply congrArg Sum.inr
          apply Subtype.ext
          simp [cell_outer_hequiv_aux_scale, w, circleToDisk,
            PolygonSurfaceHomology.circleToPolygonDisk, div_eq_mul_inv, mul_comm]
        · apply congrArg Sum.inl
          congr 1
          apply Subtype.ext
          simp [cell_outer_hequiv_aux_radial, hz, w]
  · intro x
    apply Subtype.ext
    change (F (1, x)).1 = _
    rw [show F (1, x) = F (1, q (s x)) by rw [hs x]]
    rw [congrArg Subtype.val (hFq (1, s x))]
    have hone : cell_outer_hequiv_aux_homotopy_aux_raw γ (1, s x) = (s x).1 := by
      generalize he : s x = u
      rcases u with ⟨u, hu⟩
      cases u <;> simp [cell_outer_hequiv_aux_homotopy_aux_raw,
        cell_outer_hequiv_aux_scale]
    exact (congrArg (cellMk γ) hone).trans (congrArg Subtype.val (hs x))

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
def cell_overlap_loop_aux_disk (p : unitInterval × Circle) : apm_t97J04_Disk :=
  ⟨((((1 + (p.1 : ℝ)) / 2 : ℝ) : ℂ) * (p.2 : ℂ)), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg]
    · rw [Circle.norm_coe]
      have ht := p.1.2.2
      norm_num at ht ⊢
      linarith
    · have ht := p.1.2.1
      positivity⟩

lemma cell_overlap_loop_aux_disk_continuous :
    Continuous cell_overlap_loop_aux_disk := by
  apply Continuous.subtype_mk
  fun_prop

def cell_overlap_loop_aux_map (γ : C(Circle, Y)) :
    C(unitInterval × Circle, cellOuter γ) :=
  ⟨fun p ↦ ⟨cellMk γ (.inr (cell_overlap_loop_aux_disk p)),
      ⟨.inr (cell_overlap_loop_aux_disk p), Or.inr
        ⟨cell_overlap_loop_aux_disk p, by
          change (1 : ℝ) / 3 <
            ‖((((1 + (p.1 : ℝ)) / 2 : ℝ) : ℂ) * (p.2 : ℂ))‖
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg,
            Circle.norm_coe]
          · have ht := p.1.2.1
            norm_num at ht ⊢
            linarith
          · have ht := p.1.2.1
            positivity, rfl⟩, rfl⟩⟩,
    ((continuous_cellMk γ).comp
      (continuous_inr.comp cell_overlap_loop_aux_disk_continuous)).subtype_mk _⟩

lemma cell_overlap_loop (γ : C(Circle, Y)) :
    ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
        (cellOverlapCircle γ)).Homotopic ((cellInclOuter γ).comp γ) := by
  refine ⟨ContinuousMap.Homotopy.mk (cell_overlap_loop_aux_map γ) ?_ ?_⟩
  · intro z
    apply Subtype.ext
    change cellMk γ (.inr (cell_overlap_loop_aux_disk (0, z))) =
      cellMk γ (.inr (halfDisk z))
    congr 2
    apply Subtype.ext
    simp [cell_overlap_loop_aux_disk, halfDisk, div_eq_mul_inv, mul_comm]
  · intro z
    apply Subtype.ext
    change cellMk γ (.inr _) = cellMk γ (.inl (γ z))
    apply Quotient.sound
    convert (Relation.EqvGen.rel _ _ (CellRel.boundary (γ := γ) z)).symm using 1
    apply congrArg Sum.inr
    apply Subtype.ext
    simp [cell_overlap_loop_aux_disk, circleToDisk,
      PolygonSurfaceHomology.circleToPolygonDisk]

/-- A6. Path-connectedness of the pieces and of the cell space. -/
lemma cell_pathConnected (γ : C(Circle, Y)) [PathConnectedSpace Y]
    (hA3 : ∃ e : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≃ₕ Circle,
      e.invFun = cellOverlapCircle γ)
    (hA4 : ∃ e : (cellOuter γ) ≃ₕ Y, e.invFun = cellInclOuter γ) :
    PathConnectedSpace (cellOuter γ) ∧
      PathConnectedSpace (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ∧
      PathConnectedSpace (Cell γ) := by
  sorry

/-- A7a. A homotopy equivalence is bijective on π₁ at every basepoint
(`FundamentalGroupoidFunctor.equivOfHomotopyEquiv` or directly: both
composites are homotopic to the identity, and A7b). -/
lemma cell_piOne_aux_hequiv_bijective {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₕ B) (b : B) :
    Function.Bijective (FundamentalGroup.map e.invFun b) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e.symm
  let ff := E.fullyFaithfulFunctor
  let m := FundamentalGroup.map e.invFun b
  let mEquiv : FundamentalGroup B b ≃* FundamentalGroup A (e.invFun b) :=
    { toFun := m
      invFun := fun g => ff.preimage g
      left_inv := fun g => ff.preimage_map g
      right_inv := fun g => ff.map_preimage g
      map_mul' := m.map_mul }
  exact mEquiv.bijective

/-- A7b. Homotopic maps agree on π₁ up to transport along the track of the
basepoint (`ContinuousMap.Homotopy`; Mathlib's
`FundamentalGroupoidFunctor.homotopicMapsNatIso`). -/
lemma cell_piOne_aux_homotopic_conj {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] (f g : C(A, B)) (hfg : f.Homotopic g) (a : A) :
    ∃ p : Path (g a) (f a), ∀ x : FundamentalGroup A a,
      FundamentalGroup.map f a x =
        FundamentalGroup.fundamentalGroupMulEquivOfPath p (FundamentalGroup.map g a x) := by
  exact apm_t92J05_homotopic_map_conj hfg.symm a

/-- A7c. The overlap's image in the outer piece is normally generated by the
radius-`1/2` circle: π₁ of the overlap at `cellOverlapCircle γ 1` is the image
of `π₁(Circle, 1)` (A3: a homotopy equivalence with inverse
`cellOverlapCircle γ`, so A7a), which is generated by
`circleIntegerLoopOneClass` (`PolygonSurfaceHomology.circleIntegerLoopOneClass_generates`). -/
lemma cell_piOne_aux_overlap_generator (γ : C(Circle, Y))
    (hA3 : ∃ e : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≃ₕ Circle,
      e.invFun = cellOverlapCircle γ) :
    Subgroup.normalClosure ((FundamentalGroup.map
        (apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ))
        (cellOverlapCircle γ 1)).range :
          Set (FundamentalGroup (cellOuter γ)
            (apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)
              (cellOverlapCircle γ 1)))) =
      Subgroup.normalClosure {FundamentalGroup.map
        ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
          (cellOverlapCircle γ)) 1 PolygonSurfaceHomology.circleIntegerLoopOneClass} := by
  obtain ⟨e, he⟩ := hA3
  have hc : Function.Surjective
      (FundamentalGroup.map (cellOverlapCircle γ) (1 : Circle)) := by
    have hb := (cell_piOne_aux_hequiv_bijective e (1 : Circle)).2
    rw [he] at hb
    exact hb
  have hmap (z : FundamentalGroup Circle 1) :
      FundamentalGroup.map
          ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
            (cellOverlapCircle γ)) 1 z =
        FundamentalGroup.map
          (apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ))
          (cellOverlapCircle γ 1)
          (FundamentalGroup.map (cellOverlapCircle γ) 1 z) := by
    induction z using Path.Homotopic.Quotient.ind with
    | mk p => rfl
  apply le_antisymm
  · refine Subgroup.normalClosure_le_normal
      (N := Subgroup.normalClosure
        ({FundamentalGroup.map
          ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
            (cellOverlapCircle γ)) 1
            PolygonSurfaceHomology.circleIntegerLoopOneClass} : _)) ?_
    rintro y ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hc x
    obtain ⟨n, hn⟩ :=
      PolygonSurfaceHomology.circleIntegerLoopOneClass_generates z
    subst x
    rw [← hn, map_zpow]
    rw [map_zpow, ← hmap]
    exact (Subgroup.normalClosure
      ({FundamentalGroup.map
        ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
          (cellOverlapCircle γ)) 1
          PolygonSurfaceHomology.circleIntegerLoopOneClass} :
        Set (FundamentalGroup (cellOuter γ)
          (apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)
            (cellOverlapCircle γ 1))))).zpow_mem
      (Subgroup.subset_normalClosure (Set.mem_singleton _)) n
  · apply Subgroup.normalClosure_mono
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    rw [hmap]
    exact ⟨FundamentalGroup.map (cellOverlapCircle γ) 1
      PolygonSurfaceHomology.circleIntegerLoopOneClass, rfl⟩

/-- A7. **van Kampen for one 2-cell.**  The inclusion `Y → Y ∪_γ D²` is onto
on π₁ with kernel the normal closure of `[γ]`.  Apply
`apm_t92J05_twoOpen_simplyConnectedRight_kernel` to the cover (A1, A2, A6) at
the overlap point `cellOverlapCircle γ 1`; transfer from the outer piece to
`Y` by A4, identify the overlap image with a conjugate of `[γ]` by A3 + A5
(a free homotopy conjugates; normal closures absorb conjugation), and move the
basepoint along any path (again a conjugation). -/
lemma cell_piOne_aux_normalClosure_isConj
    {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    Subgroup.normalClosure ({a} : Set G) =
      Subgroup.normalClosure ({b} : Set G) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    obtain ⟨c, rfl⟩ := isConj_iff.mp h.symm
    exact Subgroup.normalClosure_normal.conj_mem _
      (Subgroup.subset_normalClosure (Set.mem_singleton _)) c
  · apply Subgroup.normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    obtain ⟨c, rfl⟩ := isConj_iff.mp h
    exact Subgroup.normalClosure_normal.conj_mem _
      (Subgroup.subset_normalClosure (Set.mem_singleton _)) c

lemma cell_piOne_aux_transport_kernel
    {G H K : Type*} [Group G] [Group H] [Group K]
    (e : G ≃* H) (f : H →* K) (r : H)
    (hsurj : Function.Surjective f)
    (hker : MonoidHom.ker f = Subgroup.normalClosure ({r} : Set H)) :
    Function.Surjective (f.comp e.toMonoidHom) ∧
      MonoidHom.ker (f.comp e.toMonoidHom) =
        Subgroup.normalClosure ({e.symm r} : Set G) := by
  constructor
  · intro k
    obtain ⟨x, rfl⟩ := hsurj k
    exact ⟨e.symm x, by simp⟩
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply]
    change f (e x) = 1 ↔ _
    rw [show f (e x) = 1 ↔ e x ∈ MonoidHom.ker f by rfl, hker]
    constructor
    · intro hx
      have hx' : e.symm (e x) ∈
          (Subgroup.normalClosure ({r} : Set H)).map e.symm.toMonoidHom :=
        ⟨e x, hx, rfl⟩
      have hm : (Subgroup.normalClosure ({r} : Set H)).map e.symm.toMonoidHom =
          Subgroup.normalClosure ({e.symm r} : Set G) := by
        rw [Subgroup.map_normalClosure ({r} : Set H) e.symm.toMonoidHom
          e.symm.surjective]
        congr 1
        ext z
        simp
      rw [hm] at hx'
      simpa using hx'
    · intro hx
      have hx' : e (e.symm (e x)) ∈
          (Subgroup.normalClosure ({e.symm r} : Set G)).map e.toMonoidHom :=
        ⟨x, hx, by simp⟩
      have hm : (Subgroup.normalClosure ({e.symm r} : Set G)).map e.toMonoidHom =
          Subgroup.normalClosure ({r} : Set H) := by
        rw [Subgroup.map_normalClosure ({e.symm r} : Set G) e.toMonoidHom
          e.surjective]
        congr 1
        ext z
        simp
      rw [hm] at hx'
      simpa using hx'

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
      PathConnectedSpace (Cell γ))
    (hbij : ∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₕ B) (b : B),
      Function.Bijective (FundamentalGroup.map e.invFun b))
    (hconj : ∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f g : C(A, B)),
      f.Homotopic g → ∀ a : A, ∃ p : Path (g a) (f a), ∀ x : FundamentalGroup A a,
        FundamentalGroup.map f a x =
          FundamentalGroup.fundamentalGroupMulEquivOfPath p (FundamentalGroup.map g a x))
    (hgen : Subgroup.normalClosure ((FundamentalGroup.map
        (apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ))
        (cellOverlapCircle γ 1)).range :
          Set (FundamentalGroup (cellOuter γ)
            (apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)
              (cellOverlapCircle γ 1)))) =
      Subgroup.normalClosure {FundamentalGroup.map
        ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
          (cellOverlapCircle γ)) 1 PolygonSurfaceHomology.circleIntegerLoopOneClass}) :
    Function.Surjective (FundamentalGroup.map (cellIncl γ) y) ∧
      (FundamentalGroup.map (cellIncl γ) y).ker =
        Subgroup.normalClosure {loopClassAt γ y h} := by
  subst y
  let x0 : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) := cellOverlapCircle γ 1
  let u0 : cellOuter γ :=
    apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ) x0
  let v0 : cellOuter γ := cellInclOuter γ (γ 1)
  let j : C(cellOuter γ, Cell γ) :=
    apm_t92J05_twoOpen_leftInclusion (cellOuter γ)
  let l0 := FundamentalGroup.map j u0
  let r0 : FundamentalGroup (cellOuter γ) u0 :=
    FundamentalGroup.map
      ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
        (cellOverlapCircle γ)) 1
      PolygonSurfaceHomology.circleIntegerLoopOneClass
  letI : PathConnectedSpace (cellOuter γ) := hA6.1
  letI : PathConnectedSpace (cellOuter γ ∩ cellInner γ : Set (Cell γ)) := hA6.2.1
  letI : PathConnectedSpace (Cell γ) := hA6.2.2
  letI : ContractibleSpace (cellInner γ) := hA2
  obtain ⟨hs0, hk0⟩ :=
    apm_t92J05_twoOpen_simplyConnectedRight_kernel
      (cellOuter γ) (cellInner γ) hA1.1 hA1.2.1 hA1.2.2 x0
  have hk0' : MonoidHom.ker l0 =
      Subgroup.normalClosure ({r0} : Set (FundamentalGroup (cellOuter γ) u0)) := by
    simpa [l0, u0, x0, r0] using hk0.trans hgen
  obtain ⟨p, hp⟩ := hconj
    ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
      (cellOverlapCircle γ)) ((cellInclOuter γ).comp γ) hA5 1
  let ep : FundamentalGroup (cellOuter γ) v0 ≃* FundamentalGroup (cellOuter γ) u0 :=
    FundamentalGroup.fundamentalGroupMulEquivOfPath p
  let a : FundamentalGroup Y (γ 1) := FundamentalGroup.map γ 1
    PolygonSurfaceHomology.circleIntegerLoopOneClass
  have hr : r0 = ep (FundamentalGroup.map (cellInclOuter γ) (γ 1) a) := by
    simpa [r0, ep, v0, u0, x0] using
      hp PolygonSurfaceHomology.circleIntegerLoopOneClass
  let eqout : FundamentalGroup (Cell γ) (j v0) ≃* FundamentalGroup (Cell γ) (j u0) :=
    FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map j.continuous)
  let l : FundamentalGroup (cellOuter γ) u0 →* FundamentalGroup (Cell γ) (j v0) :=
    eqout.symm.toMonoidHom.comp l0
  have hsl : Function.Surjective l := eqout.symm.surjective.comp hs0
  have hkl : MonoidHom.ker l =
      Subgroup.normalClosure ({r0} : Set (FundamentalGroup (cellOuter γ) u0)) := by
    rw [← hk0']
    ext z
    simp [l, eqout]
  obtain ⟨e, he⟩ := hA4
  have hb := hbij e (γ 1)
  rw [he] at hb
  let ei : FundamentalGroup Y (γ 1) ≃* FundamentalGroup (cellOuter γ) v0 :=
    { toFun := FundamentalGroup.map (cellInclOuter γ) (γ 1)
      invFun := Function.invFun (FundamentalGroup.map (cellInclOuter γ) (γ 1))
      left_inv := Function.leftInverse_invFun hb.1
      right_inv := Function.rightInverse_invFun hb.2
      map_mul' := (FundamentalGroup.map (cellInclOuter γ) (γ 1)).map_mul }
  obtain ⟨hs1, hk1⟩ := cell_piOne_aux_transport_kernel ep l r0 hsl hkl
  rw [hr] at hk1
  have hk1' : MonoidHom.ker (l.comp ep.toMonoidHom) =
      Subgroup.normalClosure
        ({FundamentalGroup.map (cellInclOuter γ) (γ 1)
          a} :
          Set (FundamentalGroup (cellOuter γ) v0)) := by
    simpa [ep] using hk1
  obtain ⟨hs2, hk2⟩ := cell_piOne_aux_transport_kernel ei
    (l.comp ep.toMonoidHom)
    (FundamentalGroup.map (cellInclOuter γ) (γ 1)
      a) hs1 hk1'
  have hmaps : (l.comp ep.toMonoidHom).comp ei.toMonoidHom =
      FundamentalGroup.map (cellIncl γ) (γ 1) := by
    ext z
    apply eqout.injective
    change eqout (eqout.symm (l0 (ep (ei z)))) =
      eqout (FundamentalGroup.map (cellIncl γ) (γ 1) z)
    rw [eqout.apply_symm_apply]
    have hz := apm_t92J05_map_ofPath j p (ei z)
    have hc : FundamentalGroup.map j v0 (ei z) =
        FundamentalGroup.map (cellIncl γ) (γ 1) z := by
      induction z using Path.Homotopic.Quotient.ind with
      | mk q => rfl
    rw [← hc]
    simpa [ep, eqout, l0, v0, u0] using hz
  rw [hmaps] at hs2 hk2
  refine ⟨hs2, ?_⟩
  have hei : ei.symm (FundamentalGroup.map (cellInclOuter γ) (γ 1) a) = a := by
    exact ei.symm_apply_apply a
  rw [hei] at hk2
  simpa [a, loopClassAt] using hk2
/-- A8. **H₁ of a 2-cell attachment.**  Integral Mayer–Vietoris
(`IntegralMV.integralMayerVietoris`, transported to the `singularHomologyFunctor`
form by `IntegralSingularHomologyComparison`) for the cover A1: `H₁(inner) = 0`,
`H₀(overlap) → H₀(outer) ⊕ H₀(inner)` injective, `H₁(overlap) ≅ H₁(Circle)` by
A3 and its image is `γ_*` by A5, `H₁(outer) ≅ H₁(Y)` by A4. -/
lemma cell_H1_aux_exact
    {A B P D E : ModuleCat ℤ}
    (f : A ⟶ B) (I : A ⟶ P) (g : B ⟶ D) (J : P ⟶ D)
    (inB : B ⟶ P) (prB : P ⟶ B) (d : D ⟶ E) (i₀ : E ⟶ A)
    (hJ : inB ≫ J = g) (hI : I ≫ prB = f)
    (hsplit : ∀ x, inB.hom (prB.hom x) = x)
    (hproj : ∀ x, prB.hom (inB.hom x) = x)
    (hi₀ : Function.Injective i₀.hom)
    (hex₁ : LinearMap.range I.hom = LinearMap.ker J.hom)
    (hex₂ : LinearMap.range J.hom = LinearMap.ker d.hom)
    (hex₃ : LinearMap.range d.hom = LinearMap.ker i₀.hom) :
    Function.Surjective g.hom ∧ LinearMap.ker g.hom = LinearMap.range f.hom := by
  have hd_zero : d.hom = 0 := by
    apply LinearMap.range_eq_bot.mp
    rw [hex₃, LinearMap.ker_eq_bot.mpr hi₀]
  have hJ_surj : Function.Surjective J.hom := by
    rw [← LinearMap.range_eq_top, hex₂, hd_zero, LinearMap.ker_zero]
  constructor
  · intro y
    obtain ⟨x, hx⟩ := hJ_surj y
    refine ⟨prB.hom x, ?_⟩
    have hg := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hJ) (prB.hom x)
    rw [← hg, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      hsplit, hx]
  · apply le_antisymm
    · intro x hx
      let q := inB.hom x
      have hxJ : q ∈ LinearMap.ker J.hom := by
        change J.hom q = 0
        have hg := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hJ) x
        have hg' : J.hom q = g.hom x := by
          simpa [q, ModuleCat.hom_comp] using hg
        exact hg'.trans hx
      rw [← hex₁] at hxJ
      obtain ⟨a, ha⟩ := hxJ
      refine ⟨a, ?_⟩
      have hf := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hI) a
      rw [← hf, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, ha]
      simpa [q] using hproj x
    · rintro x ⟨a, rfl⟩
      let q := inB.hom (f.hom a)
      have haI : I.hom a = q := by
        rw [← hsplit (I.hom a)]
        have hf := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hI) a
        simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hf
        rw [hf]
      have : q ∈ LinearMap.ker J.hom := by
        rw [← hex₁]
        exact ⟨a, haI⟩
      change g.hom (f.hom a) = 0
      have hg := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hJ) (f.hom a)
      have hg' : J.hom q = g.hom (f.hom a) := by
        simpa [q, ModuleCat.hom_comp] using hg
      exact hg'.symm.trans (show J.hom q = 0 from this)

lemma cell_H1_aux_inner_zero (γ : C(Circle, Y))
    (hA2 : ContractibleSpace (cellInner γ)) :
    Subsingleton (IntegralMV.HZ 1 (cellInner γ)) := by
  letI := hA2
  apply ModuleCat.subsingleton_of_isZero
  exact
    ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero
      _ 1
      (ConstructionTargets.SingularHomologyConcrete.contractibleHigherHomology_isZero
        _ 1 (by decide))

lemma cell_H1_aux_mv0_injective_aux_pathConnected
    {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    (e : S ≃ₕ T) [PathConnectedSpace T] : PathConnectedSpace S := by
  rcases e.left_inv with ⟨K⟩
  refine ⟨⟨e.invFun (Classical.choice (inferInstance : Nonempty T))⟩, ?_⟩
  intro x y
  refine ⟨(K.evalAt x).symm.trans
    (((PathConnectedSpace.somePath (e x) (e y)).map e.invFun.continuous).trans
      (K.evalAt y))⟩

lemma cell_H1_aux_mv0_injective (γ : C(Circle, Y)) [PathConnectedSpace Y]
    (hA3 : ∃ e : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≃ₕ Circle,
      e.invFun = cellOverlapCircle γ)
    (hA4 : ∃ e : (cellOuter γ) ≃ₕ Y, e.invFun = cellInclOuter γ)
    (hA2 : ContractibleSpace (cellInner γ)) :
    Function.Injective (IntegralMV.mvI (cellOuter γ) (cellInner γ) 0).hom := by
  rcases hA3 with ⟨eI, heI⟩
  rcases hA4 with ⟨eO, heO⟩
  letI : PathConnectedSpace (cellOuter γ ∩ cellInner γ : Set (Cell γ)) :=
    cell_H1_aux_mv0_injective_aux_pathConnected eI
  letI : PathConnectedSpace (cellOuter γ) :=
    cell_H1_aux_mv0_injective_aux_pathConnected eO
  let f : C((cellOuter γ ∩ cellInner γ : Set (Cell γ)), cellOuter γ) :=
    ⟨Set.inclusion Set.inter_subset_left, continuous_inclusion Set.inter_subset_left⟩
  let p : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) :=
    Classical.choice inferInstance
  let q : cellOuter γ := Classical.choice inferInstance
  let e := ConstructionTargets.CoefficientH0.h0Iso ℤ p ≪≫
    (ConstructionTargets.CoefficientH0.h0Iso ℤ q).symm
  have hmap : e.hom = IntegralMV.mvIncl Set.inter_subset_left 0 := by
    apply (cancel_mono (ConstructionTargets.CoefficientH0.h0Iso ℤ q).hom).mp
    change (ConstructionTargets.CoefficientH0.h0Augmentation ℤ ≫
        ConstructionTargets.CoefficientH0.singularVertexH0Class ℤ q) ≫
        ConstructionTargets.CoefficientH0.h0Augmentation ℤ = _
    rw [Category.assoc,
      ConstructionTargets.CoefficientH0.singularVertexH0Class_comp_h0Augmentation,
      Category.comp_id]
    exact (ConstructionTargets.CoefficientH0.h0Augmentation_naturality ℤ f).symm
  have hincl : Function.Injective
      (IntegralMV.mvIncl
        (Set.inter_subset_left : cellOuter γ ∩ cellInner γ ⊆ cellOuter γ) 0).hom := by
    rw [← hmap]
    exact (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  intro a b hab
  apply hincl
  have h := congrArg
    (fun z => (CategoryTheory.Limits.biprod.fst : IntegralMV.HZ 0 (cellOuter γ) ⊞
      IntegralMV.HZ 0 (cellInner γ) ⟶ IntegralMV.HZ 0 (cellOuter γ)).hom z) hab
  simp only [IntegralMV.mvI] at h
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    CategoryTheory.Limits.biprod.lift_fst] at h
  exact h

noncomputable def cell_H1_aux_transport_iso
    {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    (e : S ≃ₕ T) (k : ℕ) : H k S ≅ H k T where
  hom := Hmap e.toFun k
  inv := Hmap e.invFun k
  hom_inv_id := by
    dsimp only [Hmap]
    rw [← Functor.map_comp]
    change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (e.invFun.comp e.toFun)) = _
    rw [ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) e.left_inv k]
    exact ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).map_id (TopCat.of S)
  inv_hom_id := by
    dsimp only [Hmap]
    rw [← Functor.map_comp]
    change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (e.toFun.comp e.invFun)) = _
    rw [ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) e.right_inv k]
    exact ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).map_id (TopCat.of T)

lemma cell_H1_aux_transport (γ : C(Circle, Y))
    (hA3 : ∃ e : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≃ₕ Circle,
      e.invFun = cellOverlapCircle γ)
    (hA4 : ∃ e : (cellOuter γ) ≃ₕ Y, e.invFun = cellInclOuter γ)
    (hA5 : ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
        (cellOverlapCircle γ)).Homotopic ((cellInclOuter γ).comp γ)) :
    ∃ (eI : IntegralMV.HZ 1 (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≅
          H 1 Circle)
      (eO : IntegralMV.HZ 1 (cellOuter γ) ≅ H 1 Y),
      IntegralMV.mvIncl
          (Set.inter_subset_left : cellOuter γ ∩ cellInner γ ⊆ cellOuter γ) 1 ≫
          eO.hom = eI.hom ≫ Hmap γ 1 ∧
      eO.inv ≫ IntegralMV.mvToX (cellOuter γ) 1 = Hmap (cellIncl γ) 1 := by
  obtain ⟨eI, heI⟩ := hA3
  obtain ⟨eO, heO⟩ := hA4
  refine ⟨cell_H1_aux_transport_iso eI 1,
    cell_H1_aux_transport_iso eO 1, ?_, ?_⟩
  · apply (cancel_epi (cell_H1_aux_transport_iso eI 1).inv).1
    simp only [Iso.inv_hom_id_assoc]
    change Hmap eI.invFun 1 ≫
        IntegralMV.mvIncl Set.inter_subset_left 1 ≫ Hmap eO.toFun 1 = Hmap γ 1
    change Hmap eI.invFun 1 ≫
      Hmap (apm_t92J05_twoOpen_overlapToLeft
          (cellOuter γ) (cellInner γ)) 1 ≫ Hmap eO.toFun 1 = Hmap γ 1
    have hsquare :
        (eO.toFun.comp ((apm_t92J05_twoOpen_overlapToLeft
          (cellOuter γ) (cellInner γ)).comp eI.invFun)).Homotopic γ := by
      rw [heI]
      have h₁ := (ContinuousMap.Homotopic.refl eO.toFun).comp hA5
      rw [← heO] at h₁
      have h₂ := eO.right_inv.comp (ContinuousMap.Homotopic.refl γ)
      exact h₁.trans (by simpa only [ContinuousMap.comp_assoc,
        ContinuousMap.id_comp] using h₂)
    dsimp only [Hmap]
    rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
    change ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (eO.toFun.comp
          ((apm_t92J05_twoOpen_overlapToLeft
            (cellOuter γ) (cellInner γ)).comp eI.invFun))) = _
    rw [ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) hsquare 1]
  · change Hmap eO.invFun 1 ≫ IntegralMV.mvToX (cellOuter γ) 1 = _
    change Hmap eO.invFun 1 ≫
      Hmap ⟨Subtype.val, continuous_subtype_val⟩ 1 = _
    dsimp only [Hmap]
    rw [← Functor.map_comp, heO]
    rfl

lemma cell_H1 (γ : C(Circle, Y)) [PathConnectedSpace Y]
    (hA1 : IsOpen (cellOuter γ) ∧ IsOpen (cellInner γ) ∧
      cellOuter γ ∪ cellInner γ = Set.univ)
    (hA2 : ContractibleSpace (cellInner γ))
    (hA3 : ∃ e : (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≃ₕ Circle,
      e.invFun = cellOverlapCircle γ)
    (hA4 : ∃ e : (cellOuter γ) ≃ₕ Y, e.invFun = cellInclOuter γ)
    (hA5 : ((apm_t92J05_twoOpen_overlapToLeft (cellOuter γ) (cellInner γ)).comp
        (cellOverlapCircle γ)).Homotopic ((cellInclOuter γ).comp γ))
    (hinner : Subsingleton (IntegralMV.HZ 1 (cellInner γ)))
    (hmv0 : Function.Injective (IntegralMV.mvI (cellOuter γ) (cellInner γ) 0).hom)
    (htrans : ∃ (eI : IntegralMV.HZ 1 (cellOuter γ ∩ cellInner γ : Set (Cell γ)) ≅
          H 1 Circle)
      (eO : IntegralMV.HZ 1 (cellOuter γ) ≅ H 1 Y),
      IntegralMV.mvIncl
          (Set.inter_subset_left : cellOuter γ ∩ cellInner γ ⊆ cellOuter γ) 1 ≫
          eO.hom = eI.hom ≫ Hmap γ 1 ∧
      eO.inv ≫ IntegralMV.mvToX (cellOuter γ) 1 = Hmap (cellIncl γ) 1) :
    Function.Surjective (Hmap (cellIncl γ) 1).hom ∧
      LinearMap.ker (Hmap (cellIncl γ) 1).hom = LinearMap.range (Hmap γ 1).hom := by
  rcases htrans with ⟨eI, eO, hf, hg⟩
  obtain ⟨δ, hexI, hexJ, hexδ⟩ :=
    IntegralMV.integralMayerVietoris (cellOuter γ) (cellInner γ)
      hA1.1 hA1.2.1 hA1.2.2
  letI : Subsingleton (IntegralMV.HZ 1 (cellInner γ)) := hinner
  have hzero := ModuleCat.isZero_of_subsingleton (IntegralMV.HZ 1 (cellInner γ))
  have hproj : (Limits.biprod.fst :
      IntegralMV.HZ 1 (cellOuter γ) ⊞ IntegralMV.HZ 1 (cellInner γ) ⟶ _) ≫
      Limits.biprod.inl = 𝟙 _ := by
    rw [← Limits.biprod.total]
    rw [hzero.eq_of_tgt (Limits.biprod.snd : _ ⟶ IntegralMV.HZ 1 (cellInner γ)) 0]
    simp
  have hsplit : ∀ x : (IntegralMV.HZ 1 (cellOuter γ) ⊞
      IntegralMV.HZ 1 (cellInner γ) : ModuleCat ℤ),
      (Limits.biprod.inl : IntegralMV.HZ 1 (cellOuter γ) ⟶ _).hom
        ((Limits.biprod.fst : _ ⟶ IntegralMV.HZ 1 (cellOuter γ)).hom x) = x := by
    intro x
    have := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hproj) x
    simpa [ModuleCat.hom_comp] using this
  have hd_zero : (δ 0).hom = 0 := by
    apply LinearMap.range_eq_bot.mp
    rw [hexδ 0, LinearMap.ker_eq_bot.mpr hmv0]
  have hJ_surj : Function.Surjective
      (IntegralMV.mvJ (cellOuter γ) (cellInner γ) 1).hom := by
    rw [← LinearMap.range_eq_top, hexJ 0, hd_zero, LinearMap.ker_zero]
  have hcore : Function.Surjective (IntegralMV.mvToX (cellOuter γ) 1).hom ∧
      LinearMap.ker (IntegralMV.mvToX (cellOuter γ) 1).hom =
        LinearMap.range (IntegralMV.mvIncl
          (Set.inter_subset_left : cellOuter γ ∩ cellInner γ ⊆ cellOuter γ) 1).hom := by
    constructor
    · intro y
      obtain ⟨x, hx⟩ := hJ_surj y
      refine ⟨(Limits.biprod.fst : _ ⟶ IntegralMV.HZ 1 (cellOuter γ)).hom x, ?_⟩
      have hx' : (IntegralMV.mvJ (cellOuter γ) (cellInner γ) 1).hom
          ((Limits.biprod.inl : IntegralMV.HZ 1 (cellOuter γ) ⟶ _).hom
            ((Limits.biprod.fst : _ ⟶ IntegralMV.HZ 1 (cellOuter γ)).hom x)) = y := by
        rw [hsplit x, hx]
      change ((Limits.biprod.inl ≫ IntegralMV.mvJ
        (cellOuter γ) (cellInner γ) 1).hom
          ((Limits.biprod.fst : _ ⟶ IntegralMV.HZ 1 (cellOuter γ)).hom x)) = y at hx'
      rw [show Limits.biprod.inl ≫ IntegralMV.mvJ
        (cellOuter γ) (cellInner γ) 1 = IntegralMV.mvToX (cellOuter γ) 1 by
          simp [IntegralMV.mvJ]] at hx'
      exact hx'
    · ext x
      constructor
      · intro hx
        have hq : (Limits.biprod.inl : IntegralMV.HZ 1 (cellOuter γ) ⟶ _).hom x ∈
            LinearMap.ker (IntegralMV.mvJ (cellOuter γ) (cellInner γ) 1).hom := by
          change ((Limits.biprod.inl ≫ IntegralMV.mvJ
            (cellOuter γ) (cellInner γ) 1).hom x) = 0
          rw [show Limits.biprod.inl ≫ IntegralMV.mvJ
            (cellOuter γ) (cellInner γ) 1 = IntegralMV.mvToX (cellOuter γ) 1 by
              simp [IntegralMV.mvJ]]
          exact hx
        rw [← hexI 1] at hq
        obtain ⟨z, hz⟩ := hq
        refine ⟨z, ?_⟩
        have hp : IntegralMV.mvI (cellOuter γ) (cellInner γ) 1 ≫
            Limits.biprod.fst = IntegralMV.mvIncl Set.inter_subset_left 1 := by
          simp [IntegralMV.mvI]
        have hz' := congrArg
          (fun q => (Limits.biprod.fst : _ ⟶ IntegralMV.HZ 1 (cellOuter γ)).hom q) hz
        have hp' := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hp) z
        apply hp'.symm.trans
        apply hz'.trans
        change ((Limits.biprod.inl ≫ Limits.biprod.fst :
          IntegralMV.HZ 1 (cellOuter γ) ⟶ _).hom x) = x
        rw [Limits.biprod.inl_fst]
        rfl
      · rintro ⟨z, rfl⟩
        have hi : (IntegralMV.mvI (cellOuter γ) (cellInner γ) 1).hom z =
            (Limits.biprod.inl : IntegralMV.HZ 1 (cellOuter γ) ⟶ _).hom
              ((IntegralMV.mvIncl
                (Set.inter_subset_left : cellOuter γ ∩ cellInner γ ⊆ cellOuter γ) 1).hom z) := by
          have hiMor : IntegralMV.mvI (cellOuter γ) (cellInner γ) 1 =
              IntegralMV.mvIncl Set.inter_subset_left 1 ≫ Limits.biprod.inl := by
            apply Limits.biprod.hom_ext
            · simp [IntegralMV.mvI]
            · simp only [IntegralMV.mvI, Limits.biprod.lift_snd,
                Category.assoc, Limits.biprod.inl_snd]
              simp
              exact hzero.eq_of_tgt _ _
          simpa [ModuleCat.hom_comp] using
            DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hiMor) z
        have hk : (IntegralMV.mvI (cellOuter γ) (cellInner γ) 1).hom z ∈
            LinearMap.ker (IntegralMV.mvJ (cellOuter γ) (cellInner γ) 1).hom := by
          rw [← hexI 1]
          exact ⟨z, rfl⟩
        rw [hi] at hk
        change ((Limits.biprod.inl ≫ IntegralMV.mvJ
          (cellOuter γ) (cellInner γ) 1).hom
            ((IntegralMV.mvIncl
              (Set.inter_subset_left : cellOuter γ ∩ cellInner γ ⊆ cellOuter γ) 1).hom z)) = 0 at hk
        rw [show Limits.biprod.inl ≫ IntegralMV.mvJ
          (cellOuter γ) (cellInner γ) 1 = IntegralMV.mvToX (cellOuter γ) 1 by
            simp [IntegralMV.mvJ]] at hk
        exact hk
  constructor
  · intro x
    obtain ⟨y, hy⟩ := hcore.1 x
    refine ⟨eO.hom.hom y, ?_⟩
    have hge := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hg) (eO.hom.hom y)
    simpa [ModuleCat.hom_comp, hy] using hge.symm
  · apply le_antisymm
    · intro x hx
      have hx' : eO.inv.hom x ∈ LinearMap.ker
          (IntegralMV.mvToX (cellOuter γ) 1).hom := by
        have hge := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hg) x
        simpa [ModuleCat.hom_comp] using hge.trans hx
      rw [hcore.2] at hx'
      obtain ⟨z, hz⟩ := hx'
      refine ⟨eI.hom.hom z, ?_⟩
      have hfe := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hf) z
      have heO : eO.hom.hom (eO.inv.hom x) = x := by simp
      rw [← heO, ← hz]
      simpa [ModuleCat.hom_comp] using hfe.symm
    · rintro x ⟨z, rfl⟩
      have hfe := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hf) (eI.inv.hom z)
      have hz : eI.hom.hom (eI.inv.hom z) = z := by simp
      rw [← hz]
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hfe
      rw [← hfe]
      have hr : (IntegralMV.mvIncl
          (Set.inter_subset_left : cellOuter γ ∩ cellInner γ ⊆ cellOuter γ) 1).hom
          (eI.inv.hom z) ∈ LinearMap.range
            (IntegralMV.mvIncl
              (Set.inter_subset_left : cellOuter γ ∩ cellInner γ ⊆ cellOuter γ) 1).hom :=
        ⟨eI.inv.hom z, rfl⟩
      rw [← hcore.2] at hr
      change (Hmap (cellIncl γ) 1).hom
        ((IntegralMV.mvIncl
          (Set.inter_subset_left : cellOuter γ ∩ cellInner γ ⊆ cellOuter γ) 1 ≫
          eO.hom).hom (eI.inv.hom z)) = 0
      have hge := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hg)
        ((IntegralMV.mvIncl
          (Set.inter_subset_left : cellOuter γ ∩ cellInner γ ⊆ cellOuter γ) 1 ≫
          eO.hom).hom (eI.inv.hom z))
      have hr' := hr
      change (IntegralMV.mvToX (cellOuter γ) 1).hom
        ((IntegralMV.mvIncl
          (Set.inter_subset_left : cellOuter γ ∩ cellInner γ ⊆ cellOuter γ) 1).hom
          (eI.inv.hom z)) = 0 at hr'
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hge
      simp at hge
      simpa using hge.symm.trans hr'
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
lemma X_fwd_aux_conj_continuous : Continuous conjDisk := by
  exact (continuous_star.comp continuous_subtype_val).subtype_mk _

lemma X_fwd_aux_cell_boundary {Y : Type} [TopologicalSpace Y]
    (γ : C(Circle, Y)) (z : Circle) :
    cellDisk γ (circleToDisk z) = cellIncl γ (γ z) := by
  exact Quotient.sound (Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _ (CellRel.boundary z)))

lemma X_fwd_aux_edges (i : Fin P.edgeCount) (t : Set.Icc (0 : ℝ) 1) :
    cellDisk word
        (apm_t97J04_edgePoint 8 i
          t) =
      cellDisk word
        (apm_t97J04_edgePoint 8 (P.pair i)
          (PolygonSurfacePiOne.pairedParameter P.pair P.sign i t)) := by
  rw [show apm_t97J04_edgePoint 8 i t =
      circleToDisk (PolygonSurfacePiOne.edgePointCircle P.edgeCount i t) by
        apply Subtype.ext
        simp [apm_t97J04_edgePoint, circleToDisk,
          PolygonSurfaceHomology.circleToPolygonDisk,
          PolygonSurfacePiOne.edgePointCircle, X_homeomorph_aux_edgeCount],
    show apm_t97J04_edgePoint 8 (P.pair i)
        (PolygonSurfacePiOne.pairedParameter P.pair P.sign i t) =
      circleToDisk (PolygonSurfacePiOne.edgePointCircle P.edgeCount (P.pair i)
        (PolygonSurfacePiOne.pairedParameter P.pair P.sign i t)) by
        apply Subtype.ext
        simp [apm_t97J04_edgePoint, circleToDisk,
          PolygonSurfaceHomology.circleToPolygonDisk,
          PolygonSurfacePiOne.edgePointCircle, X_homeomorph_aux_edgeCount],
    X_fwd_aux_cell_boundary word, X_fwd_aux_cell_boundary word]
  congr 1
  change PolygonSurfaceHomology.polygonBoundaryWedgeLoop P
      (PolygonSurfacePiOne.edgePointCircle P.edgeCount i t) =
    PolygonSurfaceHomology.polygonBoundaryWedgeLoop P
      (PolygonSurfacePiOne.edgePointCircle P.edgeCount (P.pair i)
        (PolygonSurfacePiOne.pairedParameter P.pair P.sign i t))
  rw [PolygonSurfaceHomology.polygonBoundaryWedgeLoop_edgePoint,
    PolygonSurfaceHomology.polygonBoundaryWedgeLoop_edgePoint]
  exact (P.signedWedgeArc_pair i t).symm

lemma X_fwd :
    ∃ f : C(apm_t97J04_X, Xc),
      (∀ z, f (xMk (.inl z)) = cellIncl cLoop (cellDisk word z)) ∧
      (∀ z, f (xMk (.inr z)) = cellDisk cLoop (conjDisk z)) := by
  let F : apm_t97J04_Disk ⊕ apm_t97J04_Disk → Xc := fun x =>
    Sum.elim (fun z => cellIncl cLoop (cellDisk word z))
      (fun z => cellDisk cLoop (conjDisk z)) x
  have hrel : ∀ a b, apm_t97J04_ComplexRel a b → F a = F b := by
    intro a b h
    cases h with
    | a t =>
        apply congrArg (cellIncl cLoop)
        simpa [P, PolygonSurfacePiOne.pairedParameter,
          PolygonSurfacePiOne.reverseIcc] using X_fwd_aux_edges (i := (0 : Fin 8)) t
    | b t =>
        apply congrArg (cellIncl cLoop)
        simpa [P, PolygonSurfacePiOne.pairedParameter,
          PolygonSurfacePiOne.reverseIcc] using X_fwd_aux_edges (i := (1 : Fin 8)) t
    | c t =>
        apply congrArg (cellIncl cLoop)
        simpa [P, PolygonSurfacePiOne.pairedParameter,
          PolygonSurfacePiOne.reverseIcc] using X_fwd_aux_edges (i := (4 : Fin 8)) t
    | d t =>
        apply congrArg (cellIncl cLoop)
        simpa [P, PolygonSurfacePiOne.pairedParameter,
          PolygonSurfacePiOne.reverseIcc] using X_fwd_aux_edges (i := (5 : Fin 8)) t
    | meridian t =>
        dsimp [F]
        have hconj : conjDisk (apm_t97J04_edgePoint 1 0 t) =
            circleToDisk (PolygonSurfacePiOne.circleArc
              (PolygonSurfacePiOne.reverseIcc t)) := by
          rw [X_homeomorph_aux_oneDisk_boundary]
          apply Subtype.ext
          change (starRingEnd ℂ)
              ((AddCircle.toCircle ((t : ℝ) : AddCircle (1 : ℝ)) : Circle) : ℂ) = _
          rw [← Circle.coe_inv_eq_conj,
            ← AddCircle.toCircle_neg (T := (1 : ℝ))]
          congr 2
          simp [PolygonSurfacePiOne.reverseIcc, AddCircle.coe_period]
        rw [hconj, X_fwd_aux_cell_boundary cLoop]
        have hedge : apm_t97J04_edgePoint 8 4 t =
            circleToDisk (PolygonSurfacePiOne.edgePointCircle P.edgeCount cEdge t) := by
          apply Subtype.ext
          simp [apm_t97J04_edgePoint, circleToDisk,
            PolygonSurfaceHomology.circleToPolygonDisk,
            PolygonSurfacePiOne.edgePointCircle, cEdge, X_homeomorph_aux_edgeCount]
        rw [hedge, X_fwd_aux_cell_boundary word, X_homeomorph_aux_word_cEdge]
        rfl
  let f0 : apm_t97J04_X → Xc := Quotient.lift F (by
    intro a b hab
    exact Relation.EqvGen.rec (fun _ _ h => hrel _ _ h)
      (fun _ => rfl) (fun _ _ _ h => h.symm)
      (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂) hab)
  have hf0 : Continuous f0 := by
    apply continuous_coinduced_dom.mpr
    change Continuous F
    simpa only [F, Function.comp_apply] using
      (((cellIncl cLoop).continuous.comp (cellDisk word).continuous).sumElim
        ((cellDisk cLoop).continuous.comp X_fwd_aux_conj_continuous))
  refine ⟨⟨f0, hf0⟩, ?_, ?_⟩ <;> intro z <;> rfl

/-- B1b. Backward map `Xc → X`: on `Sigma = Cell word`, `W`-points go through
`P.skeletonHomeomorphWedge.symm` and the octagon quotient (`P.Rel` generated
classes are `ComplexRel` classes on `inl`), disk points `z ↦ xMk (.inl z)`; on
the `cLoop` disk, `z ↦ xMk (.inr (conjDisk z))`.  Two nested quotient lifts;
both continuous via `continuous_coinduced_dom`. -/
lemma X_bwd_aux_poly_rel {x y : apm_t97J04_Disk}
    (h : Relation.EqvGen P.Rel x y) :
    xMk (.inl x) = xMk (.inl y) := by
  apply Quotient.sound
  have hs : Relation.EqvGen (ConstructionTargets.Surfaces.SurfaceRel true 2) x y := by
    apply (PolygonSurfacePiOne.orientable_eqvGen_iff 2 x y).mp
    exact h
  have hm : ∀ {u v : apm_t97J04_Disk},
      Relation.EqvGen (ConstructionTargets.Surfaces.SurfaceRel true 2) u v →
        Relation.EqvGen apm_t97J04_ComplexRel (.inl u) (.inl v) := by
    intro u v huv
    induction huv with
    | rel u v hrel =>
        rcases hrel with ⟨j, hj, t, h | h⟩
        · rcases h with ⟨rfl, rfl⟩
          interval_cases j
          · exact Relation.EqvGen.rel _ _ (apm_t97J04_ComplexRel.a t)
          · exact Relation.EqvGen.rel _ _ (apm_t97J04_ComplexRel.c t)
        · rcases h with ⟨rfl, rfl⟩
          interval_cases j
          · exact Relation.EqvGen.rel _ _ (apm_t97J04_ComplexRel.b t)
          · exact Relation.EqvGen.rel _ _ (apm_t97J04_ComplexRel.d t)
    | refl u => exact .refl _
    | symm u v _ ih => exact .symm _ _ ih
    | trans u v w _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  exact hm hs

def X_bwd_aux_poly : P.Space → apm_t97J04_X :=
  Quotient.lift (fun z ↦ xMk (.inl z)) (fun _ _ h ↦ X_bwd_aux_poly_rel h)

lemma X_bwd_aux_poly_continuous : Continuous X_bwd_aux_poly := by
  apply continuous_coinduced_dom.mpr
  exact continuous_coinduced_rng.comp continuous_inl

def X_bwd_aux_wedge (w : W) : apm_t97J04_X :=
  X_bwd_aux_poly (P.skeletonHomeomorphWedge.symm w).1

lemma X_bwd_aux_wedge_continuous : Continuous X_bwd_aux_wedge := by
  exact X_bwd_aux_poly_continuous.comp
    (continuous_subtype_val.comp P.skeletonHomeomorphWedge.symm.continuous)

lemma X_bwd_aux_wedge_word (z : Circle) :
    X_bwd_aux_wedge (word z) = xMk (.inl (circleToDisk z)) := by
  simp [X_bwd_aux_wedge, word, PolygonSurfaceHomology.polygonBoundaryWedgeLoop,
    PolygonSurfaceHomology.polygonBoundarySkeletonLoop, X_bwd_aux_poly,
    circleToDisk, PolygonSurfacePiOne.PairingData.quotientMap]

def X_bwd_aux_sigma : Sigma → apm_t97J04_X :=
  Quotient.lift
    (Sum.elim X_bwd_aux_wedge (fun z ↦ xMk (.inl z)))
    (by
      intro a b h
      change Relation.EqvGen (CellRel word) a b at h
      induction h with
      | rel a b h =>
          cases h with
          | boundary z => exact X_bwd_aux_wedge_word z
      | refl a => exact rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

lemma X_bwd_aux_sigma_continuous : Continuous X_bwd_aux_sigma := by
  apply continuous_coinduced_dom.mpr
  apply continuous_sum_dom.mpr
  exact ⟨X_bwd_aux_wedge_continuous,
    continuous_coinduced_rng.comp continuous_inl⟩

lemma X_bwd_aux_wedge_cOrbit (t : Set.Icc (0 : ℝ) 1) :
    X_bwd_aux_wedge (wedgeCircle cOrbit (PolygonSurfacePiOne.circleArc t)) =
      xMk (.inl (apm_t97J04_edgePoint 8 4 (PolygonSurfacePiOne.reverseIcc t))) := by
  rw [show wedgeCircle cOrbit (PolygonSurfacePiOne.circleArc t) =
      P.skeletonHomeomorphWedge
        (P.skeletonArc cEdge (PolygonSurfacePiOne.reverseIcc t)) by
    rw [P.skeletonHomeomorphWedge_skeletonArc,
      P.signedWedgeArc_of_not_sign _ _ X_homeomorph_aux_cEdge_sign,
      PolygonSurfacePiOne.reverseIcc_reverseIcc, cOrbit]]
  simp [X_bwd_aux_wedge, X_bwd_aux_poly,
    PolygonSurfacePiOne.PairingData.skeletonArc,
    PolygonSurfacePiOne.PairingData.quotientMap, cEdge,
    X_homeomorph_aux_edgeCount, apm_t97J04_edgePoint]

lemma X_bwd_aux_conj_boundary (t : Set.Icc (0 : ℝ) 1) :
    conjDisk (circleToDisk (PolygonSurfacePiOne.circleArc t)) =
      apm_t97J04_edgePoint 1 0 (PolygonSurfacePiOne.reverseIcc t) := by
  rw [X_homeomorph_aux_oneDisk_boundary]
  apply Subtype.ext
  change (starRingEnd ℂ) (PolygonSurfacePiOne.circleArc t : ℂ) =
    (PolygonSurfacePiOne.circleArc (PolygonSurfacePiOne.reverseIcc t) : ℂ)
  simp only [PolygonSurfacePiOne.circleArc, AddCircle.toCircle_apply_mk,
    Circle.coe_exp]
  rw [← Complex.exp_conj]
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  norm_num [PolygonSurfacePiOne.reverseIcc]
  rw [show (2 * (Real.pi : ℂ) * (1 - t.1)) * Complex.I =
      ((2 * (Real.pi : ℂ) * t.1) * -Complex.I) + 2 * Real.pi * Complex.I by ring,
    Complex.exp_periodic]
  congr 1
  ring

lemma X_bwd_aux_sigma_cLoop (z : Circle) :
    X_bwd_aux_sigma (cLoop z) =
      xMk (.inr (conjDisk (circleToDisk z))) := by
  obtain ⟨t, rfl⟩ := PolygonSurfacePiOne.surjective_circleArc z
  change X_bwd_aux_wedge
      (wedgeCircle cOrbit (PolygonSurfacePiOne.circleArc t)) = _
  rw [X_bwd_aux_wedge_cOrbit, X_bwd_aux_conj_boundary]
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _
    (apm_t97J04_ComplexRel.meridian (PolygonSurfacePiOne.reverseIcc t))

def X_bwd_aux_map : Xc → apm_t97J04_X :=
  Quotient.lift
    (Sum.elim X_bwd_aux_sigma (fun z ↦ xMk (.inr (conjDisk z))))
    (by
      intro a b h
      change Relation.EqvGen (CellRel cLoop) a b at h
      induction h with
      | rel a b h =>
          cases h with
          | boundary z => exact X_bwd_aux_sigma_cLoop z
      | refl a => exact rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

lemma X_bwd_aux_map_continuous : Continuous X_bwd_aux_map := by
  apply continuous_coinduced_dom.mpr
  apply continuous_sum_dom.mpr
  refine ⟨X_bwd_aux_sigma_continuous, ?_⟩
  exact (continuous_coinduced_rng.comp continuous_inr).comp
    (by
      apply Continuous.subtype_mk
      exact Complex.continuous_conj.comp continuous_subtype_val)

lemma X_bwd :
    ∃ g : C(Xc, apm_t97J04_X),
      (∀ z, g (cellIncl cLoop (cellDisk word z)) = xMk (.inl z)) ∧
      (∀ z, g (cellDisk cLoop z) = xMk (.inr (conjDisk z))) := by
  refine ⟨⟨X_bwd_aux_map, X_bwd_aux_map_continuous⟩, ?_, ?_⟩
  · intro z
    rfl
  · intro z
    rfl

/-- B1c. Every point of `Xc` lies on one of the two disks
(`W`-points are on the `word` boundary: `polygonBoundaryWedgeLoop` is onto;
`cellIncl word (word z) = cellDisk word (circleToDisk z)` by `CellRel`). -/
lemma Xc_points_aux_word_surjective : Function.Surjective word := by
  intro w
  induction w using Quotient.inductionOn with
  | h q =>
      rcases q with ⟨o, z⟩
      induction o using Quotient.inductionOn with
      | h i =>
          obtain ⟨t, ht⟩ := PolygonSurfacePiOne.surjective_circleArc z
          by_cases hs : P.sign i
          · refine ⟨PolygonSurfacePiOne.edgePointCircle P.edgeCount i t, ?_⟩
            change PolygonSurfaceHomology.polygonBoundaryWedgeLoop P
              (PolygonSurfacePiOne.edgePointCircle P.edgeCount i t) =
                PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (P.orbit i) z
            rw [PolygonSurfaceHomology.polygonBoundaryWedgeLoop_edgePoint,
              P.signedWedgeArc_of_sign i t hs, ht]
          · refine ⟨PolygonSurfacePiOne.edgePointCircle P.edgeCount i
                (PolygonSurfacePiOne.reverseIcc t), ?_⟩
            have hs0 : P.sign i = false := Bool.eq_false_of_not_eq_true hs
            change PolygonSurfaceHomology.polygonBoundaryWedgeLoop P
              (PolygonSurfacePiOne.edgePointCircle P.edgeCount i
                (PolygonSurfacePiOne.reverseIcc t)) =
                  PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (P.orbit i) z
            rw [PolygonSurfaceHomology.polygonBoundaryWedgeLoop_edgePoint,
              P.signedWedgeArc_of_not_sign i _ hs0,
              PolygonSurfacePiOne.reverseIcc_reverseIcc, ht]

lemma Xc_points (p : Xc) :
    (∃ z, p = cellIncl cLoop (cellDisk word z)) ∨ ∃ z, p = cellDisk cLoop z := by
  induction p using Quotient.inductionOn with
  | h q =>
      rcases q with s | z
      · left
        induction s using Quotient.inductionOn with
        | h q =>
            rcases q with w | z
            · obtain ⟨u, hu⟩ := Xc_points_aux_word_surjective w
              refine ⟨circleToDisk u, ?_⟩
              change cellIncl cLoop (cellIncl word w) =
                cellIncl cLoop (cellDisk word (circleToDisk u))
              apply congrArg (cellIncl cLoop)
              rw [← hu]
              exact (X_fwd_aux_cell_boundary word u).symm
            · exact ⟨z, rfl⟩
      · right
        exact ⟨z, rfl⟩

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
  simpa [loopClassAt, word,
    PolygonSurfaceHomology.polygonBoundaryIntegerLoopPath,
    PolygonSurfaceHomology.circleIntegerLoopOneClass] using
    (apm_t92J05_genusTwo_W1_boundary_word wedgeCoords
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedge_hcoord)

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
  have hleg :
      wedgeCoords.symm (FreeGroup.of (orbitLabel cOrbit)) =
        PolygonSurfaceHomology.finiteWedgeExplicitLegClassAtBase P cOrbit := by
    apply wedgeCoords.injective
    rw [wedgeCoords.apply_symm_apply]
    exact
      apm_t92J05_genusTwo_polygon_attach_specialization_aux_outer_word_aux_outer_equiv_aux_wedge_hcoord
        cOrbit |>.symm
  rw [hleg]
  rfl

/-- B3'. Edge 4 lies in handle 1 at position 0: label `(1, false) ↦ 2`
(`orientableOrbitEquiv`, `finTwoEquiv`, `finProdFinEquiv`). -/
lemma cOrbit_label : orbitLabel cOrbit = 2 := by
  rfl

/-- B4. Two successive one-relator quotients (pure group theory). -/
lemma two_step_quotient {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (a b : G)
    (hkf : f.ker = Subgroup.normalClosure {a})
    (hkg : g.ker = Subgroup.normalClosure {f b}) :
    Nonempty (K ≃* G ⧸ Subgroup.normalClosure ({a, b} : Set G)) := by
  let F : G →* K := g.comp f
  have hF : Function.Surjective F := hg.comp hf
  have hker : F.ker = Subgroup.normalClosure ({a, b} : Set G) := by
    apply le_antisymm
    · intro x hx
      have hfx : f x ∈ Subgroup.normalClosure ({f b} : Set H) := by
        rw [← hkg]
        exact (MonoidHom.mem_ker.mpr hx)
      have himage : Subgroup.map f (Subgroup.normalClosure ({b} : Set G)) =
          Subgroup.normalClosure ({f b} : Set H) := by
        rw [Subgroup.map_normalClosure _ _ hf]
        congr 1
        ext z
        simp
      rw [← himage] at hfx
      obtain ⟨y, hy, hfy⟩ := Subgroup.mem_map.mp hfx
      have hxy : x * y⁻¹ ∈ Subgroup.normalClosure ({a} : Set G) := by
        rw [← hkf, MonoidHom.mem_ker]
        rw [map_mul, map_inv, hfy]
        simp
      have ha : Subgroup.normalClosure ({a} : Set G) ≤
          Subgroup.normalClosure ({a, b} : Set G) :=
        Subgroup.normalClosure_mono (by simp)
      have hb : Subgroup.normalClosure ({b} : Set G) ≤
          Subgroup.normalClosure ({a, b} : Set G) :=
        Subgroup.normalClosure_mono (by simp)
      have := Subgroup.mul_mem _ (ha hxy) (hb hy)
      simpa [mul_assoc] using this
    · apply Subgroup.normalClosure_le_normal
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with ha | hb
      · apply MonoidHom.mem_ker.mpr
        subst z
        change g (f a) = 1
        have : f a = 1 := MonoidHom.mem_ker.mp (hkf.symm ▸
          Subgroup.subset_normalClosure (Set.mem_singleton a))
        simp [this]
      · apply MonoidHom.mem_ker.mpr
        subst z
        change g (f b) = 1
        exact MonoidHom.mem_ker.mp (hkg.symm ▸
          Subgroup.subset_normalClosure (Set.mem_singleton (f b)))
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective F hF).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

/-- B5. Tietze: kill `c` (generator 2) in the genus-two group; generators
`a, b, d` ↦ `0, 1, 2`.  The relator may enter up to conjugacy/inversion. -/
def presentation_algebra_aux_f : Fin 4 → apm_t97J04_piOne
  := ![PresentedGroup.of 0, PresentedGroup.of 1, 1, PresentedGroup.of 2]

lemma presentation_algebra_aux_genus :
    FreeGroup.lift presentation_algebra_aux_f apm_t92J05_genusTwoRelator = 1 := by
  simp only [apm_t92J05_genusTwoRelator, apm_t92J05_commutator, map_mul,
    map_inv, FreeGroup.lift_apply_of, presentation_algebra_aux_f,
    Matrix.cons_val_zero, Matrix.cons_val_one, inv_one, mul_one]
  exact PresentedGroup.one_of_mem (by simp [apm_t97J04_relator])

lemma presentation_algebra_aux_r (r : FreeGroup (Fin 4))
    (hr : IsConj r apm_t92J05_genusTwoRelator ∨
      IsConj r apm_t92J05_genusTwoRelator⁻¹) :
    FreeGroup.lift presentation_algebra_aux_f r = 1 := by
  rcases hr with hr | hr
  · have h := (FreeGroup.lift presentation_algebra_aux_f).map_isConj hr
    rw [presentation_algebra_aux_genus] at h
    exact isConj_one_left.mp h
  · have h := (FreeGroup.lift presentation_algebra_aux_f).map_isConj hr
    simp only [map_inv, presentation_algebra_aux_genus, inv_one] at h
    exact isConj_one_left.mp h

lemma presentation_algebra (r : FreeGroup (Fin 4))
    (hr : IsConj r apm_t92J05_genusTwoRelator ∨
      IsConj r apm_t92J05_genusTwoRelator⁻¹) :
    Nonempty (FreeGroup (Fin 4) ⧸
        Subgroup.normalClosure ({r, FreeGroup.of 2} : Set (FreeGroup (Fin 4))) ≃*
      apm_t97J04_piOne) := by
  let N := Subgroup.normalClosure ({r, FreeGroup.of 2} : Set (FreeGroup (Fin 4)))
  let q : FreeGroup (Fin 4) →* (FreeGroup (Fin 4) ⧸ N) := QuotientGroup.mk' N
  let F : FreeGroup (Fin 4) →* apm_t97J04_piOne :=
    FreeGroup.lift presentation_algebra_aux_f
  have hN : N ≤ F.ker := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact MonoidHom.mem_ker.mpr (presentation_algebra_aux_r _ hr)
    · exact MonoidHom.mem_ker.mpr (by simp [F, presentation_algebra_aux_f])
  let phi : (FreeGroup (Fin 4) ⧸ N) →* apm_t97J04_piOne :=
    QuotientGroup.lift N F hN
  let e : Fin 3 → (FreeGroup (Fin 4) ⧸ N) :=
    ![q (FreeGroup.of 0), q (FreeGroup.of 1), q (FreeGroup.of 3)]
  have he : ∀ x ∈ ({apm_t97J04_relator} : Set (FreeGroup (Fin 3))),
      FreeGroup.lift e x = 1 := by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    change q (apm_t92J05_commutator 0 1) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    have hrN : r ∈ N := Subgroup.subset_normalClosure (by simp)
    have hgen : apm_t92J05_genusTwoRelator ∈ N := by
      rcases hr with hr | hr
      · rcases isConj_iff.mp hr with ⟨g, hg⟩
        rw [← hg]
        exact Subgroup.normalClosure_normal.conj_mem _ hrN g
      · rcases isConj_iff.mp hr with ⟨g, hg⟩
        have hi : apm_t92J05_genusTwoRelator⁻¹ ∈ N := by
          rw [← hg]
          exact Subgroup.normalClosure_normal.conj_mem _ hrN g
        exact N.inv_mem hi
    have hc : FreeGroup.of (2 : Fin 4) ∈ N :=
      Subgroup.subset_normalClosure (by simp)
    have hcmt : apm_t92J05_commutator 2 3 ∈ N := by
      unfold apm_t92J05_commutator
      simpa only [mul_assoc] using N.mul_mem hc
        (Subgroup.normalClosure_normal.conj_mem _ (N.inv_mem hc) (FreeGroup.of 3))
    have := N.mul_mem hgen (N.inv_mem hcmt)
    simpa [apm_t92J05_genusTwoRelator] using this
  let psi : apm_t97J04_piOne →* (FreeGroup (Fin 4) ⧸ N) :=
    PresentedGroup.toGroup he
  have hpf : psi.comp phi = MonoidHom.id (FreeGroup (Fin 4) ⧸ N) := by
    apply QuotientGroup.monoidHom_ext
    ext i
    fin_cases i
    · simp [psi, phi, e, F, presentation_algebra_aux_f, q]
    · simp [psi, phi, e, F, presentation_algebra_aux_f, q]
    · simp only [MonoidHom.comp_apply, QuotientGroup.lift_mk', FreeGroup.lift_apply_of,
        presentation_algebra_aux_f, Matrix.cons_val_one, map_one, MonoidHom.id_apply]
      exact ((QuotientGroup.eq_one_iff _).mpr
        (Subgroup.subset_normalClosure (by simp))).symm
    · simp [psi, phi, e, F, presentation_algebra_aux_f, q]
  have hfp : phi.comp psi = MonoidHom.id apm_t97J04_piOne := by
    apply PresentedGroup.ext
    intro i
    fin_cases i <;> simp [psi, phi, e, F, presentation_algebra_aux_f, q]
  refine ⟨MulEquiv.ofBijective phi ?_⟩
  constructor
  · intro x y hxy
    have hleft : psi (phi x) = psi (phi y) := congrArg psi hxy
    have hx := DFunLike.congr_fun hpf x
    have hy := DFunLike.congr_fun hpf y
    change psi (phi x) = x at hx
    change psi (phi y) = y at hy
    exact hx.symm.trans (hleft.trans hy)
  · intro y
    refine ⟨psi y, ?_⟩
    exact DFunLike.congr_fun hfp y

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
    (cell_pathConnected word hA3w hA4w) cell_piOne_aux_hequiv_bijective
    cell_piOne_aux_homotopic_conj (cell_piOne_aux_overlap_generator word hA3w)
  obtain ⟨hgs, hgk⟩ := cell_piOne cLoop sBase cLoop_one hA1c hA2c hA3c hA4c hA5c
    (cell_pathConnected cLoop hA3c hA4c) cell_piOne_aux_hequiv_bijective
    cell_piOne_aux_homotopic_conj (cell_piOne_aux_overlap_generator cLoop hA3c)
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
    (cell_H1_aux_inner_zero word hA2w) (cell_H1_aux_mv0_injective word hA3w hA4w hA2w)
    (cell_H1_aux_transport word hA3w hA4w hA5w)
  have hA8c := cell_H1 cLoop hA1c hA2c hA3c hA4c hA5c
    (cell_H1_aux_inner_zero cLoop hA2c) (cell_H1_aux_mv0_injective cLoop hA3c hA4c hA2c)
    (cell_H1_aux_transport cLoop hA3c hA4c hA5c)
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
