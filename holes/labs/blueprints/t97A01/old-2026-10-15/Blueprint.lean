import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.Surfaces
import ConstructionTargets.PolygonSurfacePiOne
import ConstructionTargets.PolygonRadialOpenCoverPackages
import ConstructionTargets.PolygonOverlapHomotopyEquivCircle
import ConstructionTargets.PolygonBoundaryThreeLoopHomeomorphisms
import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.FiniteCircleWedgeFundamentalGroup
import ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout

/-!
# Blueprint for APM t97A01

The definitions and final theorem type below are the frozen ones from
`problems/t97A01/lean/Main.lean`.  The two missing theorems are deliberately
large library boundaries: the polygon Mayer--Vietoris computation and the
polygon boundary-word van Kampen computation.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t97a01_Disk := Metric.closedBall (0 : ℂ) 1

def apm_t97a01_edgePoint (j : Fin 6) (t : Set.Icc (0 : ℝ) 1) :
    apm_t97a01_Disk :=
  ⟨Complex.exp (Complex.I * (2 * Real.pi * ((j : ℝ) + t.1) / 6)), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    simp⟩

inductive apm_t97a01_RelX : apm_t97a01_Disk → apm_t97a01_Disk → Prop
  | a (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelX (apm_t97a01_edgePoint 0 t) (apm_t97a01_edgePoint 1 t)
  | b (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelX (apm_t97a01_edgePoint 2 t) (apm_t97a01_edgePoint 3 t)
  | c (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelX (apm_t97a01_edgePoint 4 t) (apm_t97a01_edgePoint 5 t)

inductive apm_t97a01_RelTorusRP2 :
    apm_t97a01_Disk → apm_t97a01_Disk → Prop
  | a (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelTorusRP2 (apm_t97a01_edgePoint 0 t)
        (apm_t97a01_edgePoint 2 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩)
  | b (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelTorusRP2 (apm_t97a01_edgePoint 1 t)
        (apm_t97a01_edgePoint 3 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩)
  | c (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelTorusRP2 (apm_t97a01_edgePoint 4 t)
        (apm_t97a01_edgePoint 5 t)

def apm_t97a01_X := Quotient (Relation.EqvGen.setoid apm_t97a01_RelX)
def apm_t97a01_TorusRP2 :=
  Quotient (Relation.EqvGen.setoid apm_t97a01_RelTorusRP2)

noncomputable instance : TopologicalSpace apm_t97a01_X :=
  TopologicalSpace.coinduced (fun x : apm_t97a01_Disk ↦ Quotient.mk _ x) inferInstance

noncomputable instance : TopologicalSpace apm_t97a01_TorusRP2 :=
  TopologicalSpace.coinduced (fun x : apm_t97a01_Disk ↦ Quotient.mk _ x) inferInstance

abbrev apm_t97a01_H (k : ℕ) (Y : Type) [TopologicalSpace Y] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y))

def apm_t97a01_baseTorusRP2 : apm_t97a01_TorusRP2 :=
  Quotient.mk _ (0 : apm_t97a01_Disk)

def apm_t97a01_relator : FreeGroup (Fin 3) :=
  (.of 0) * (.of 1) * (.of 0)⁻¹ * (.of 1)⁻¹ * (.of 2) * (.of 2)

/-- LIBRARY: the integral singular homology of both literal six-edge polygon
quotients.  The proof must construct the radial two-open cover, identify its
outer piece with a three-circle wedge and its overlap with a circle, and show
that the Mayer--Vietoris map is respectively `(2,2,2)` and `(0,0,2)`.
The conclusion is bundled so that this common geometric comparison is proved
once rather than independently for the two presentations. -/
theorem apm_t97a01_polygon_singular_homology :
    (Nonempty (apm_t97a01_H 0 apm_t97a01_X ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (apm_t97a01_H 1 apm_t97a01_X ≅
        ModuleCat.of ℤ (ℤ × ℤ × ZMod 2)) ∧
      ∀ k : ℕ, 2 ≤ k → Limits.IsZero (apm_t97a01_H k apm_t97a01_X)) ∧
    (Nonempty (apm_t97a01_H 0 apm_t97a01_TorusRP2 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (apm_t97a01_H 1 apm_t97a01_TorusRP2 ≅
        ModuleCat.of ℤ (ℤ × ℤ × ZMod 2)) ∧
      ∀ k : ℕ, 2 ≤ k → Limits.IsZero
        (apm_t97a01_H k apm_t97a01_TorusRP2)) := by
  sorry

/-- LIBRARY: Seifert--van Kampen for the literal torus-crosscap polygon,
including the path-level calculation that the attaching circle reads
`a b a⁻¹ b⁻¹ c c`. -/
theorem apm_t97a01_torusRP2_fundamentalGroup :
    Nonempty
      (FundamentalGroup apm_t97a01_TorusRP2 apm_t97a01_baseTorusRP2 ≃*
        PresentedGroup ({apm_t97a01_relator} : Set (FreeGroup (Fin 3)))) := by
  sorry

theorem apm_t97a01 :
    Nonempty (apm_t97a01_H 0 apm_t97a01_X ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97a01_H 1 apm_t97a01_X ≅
      ModuleCat.of ℤ (ℤ × ℤ × ZMod 2)) ∧
    (∀ k : ℕ, 2 ≤ k → Limits.IsZero (apm_t97a01_H k apm_t97a01_X)) ∧
    Nonempty (apm_t97a01_H 0 apm_t97a01_TorusRP2 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97a01_H 1 apm_t97a01_TorusRP2 ≅
      ModuleCat.of ℤ (ℤ × ℤ × ZMod 2)) ∧
    (∀ k : ℕ, 2 ≤ k → Limits.IsZero (apm_t97a01_H k apm_t97a01_TorusRP2)) ∧
    Nonempty
      (FundamentalGroup apm_t97a01_TorusRP2 apm_t97a01_baseTorusRP2 ≃*
        PresentedGroup ({apm_t97a01_relator} : Set (FreeGroup (Fin 3)))) := by
  rcases apm_t97a01_polygon_singular_homology with
    ⟨⟨hX0, hX1, hXhi⟩, hT0, hT1, hThi⟩
  exact ⟨hX0, hX1, hXhi, hT0, hT1, hThi,
    apm_t97a01_torusRP2_fundamentalGroup⟩

#print axioms apm_t97a01
