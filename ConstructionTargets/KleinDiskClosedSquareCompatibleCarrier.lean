import ConstructionTargets.KleinSquareEqvGenCasesIff
import ConstructionTargets.KleinDiskSquareCarrier

namespace ConstructionTargets.KleinDiskClosedSquareCompatibleCarrier

open Set
open ConstructionTargets.Surfaces
open KleinPlaneActionSquareOrbitClassification
open KleinSquareEdgeOrientation

abbrev ClosedSquare := {p : ℝ × ℝ // InSquare p}

def zeroIcc : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩

def oneIcc : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩

theorem disk_edge_zero_one_endpoint :
    edgePoint 4 0 oneIcc = edgePoint 4 1 zeroIcc := by
  apply Subtype.ext
  simp only [edgePoint, oneIcc, zeroIcc]
  congr 2
  ring_nf

theorem square_edge_zero_one_endpoint_ne :
    squareEdge 0 oneIcc ≠ squareEdge 1 zeroIcc := by
  norm_num [squareEdge, zeroIcc, oneIcc]

/-- The first two coordinate formulas demanded of the proposed carrier are
already inconsistent at their common disk endpoint.  Consequently no function,
and hence no homeomorphism, can satisfy all four corresponding edge formulas. -/
theorem no_carrier_with_required_boundary_formulas :
    ¬ ∃ h : Disk → ClosedSquare,
      (∀ t : Set.Icc (0 : ℝ) 1,
        (h (edgePoint 4 0 t)).1 = squareEdge 0 t) ∧
      (∀ t : Set.Icc (0 : ℝ) 1,
        (h (edgePoint 4 1 t)).1 = squareEdge 1 t) ∧
      (∀ t : Set.Icc (0 : ℝ) 1,
        (h (edgePoint 4 2 t)).1 = squareEdge 2 t) ∧
      (∀ t : Set.Icc (0 : ℝ) 1,
        (h (edgePoint 4 3 t)).1 = squareEdge 3 t) := by
  rintro ⟨h, h0, h1, -, -⟩
  apply square_edge_zero_one_endpoint_ne
  calc
    squareEdge 0 oneIcc = (h (edgePoint 4 0 oneIcc)).1 := (h0 oneIcc).symm
    _ = (h (edgePoint 4 1 zeroIcc)).1 := by rw [disk_edge_zero_one_endpoint]
    _ = squareEdge 1 zeroIcc := h1 zeroIcc

end ConstructionTargets.KleinDiskClosedSquareCompatibleCarrier
