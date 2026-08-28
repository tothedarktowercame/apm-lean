import ConstructionTargets.TwoOpenDescentQuotient
import ConstructionTargets.HomotopySquareStripEndpoints

/-!
# Identity law for quotient two-open descent
-/

open Set CategoryTheory
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.TwoOpenDescentFunctorLaws

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.HomotopySquareUniformGrid
open ConstructionTargets.HomotopySquareStripEndpoints
open ConstructionTargets.TwoOpenDescentQuotient

variable {X : Type*} [TopologicalSpace X]
variable {U V : Set X}
variable {C : Type*} [Category C]

/-- An identity morphism between mutually transported objects cancels the two
endpoint transports, independently of the proofs used to construct them. -/
theorem eqToHom_id_eqToHom_cancel {A B : C} (h : A = B) (h' : B = A) :
    eqToHom h ≫ 𝟙 B ≫ eqToHom h' = 𝟙 A := by
  subst B
  simp

/-- The one-segment subdivision of a constant path in a selected cover
member. -/
def reflSubdivision (b : Bool) (z : X) (hz : z ∈ twoChart U V b) :
    PathTwoOpenSubdivision (Path.refl z) U V where
  n := 0
  vertex := gridCoord 1 (by omega)
  side := fun _ ↦ b
  vertex_zero := gridCoord_zero 1 (by omega)
  vertex_last := gridCoord_last 1 (by omega)
  monotone_vertex := monotone_gridCoord 1 (by omega)
  segment_mem := by
    intro k t ht
    simpa [Path.refl, Path.subpath] using hz

@[simp] theorem reflSubdivision_n (b : Bool) (z : X)
    (hz : z ∈ twoChart U V b) : (reflSubdivision b z hz).n = 0 := rfl

theorem evaluate_reflSubdivision
    (D : @TwoOpenDescentDatum X _ U V C _)
    (b : Bool) (z : X) (hz : z ∈ twoChart U V b) :
    D.evaluate (reflSubdivision b z hz) = 𝟙 (D.obj z) := by
  have hm : D.mappedPiece (reflSubdivision b z hz) 0 = 𝟙 (D.obj z) := by
    change D.mapPath b _ _ = 𝟙 (D.obj z)
    calc
      D.mapPath b ((reflSubdivision b z hz).piece 0) _ =
          D.mapPath b (Path.refl z) (fun _ ↦ hz) :=
        mapPath_eq_of_path_eq D
          (show (reflSubdivision b z hz).piece 0 = Path.refl z by
        apply Path.ext
        funext t
        change z = z
        rfl) _ _
      _ = 𝟙 (D.obj z) := mapPath_refl D b z hz
  simp only [TwoOpenDescentDatum.evaluate]
  rw [TwoOpenDescentDatum.composeFin_succ]
  simp only [reflSubdivision_n]
  rw [TwoOpenDescentDatum.composeFin_zero]
  change eqToHom _ ≫ ((𝟙 _ ≫
    D.mappedPiece (reflSubdivision b z hz) 0) ≫ eqToHom _) = _
  rw [Category.id_comp, hm]
  apply eqToHom_id_eqToHom_cancel

/-- `quotientEvaluation` sends the identity path class to the categorical
identity. -/
theorem quotientEvaluation_refl (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (D : @TwoOpenDescentDatum X _ U V C _) (z : X) :
    quotientEvaluation hU hV hcover D
        (Path.Homotopic.Quotient.refl z) = 𝟙 (D.obj z) := by
  have hz : z ∈ U ∨ z ∈ V := by
    have : z ∈ U ∪ V := by rw [hcover]; trivial
    simpa only [Set.mem_union] using this
  rcases hz with hzU | hzV
  · have hz' : z ∈ twoChart U V true := by simpa [twoChart]
    change quotientEvaluation hU hV hcover D
      (Path.Homotopic.Quotient.mk (Path.refl z)) = _
    rw [quotientEvaluation_mk hU hV hcover D (Path.refl z)
      (reflSubdivision true z hz')]
    exact evaluate_reflSubdivision D true z hz'
  · have hz' : z ∈ twoChart U V false := by simpa [twoChart]
    change quotientEvaluation hU hV hcover D
      (Path.Homotopic.Quotient.mk (Path.refl z)) = _
    rw [quotientEvaluation_mk hU hV hcover D (Path.refl z)
      (reflSubdivision false z hz')]
    exact evaluate_reflSubdivision D false z hz'

#print axioms reflSubdivision
#print axioms evaluate_reflSubdivision
#print axioms quotientEvaluation_refl

end ConstructionTargets.TwoOpenDescentFunctorLaws
