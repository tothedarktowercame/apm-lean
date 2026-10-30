import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.LefschetzCompactPolyhedron
import ConstructionTargets.ProjectivePlaneWedgeRationalHomology
import ConstructionTargets.FiniteTriangulation
import ConstructionTargets.RealProjectivePlaneTriangulation
import ConstructionTargets.LefschetzFixedPoint

/-! # APM t99A03: fixed points on a wedge and a connected sum -/

open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.StatementSurfaceModels
open ConstructionTargets.Surfaces
open ConstructionTargets.RationalLefschetz

noncomputable section

namespace T99A03

/-- The common point in the wedge of two projective planes. -/
def twoWedgePoint : ProjectivePlaneWedge :=
  quotientMap (surfacePoint false 1) (surfacePoint false 1)
    (Sum.inl (surfacePoint false 1))

/-- Four copies of `ℝP²`, joined at one point. -/
abbrev FourProjectivePlanesWedge := Wedge twoWedgePoint twoWedgePoint

/-- The connected sum of four copies of `ℝP²`. -/
abbrev FourProjectivePlanesConnectedSum := Surface false 4

/-- The connected sum of three copies of `ℝP²`, used as the base of the
double cover producing the fixed-point-free map. -/
abbrev ThreeProjectivePlanesConnectedSum := Surface false 3

end T99A03

/-- **LIBRARY.** Every self-map of the fourfold projective-plane wedge has
rational Lefschetz number one. -/
theorem t99A03_wedge_lefschetz_number :
    ∀ f : C(T99A03.FourProjectivePlanesWedge,
        T99A03.FourProjectivePlanesWedge), HasLefschetzNumber f 1 := by
  intro f
  open ConstructionTargets.ProjectivePlaneWedgeRationalHomology in
    letI : PathConnectedSpace
        ConstructionTargets.StatementSurfaceModels.RealProjectivePlane :=
      realProjectivePlane_pathConnected
    let hH : RationallyPointlike T99A03.FourProjectivePlanesWedge :=
      wedge_rationallyPointlike _ _
        projectivePlaneWedge_rationallyPointlike
        projectivePlaneWedge_rationallyPointlike
        projectivePlaneWedge_pointedNeighbourhood
        projectivePlaneWedge_pointedNeighbourhood
    exact lefschetzNumber_one_of_rationallyPointlike hH f

/-- **LIBRARY (triangulation).** The space admits a finite geometric
triangulation, as required by
`ConstructionTargets.LefschetzCompactPolyhedron.fixedPointOfNonzeroLefschetz`.
(claude-14, 2026-10-28; statement as recorded in that module's blueprint.) -/
theorem t99A03_fourProjectivePlanesWedge_isFinitePolyhedron :
    ConstructionTargets.LefschetzCompactPolyhedron.IsFinitePolyhedron
      T99A03.FourProjectivePlanesWedge := by
  open ConstructionTargets.FiniteTriangulation in
    have htwo := wedge_isFinitePolyhedron_of_vertexTriangulations _ _
        ConstructionTargets.RealProjectivePlaneTriangulation.realProjectivePlane_hasFiniteVertexTriangulation
        ConstructionTargets.RealProjectivePlaneTriangulation.realProjectivePlane_hasFiniteVertexTriangulation
    exact (wedge_isFinitePolyhedron_of_vertexTriangulations _ _
      htwo htwo).isFinitePolyhedron

/-- **LIBRARY.** The Lefschetz fixed-point implication, specialized to the
finite projective-plane wedge.  Its homology calculation is supplied as a
hypothesis so this foundation can be developed in parallel with that
calculation. -/
theorem t99A03_wedge_fixed_point_of_lefschetz
    (hL : ∀ f : C(T99A03.FourProjectivePlanesWedge,
        T99A03.FourProjectivePlanesWedge), HasLefschetzNumber f 1) :
    ∀ f : C(T99A03.FourProjectivePlanesWedge,
        T99A03.FourProjectivePlanesWedge), ∃ x, f x = x := by
  intro f
  exact ConstructionTargets.LefschetzFixedPoint.fixedPointOfNonzeroLefschetz
    t99A03_fourProjectivePlanesWedge_isFinitePolyhedron f (hL f) one_ne_zero

/-! ### A fixed-point-free self-map of `N₄` (claude-14, 2026-10-30)

The earlier route (a double cover `N₄ → N₃` and its deck involution) needs a
covering map out of a polygon quotient. A shorter one: in the model `Surface false 4`
(the 8-gon `a₁a₁a₂a₂a₃a₃a₄a₄`), a map `h : N₄ → S¹` winding once along `a₁`, once
backwards along `a₂`, and constant on `a₃, a₄`, composed after the `a₁` edge loop
`γ : S¹ → N₄`, is the rotation `z ↦ -z`. Then `f = γ ∘ h` has no fixed point:
`f x = x` gives `h x = h (γ (h x)) = -h x`. -/

/-- The boundary angle of the circle map: a continuous `φ : S¹ → ℝ` with the
prescribed values on the eight arcs (arc `j` is `Circle.exp (2π(j + t)/8)`,
`t ∈ [0, 1]`). Take the 1-periodic piecewise-linear `ψ : ℝ → ℝ` with these values on
`[j/8, (j+1)/8]` (it is `0` at both ends of a period, so periodic extension is
continuous) and descend it along `t ↦ Circle.exp (2πt)`
(`Function.Periodic.lift`, or `AddCircle.homeomorphCircle'`). -/
theorem t99A03_aux_boundaryAngle :
    ∃ φ : C(Circle, ℝ), ∀ t : Set.Icc (0 : ℝ) 1,
      φ (Circle.exp (2 * Real.pi * (0 + t.1) / 8)) = 2 * Real.pi * t.1 ∧
      φ (Circle.exp (2 * Real.pi * (1 + t.1) / 8)) = 2 * Real.pi + 2 * Real.pi * t.1 ∧
      φ (Circle.exp (2 * Real.pi * (2 + t.1) / 8)) = 4 * Real.pi - 2 * Real.pi * t.1 ∧
      φ (Circle.exp (2 * Real.pi * (3 + t.1) / 8)) = 2 * Real.pi - 2 * Real.pi * t.1 ∧
      ∀ j : ℕ, 4 ≤ j → j < 8 → φ (Circle.exp (2 * Real.pi * (j + t.1) / 8)) = 0 := by
  sorry

/-- The circle map. Take `φ` from `t99A03_aux_boundaryAngle` (`edgePoint 8 j t` is
the boundary point `Circle.exp (2π(j + t)/8)`, by `Circle.coe_exp`). Extend
radially, `Φ z = ‖z‖ * φ (z / ‖z‖)` (`0` at `z = 0`) (continuous at the centre since `φ` is bounded), and
set `h = Circle.exp (Φ + π)`. Paired arcs `2j, 2j+1` (same parameter) get equal
values modulo `2π`, so `h` respects `SurfaceRel false 4` and descends through the
coinduced topology (`Quotient.lift`, `continuous_coinduced_dom`). On arc 0,
`h = Circle.exp (2πs + π)`. -/
theorem t99A03_aux_circleMap :
    ∃ h : C(T99A03.FourProjectivePlanesConnectedSum, Circle),
      ∀ t : Set.Icc (0 : ℝ) 1,
        h (surfaceQuotient false 4 (edgePoint 8 0 t)) =
          Circle.exp (2 * Real.pi * t.1 + Real.pi) := by
  sorry

/-- The edge loop of `a₁`. The path `t ↦ surfaceQuotient (edgePoint 8 0 t)` on
`[0, 1]` is closed: its endpoints are polygon vertices `0` and `1`, identified by
`SurfaceRel false 4` at `j = 0, t = 0` (edge 1 starts where edge 0 ends). Descend it
along the quotient map `[0, 1] → Circle`, `t ↦ Circle.exp (2πt)` (a closed map from a
compact space onto a Hausdorff space, so a quotient map identifying only `0 ~ 1`). -/
theorem t99A03_aux_edgeLoop :
    ∃ γ : C(Circle, T99A03.FourProjectivePlanesConnectedSum),
      ∀ t : Set.Icc (0 : ℝ) 1,
        γ (Circle.exp (2 * Real.pi * t.1)) = surfaceQuotient false 4 (edgePoint 8 0 t) := by
  sorry

/-- Every point of the circle is `Circle.exp (2πt)` for some `t ∈ [0, 1]`: take
`t = toIcoMod` of the argument divided by `2π` (`Circle.periodic_exp`,
`Circle.exp_arg` or the surjectivity of `Circle.exp`). -/
-- BEGIN SEAT AREA
theorem t99A03_aux_circle_param (z : Circle) :
    ∃ t : Set.Icc (0 : ℝ) 1, Circle.exp (2 * Real.pi * t.1) = z := by
  by_cases h : 0 ≤ Complex.arg (z : ℂ)
  · let t : ℝ := Complex.arg (z : ℂ) / (2 * Real.pi)
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg h (by positivity)
      · apply (div_le_one (by positivity : (0 : ℝ) < 2 * Real.pi)).2
        have hz := Complex.arg_le_pi (z : ℂ)
        linarith [Real.pi_pos]
    refine ⟨⟨t, ht⟩, ?_⟩
    convert Circle.exp_arg z using 1
    · dsimp [t]
      field_simp
  · let t : ℝ := (Complex.arg (z : ℂ) + 2 * Real.pi) / (2 * Real.pi)
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · apply div_nonneg
        · have hz := Complex.neg_pi_lt_arg (z : ℂ)
          linarith [Real.pi_pos]
        · positivity
      · apply (div_le_one (by positivity : (0 : ℝ) < 2 * Real.pi)).2
        exact add_le_of_nonpos_left (le_of_not_ge h)
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [show 2 * Real.pi * t = Complex.arg (z : ℂ) + 2 * Real.pi by
      dsimp [t]
      field_simp]
    rw [Circle.exp_add_two_pi, Circle.exp_arg]
-- END SEAT AREA

theorem t99A03_exists_fixedPointFree_N4 :
    ∃ f : C(T99A03.FourProjectivePlanesConnectedSum,
        T99A03.FourProjectivePlanesConnectedSum), ∀ x, f x ≠ x := by
  obtain ⟨h, hh⟩ := t99A03_aux_circleMap
  obtain ⟨γ, hγ⟩ := t99A03_aux_edgeLoop
  refine ⟨γ.comp h, fun x hx => ?_⟩
  obtain ⟨t, ht⟩ := t99A03_aux_circle_param (h x)
  have hfix : h (γ (h x)) = h x := congrArg h hx
  rw [← ht, hγ t, hh t, Circle.exp_add] at hfix
  have hpi : Circle.exp Real.pi = 1 := by
    have := congrArg (fun w => (Circle.exp (2 * Real.pi * t.1))⁻¹ * w) hfix
    simpa using this
  have hc := congrArg (fun w : Circle => (w : ℂ)) hpi
  simp [Circle.coe_exp, Complex.exp_pi_mul_I] at hc
  norm_num at hc

/-- A nonidentity deck transformation of a connected cover has no fixed
point.  This is the generic uniqueness-of-lifts step from the old stand-in. -/
theorem t99A03_deckTransformation_fixedPointFree
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [ConnectedSpace E] (p : E → B) (hp : IsCoveringMap p)
    (τ : E ≃ₜ E) (hdeck : p ∘ τ = p)
    (hne : τ ≠ Homeomorph.refl E) : ∀ x : E, τ x ≠ x := by
  intro x hx
  apply hne
  have hfun : (τ : E → E) = id :=
    hp.eq_of_comp_eq τ.continuous continuous_id (by simpa using hdeck) x
      (by simpa using hx)
  exact Homeomorph.ext (fun y ↦ by simpa using congrFun hfun y)

theorem apm_t99a03 :
    (∀ f : C(T99A03.FourProjectivePlanesWedge,
        T99A03.FourProjectivePlanesWedge), ∃ x, f x = x) ∧
    (∃ f : C(T99A03.FourProjectivePlanesConnectedSum,
        T99A03.FourProjectivePlanesConnectedSum), ∀ x, f x ≠ x) := by
  constructor
  · exact t99A03_wedge_fixed_point_of_lefschetz
      t99A03_wedge_lefschetz_number
  · exact t99A03_exists_fixedPointFree_N4

#print axioms apm_t99a03
