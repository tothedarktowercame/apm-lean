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
-- BEGIN SEAT AREA
private def t99A03_aux_boundaryAngle_g (x : ℝ) : ℝ :=
  max 0 (4 * Real.pi - 8 * |x - Real.pi / 2|)

private lemma t99A03_aux_boundaryAngle_g_continuous :
    Continuous t99A03_aux_boundaryAngle_g := by
  unfold t99A03_aux_boundaryAngle_g
  fun_prop

private lemma t99A03_aux_boundaryAngle_g_end :
    t99A03_aux_boundaryAngle_g 0 =
      t99A03_aux_boundaryAngle_g (2 * Real.pi) := by
  unfold t99A03_aux_boundaryAngle_g
  have hp : 0 < Real.pi := Real.pi_pos
  rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
  rw [max_eq_left (by nlinarith), max_eq_left (by nlinarith)]

private lemma t99A03_aux_boundaryAngle_eval
    [Fact (0 < 2 * Real.pi)]
    (x : ℝ) (hx0 : 0 ≤ x) (hx2 : x ≤ 2 * Real.pi) :
    AddCircle.liftIco (2 * Real.pi) 0 t99A03_aux_boundaryAngle_g (x : AddCircle (2 * Real.pi)) =
      t99A03_aux_boundaryAngle_g x := by
  rcases hx2.eq_or_lt with rfl | hx
  · rw [show ((2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) = (0 : AddCircle (2 * Real.pi)) by
      simpa using (AddCircle.coe_add_period (2 * Real.pi) (0 : ℝ))]
    change AddCircle.liftIco (2 * Real.pi) 0 t99A03_aux_boundaryAngle_g
      ((0 : ℝ) : AddCircle (2 * Real.pi)) = _
    rw [AddCircle.liftIco_zero_coe_apply (p := 2 * Real.pi) (x := 0) (by
      exact ⟨le_rfl, by positivity⟩)]
    exact t99A03_aux_boundaryAngle_g_end
  · exact AddCircle.liftIco_zero_coe_apply ⟨hx0, hx⟩

theorem t99A03_aux_boundaryAngle :
    ∃ φ : C(Circle, ℝ), ∀ t : Set.Icc (0 : ℝ) 1,
      φ (Circle.exp (2 * Real.pi * (0 + t.1) / 8)) = 2 * Real.pi * t.1 ∧
      φ (Circle.exp (2 * Real.pi * (1 + t.1) / 8)) = 2 * Real.pi + 2 * Real.pi * t.1 ∧
      φ (Circle.exp (2 * Real.pi * (2 + t.1) / 8)) = 4 * Real.pi - 2 * Real.pi * t.1 ∧
      φ (Circle.exp (2 * Real.pi * (3 + t.1) / 8)) = 2 * Real.pi - 2 * Real.pi * t.1 ∧
      ∀ j : ℕ, 4 ≤ j → j < 8 → φ (Circle.exp (2 * Real.pi * (j + t.1) / 8)) = 0 := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let F : AddCircle (2 * Real.pi) → ℝ :=
    AddCircle.liftIco (2 * Real.pi) 0 t99A03_aux_boundaryAngle_g
  have hF : Continuous F := AddCircle.liftIco_zero_continuous
    t99A03_aux_boundaryAngle_g_end
    t99A03_aux_boundaryAngle_g_continuous.continuousOn
  let φ : C(Circle, ℝ) :=
    ⟨fun z ↦ F (AddCircle.homeomorphCircle'.symm z),
      hF.comp AddCircle.homeomorphCircle'.symm.continuous⟩
  refine ⟨φ, fun t ↦ ?_⟩
  have ht0 : 0 ≤ t.1 := t.2.1
  have ht1 : t.1 ≤ 1 := t.2.2
  have heval (j : ℕ) (hj : j < 8) :
      φ (Circle.exp (2 * Real.pi * (j + t.1) / 8)) =
        t99A03_aux_boundaryAngle_g (2 * Real.pi * (j + t.1) / 8) := by
    change F (AddCircle.homeomorphCircle'.symm
      (Circle.exp (2 * Real.pi * (j + t.1) / 8))) = _
    rw [← AddCircle.homeomorphCircle'_apply_mk]
    rw [AddCircle.homeomorphCircle'.symm_apply_apply]
    apply t99A03_aux_boundaryAngle_eval
    · positivity
    · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).2
      have hj' : (j : ℝ) + t.1 ≤ 8 := by
        have hj7 : (j : ℝ) ≤ 7 := by exact_mod_cast (Nat.le_pred_of_lt hj)
        linarith
      nlinarith [Real.pi_pos]
  constructor
  · have h := heval 0 (by norm_num)
    norm_num at h
    norm_num only [zero_add] at ⊢
    rw [h]
    unfold t99A03_aux_boundaryAngle_g
    rw [abs_of_nonpos (by nlinarith [Real.pi_pos])]
    rw [max_eq_right]
    · ring
    · nlinarith [Real.pi_pos]
  constructor
  · have h := heval 1 (by norm_num)
    norm_num at h
    rw [h]
    unfold t99A03_aux_boundaryAngle_g
    rw [abs_of_nonpos (by nlinarith [Real.pi_pos])]
    rw [max_eq_right]
    · ring
    · nlinarith [Real.pi_pos]
  constructor
  · have h := heval 2 (by norm_num)
    norm_num at h
    rw [h]
    unfold t99A03_aux_boundaryAngle_g
    rw [abs_of_nonneg (by nlinarith [Real.pi_pos])]
    rw [max_eq_right]
    · ring
    · nlinarith [Real.pi_pos]
  constructor
  · have h := heval 3 (by norm_num)
    norm_num at h
    rw [h]
    unfold t99A03_aux_boundaryAngle_g
    rw [abs_of_nonneg (by nlinarith [Real.pi_pos])]
    rw [max_eq_right]
    · ring
    · nlinarith [Real.pi_pos]
  · intro j hj4 hj8
    rw [heval j hj8]
    rw [t99A03_aux_boundaryAngle_g, max_eq_left]
    have hj4' : (4 : ℝ) ≤ j := by exact_mod_cast hj4
    have habs : Real.pi / 2 ≤
        |2 * Real.pi * ((j : ℝ) + t.1) / 8 - Real.pi / 2| := by
      rw [abs_of_nonneg]
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    nlinarith
-- END SEAT AREA

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
