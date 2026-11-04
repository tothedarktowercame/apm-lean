import Mathlib
import ConstructionTargets.ManifoldFormTargets

/-!
# Integration of top forms on an oriented compact manifold

An orientation is represented by a nowhere-vanishing smooth top form.  This is
the standard ``volume-form'' description of an orientation: two representatives
define the same orientation precisely when one is a pointwise positive multiple
of the other.  The integral below only reads the sign of the representative in
a chart, so it is insensitive to that positive rescaling.

Following the usual chart construction (and TauCeti's implementation of it), a
finite chart cover is chosen, made disjoint with `disjointed`, and the signed
coordinate coefficients are integrated against Lebesgue measure (`volume`) on
Euclidean space.  `IntegrableTopForm` makes the failure branch of `integral` explicit.
-/

open Set MeasureTheory
open scoped Manifold ContDiff
noncomputable section

namespace ConstructionTargets.ManifoldTopFormIntegral

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (E n) M]
  [IsManifold 𝓘(ℝ, E n) ∞ M]

abbrev Form := ManifoldFormTargets.Form (E n) M n

/-- A volume-form representative of an orientation.  Multiplication of `form`
by an everywhere-positive smooth function represents the same orientation. -/
structure Orientation (M : Type*) [TopologicalSpace M] [ChartedSpace (E n) M]
    [IsManifold 𝓘(ℝ, E n) ∞ M] where
  form : ManifoldFormTargets.Form (E n) M n
  smooth_form : ManifoldFormTargets.IsSmooth form
  nowhere_zero : ∀ x, form x ≠ 0

/-- Reverse an orientation by negating its volume-form representative. -/
def Orientation.reverse (o : Orientation (n := n) M) : Orientation (n := n) M where
  form := -o.form
  smooth_form := by
    intro e he
    simpa [ManifoldFormTargets.inChart] using (o.smooth_form e he).neg
  nowhere_zero x := neg_ne_zero.mpr (o.nowhere_zero x)

instance : Neg (Orientation (n := n) M) := ⟨Orientation.reverse⟩

structure ChartCover (M : Type*) [TopologicalSpace M]
    [ChartedSpace (E n) M] where
  count : ℕ
  center : Fin count → M
  covers : (Set.univ : Set M) ⊆ ⋃ i, (chartAt (E n) (center i)).source

private theorem chartCover_exists [CompactSpace M] :
    Nonempty (ChartCover (n := n) M) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M ↦ (chartAt (E n) x).source)
    (fun x ↦ (chartAt (E n) x).open_source) (by
      intro x hx
      exact mem_iUnion.mpr ⟨x, mem_chart_source (E n) x⟩)
  let c : Fin s.card → M := fun i ↦ ((s.equivFin).symm i).1
  refine ⟨⟨s.card, c, ?_⟩⟩
  intro x hx
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp (hs hx)
  let i : Fin s.card := s.equivFin ⟨a, ha⟩
  exact mem_iUnion.mpr ⟨i, by simpa [c, i] using hxa⟩

private def chosenCover [CompactSpace M] : ChartCover (n := n) M :=
  Classical.choice chartCover_exists

def ChartCover.domain (c : ChartCover (n := n) M) (i : Fin c.count) : Set M :=
  (chartAt (E n) (c.center i)).source

def ChartCover.piece (c : ChartCover (n := n) M) (i : Fin c.count) : Set M :=
  disjointed c.domain i

/-- The coefficient of a top form in the standard ordered Euclidean basis. -/
def coefficient (w : Form (n := n) (M := M))
    (e : OpenPartialHomeomorph M (E n)) (y : E n) : ℝ :=
  ManifoldFormTargets.inChart w e y (fun i ↦ EuclideanSpace.basisFun (Fin n) ℝ i)

/-- The orientation sign at a coordinate point.  A nowhere-zero top form has a
nonzero coefficient in a genuine manifold chart, so the two branches are the
two possible local orientations. -/
def chartSign (o : Orientation (n := n) M)
    (e : OpenPartialHomeomorph M (E n)) (y : E n) : ℝ :=
  if 0 < coefficient o.form e y then 1 else -1

def chartIntegrand (o : Orientation (n := n) M)
    (w : Form (n := n) (M := M)) (c : ChartCover (n := n) M)
    (i : Fin c.count) : E n → ℝ :=
  ((chartAt (E n) (c.center i)) '' c.piece i).indicator
    (fun y ↦ chartSign o (chartAt (E n) (c.center i)) y *
      coefficient w (chartAt (E n) (c.center i)) y)

/-- Chartwise Lebesgue integrability for the fixed finite cover used by the
definition.  On a compact manifold this is the only analytic side condition. -/
def IntegrableTopForm [CompactSpace M] (o : Orientation (n := n) M)
    (w : Form (n := n) (M := M)) : Prop :=
  ∀ i, Integrable (chartIntegrand o w chosenCover i) volume

private def coverIntegral [CompactSpace M] (o : Orientation (n := n) M)
    (w : Form (n := n) (M := M)) : ℝ :=
  ∑ i, ∫ y, chartIntegrand o w chosenCover i y ∂volume

/-- Integral of a top form, obtained from a classically chosen finite chart
cover and its disjoint Borel pieces.  Non-integrable input takes the explicit
zero branch; callers can rule it out with `IntegrableTopForm`. -/
def integral [CompactSpace M] (o : Orientation (n := n) M)
    (w : Form (n := n) (M := M)) : ℝ := by
  classical
  exact if IntegrableTopForm o w then coverIntegral o w else 0

/-- The chart construction is independent of the chosen finite chart cover. -/
theorem integral_eq_of_cover [CompactSpace M] (o : Orientation (n := n) M)
    (w : Form (n := n) (M := M)) (hw : IntegrableTopForm o w)
    (c : ChartCover (n := n) M) :
    integral o w = ∑ i, ∫ y, chartIntegrand o w c i y ∂volume := by
  sorry

/-- Reversing the orientation negates integration. -/
theorem integral_reverse [CompactSpace M] (o : Orientation (n := n) M)
    (w : Form (n := n) (M := M)) (hw : IntegrableTopForm o w)
    (hrw : IntegrableTopForm (-o) w) :
    integral (-o) w = -integral o w := by
  sorry

/-- Additivity on integrable top forms. -/
theorem integral_add [CompactSpace M] (o : Orientation (n := n) M)
    (w v : Form (n := n) (M := M)) (hw : IntegrableTopForm o w)
    (hv : IntegrableTopForm o v) (ha : IntegrableTopForm o (w + v)) :
    integral o (w + v) = integral o w + integral o v := by
  sorry

/-- Homogeneity on integrable top forms. -/
theorem integral_smul [CompactSpace M] (o : Orientation (n := n) M)
    (a : ℝ) (w : Form (n := n) (M := M)) (hw : IntegrableTopForm o w)
    (ha : IntegrableTopForm o (a • w)) :
    integral o (a • w) = a * integral o w := by
  sorry

instance : Fact (Module.finrank ℝ (E 2) = 1 + 1) := ⟨by simp⟩

/-- The unit circle in the Euclidean plane, with Mathlib's smooth structure. -/
abbrev UnitCircle := Metric.sphere (0 : E 2) 1

/-- The angle form `dθ`: the restriction of the ambient covector
`v ↦ -p₁ v₀ + p₀ v₁` at `p` to the tangent space of the circle, through the
derivative of the inclusion. -/
def angleForm : ManifoldFormTargets.Form (E 1) UnitCircle 1 := fun x ↦
  ContinuousAlternatingMap.ofSubsingleton ℝ (E 1) ℝ (0 : Fin 1)
    (ContinuousLinearMap.comp
      ((-(x : E 2) 1) • (EuclideanSpace.proj (0 : Fin 2) : E 2 →L[ℝ] ℝ) +
        ((x : E 2) 0) • (EuclideanSpace.proj (1 : Fin 2) : E 2 →L[ℝ] ℝ))
      (mfderiv 𝓘(ℝ, E 1) 𝓘(ℝ, E 2) (Subtype.val : UnitCircle → E 2) x))

/-- Sanity check pinning the normalization (Lebesgue measure, chart signs):
with the counterclockwise orientation represented by `dθ` itself, the angle
form integrates to `2π`, the length of the unit circle.  A wrong measure
normalization, a sign error, or a constant definition fails this. -/
theorem unitCircle_angleForm_integral :
    ∃ o : Orientation (n := 1) UnitCircle, o.form = angleForm ∧
      IntegrableTopForm o angleForm ∧ integral o angleForm = 2 * Real.pi := by
  sorry

end ConstructionTargets.ManifoldTopFormIntegral
