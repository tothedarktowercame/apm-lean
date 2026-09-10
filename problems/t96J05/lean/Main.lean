import Mathlib
import ConstructionTargets.RadialSquaredFiber
import ConstructionTargets.ManifoldRegularFiberGlobalAtlas
import ConstructionTargets.TransverseIncidenceChosenAtlas

/-!
# APM t96J05 — a regular radial level of an embedded manifold

## Statement repairs

The former unconditional conclusion is false: the reviewed centered-circle
example has constant radius and hence no codimension-one radial level.  The
corrected theorem below adds an explicit positive attained regular value for
the squared-norm restriction while retaining the original hypotheses and the
literal radial-level conclusion.

## Encoding note

The object is an actual subset of Euclidean space. Its subtype carries a
positive-dimensional smooth manifold structure and its inclusion into the
ambient Euclidean space is smooth. The conclusion is the literal nonempty
intersection with an origin-centred sphere, equipped with the expected
codimension-one manifold structure. The corrected statement supplies the
positive radius, an inhabitant of its literal level, smoothness of the
squared-norm restriction, and surjectivity of its manifold derivative along
the corresponding squared-norm fiber.
-/

open scoped ContDiff Manifold

noncomputable section

abbrev apm_t96j05_E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev apm_t96j05_I (n : ℕ) := 𝓘(ℝ, apm_t96j05_E n)

def apm_t96j05_IsEmbeddedSmoothSubmanifold {m n : ℕ}
    (X : Set (apm_t96j05_E n)) : Prop :=
  ∃ charts : ChartedSpace (apm_t96j05_E m) X,
    let _ := charts
    IsManifold (apm_t96j05_I m) ⊤ X ∧
    ContMDiff (apm_t96j05_I m) (apm_t96j05_I n) ⊤
      (fun x : X ↦ x.1)

/-- The actual intersection of `X` with the sphere of radius `r`. -/
abbrev apm_t96j05_radialLevel {n : ℕ}
    (X : Set (apm_t96j05_E n)) (r : ℝ) :=
  {x : X // ‖x.1‖ = r}

def apm_t96j05_IsSmoothRadialLevel {m n : ℕ}
    (X : Set (apm_t96j05_E n)) (r : ℝ) : Prop :=
  ∃ charts : ChartedSpace (apm_t96j05_E (m - 1))
      (apm_t96j05_radialLevel X r),
    let _ := charts
    IsManifold (apm_t96j05_I (m - 1)) ∞
      (apm_t96j05_radialLevel X r)

/-- A nonzero point supplies a positive attained radial level. This separates
the elementary existence part from Sard and regular-level smoothness. -/
lemma apm_t96j05_exists_positive_nonempty_radialLevel
    {n : ℕ} {X : Set (apm_t96j05_E n)}
    (hXnz : ∃ x : X, (x.1 : apm_t96j05_E n) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Nonempty (apm_t96j05_radialLevel X r) := by
  obtain ⟨x, hx⟩ := hXnz
  refine ⟨‖x.1‖, norm_pos_iff.mpr hx, ⟨x, rfl⟩⟩

/-- A nontrivial subtype cannot consist solely of the ambient origin. Combined
with the preceding lemma, this removes all radial-level existence bookkeeping
once positive manifold dimension is converted into `Nontrivial X`. -/
lemma apm_t96j05_exists_positive_nonempty_radialLevel_of_nontrivial
    {n : ℕ} {X : Set (apm_t96j05_E n)} [Nonempty X] [Nontrivial X] :
    ∃ r : ℝ, 0 < r ∧ Nonempty (apm_t96j05_radialLevel X r) := by
  apply apm_t96j05_exists_positive_nonempty_radialLevel
  by_contra h
  push_neg at h
  have hsub : Subsingleton X :=
    ⟨fun x y ↦ Subtype.ext ((h x).trans (h y).symm)⟩
  exact not_subsingleton X hsub

/-- A nonempty manifold modelled on a positive-dimensional Euclidean space is
nontrivial.  Indeed, every chart target is an open neighbourhood of the image
of its centre, and moving a small amount in one coordinate gives a second
point which can be pulled back through the chart. -/
lemma apm_t96j05_nontrivial_of_pos_dim
    {m : ℕ} (hm : 0 < m) {Y : Type*} [TopologicalSpace Y] [Nonempty Y]
    [ChartedSpace (apm_t96j05_E m) Y]
    [IsManifold (apm_t96j05_I m) ⊤ Y] : Nontrivial Y := by
  let y₀ : Y := Classical.choice inferInstance
  let c : apm_t96j05_E m := (chartAt (apm_t96j05_E m) y₀) y₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (chartAt (apm_t96j05_E m) y₀).open_target c
    (mem_chart_target (apm_t96j05_E m) y₀)
  let i : Fin m := ⟨0, hm⟩
  let z : apm_t96j05_E m := c + EuclideanSpace.single i (ε / 2)
  have hzball : z ∈ Metric.ball c ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [z, add_sub_cancel_left]
    rw [PiLp.norm_single]
    simp [abs_of_pos hε, hε]
  have hz : z ∈ (chartAt (apm_t96j05_E m) y₀).target := hball hzball
  let y₁ : Y := (chartAt (apm_t96j05_E m) y₀).symm z
  have hy : y₀ ≠ y₁ := by
    intro heq
    have hz_eq : z = c := by
      calc
        z = (chartAt (apm_t96j05_E m) y₀) y₁ :=
          ((chartAt (apm_t96j05_E m) y₀).right_inv hz).symm
        _ = c := by rw [← heq]
    have hcoord := congrArg (fun v : apm_t96j05_E m ↦ v i) hz_eq
    simp [z, c, i] at hcoord
    linarith
  exact ⟨⟨y₀, y₁, hy⟩⟩

theorem apm_t96j05
    (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (X : Set (apm_t96j05_E n))
    (hXne : X.Nonempty)
    (hXconn : IsConnected (Set.univ : Set X))
    (hX : apm_t96j05_IsEmbeddedSmoothSubmanifold (m := m) X)
    (r : ℝ) (hr : 0 < r)
    (hlevel : Nonempty (apm_t96j05_radialLevel X r))
    (hdata : ∃ charts : ChartedSpace (apm_t96j05_E m) X,
      letI := charts
      IsManifold (apm_t96j05_I m) ∞ X ∧
      ContMDiff (apm_t96j05_I m) 𝓘(ℝ, ℝ) ∞
        (fun x : X => ‖x.1‖ ^ 2) ∧
      ∀ x : X, ‖x.1‖ ^ 2 = r ^ 2 →
        Function.Surjective
          (mfderiv (apm_t96j05_I m) 𝓘(ℝ, ℝ)
            (fun y : X => ‖y.1‖ ^ 2) x)) :
    ∃ r : ℝ, 0 < r ∧
      Nonempty (apm_t96j05_radialLevel X r) ∧
      apm_t96j05_IsSmoothRadialLevel (m := m) X r := by
  have hm' := hm
  have hmn' := hmn
  have hXne' := hXne
  have hXconn' := hXconn
  have hX' := hX
  clear hm' hmn' hXne' hXconn' hX'
  rcases hdata with ⟨charts, hman, hsm, hreg⟩
  letI : ChartedSpace (apm_t96j05_E m) X := charts
  letI : IsManifold (apm_t96j05_I m) ∞ X := hman
  let f : X → ℝ := fun x => ‖x.1‖ ^ 2
  have hp : (fun x : X => f x = r ^ 2) = (fun x : X => ‖x.1‖ = r) := by
    funext x
    exact propext
      (ConstructionTargets.RadialSquaredFiber.norm_sq_eq_sq_iff hr)
  let H := ConstructionTargets.ManifoldRegularFiberCharts.Model
    (E := apm_t96j05_E m) (F := ℝ)
  let c0 : ChartedSpace H {x : X // f x = r ^ 2} :=
    ConstructionTargets.ManifoldRegularFiberGlobalAtlas.chartedSpace
      f (r ^ 2) hsm hreg
  letI : ChartedSpace H {x : X // f x = r ^ 2} := c0
  letI : IsManifold 𝓘(ℝ, H) ∞ {x : X // f x = r ^ 2} :=
    ConstructionTargets.ManifoldRegularFiberGlobalAtlas.isManifold
      f (r ^ 2) hsm hreg
  let e : H ≃L[ℝ] apm_t96j05_E (m - 1) :=
    ContinuousLinearEquiv.ofFinrankEq (by
      simp [H, ConstructionTargets.ManifoldRegularFiberCharts.Model,
        ConstructionTargets.RegularFiberFixedModelOverlaps.Model,
        ConstructionTargets.RegularFiberFixedModel.Model, apm_t96j05_E])
  let c1 : ChartedSpace (apm_t96j05_E (m - 1))
      {x : X // f x = r ^ 2} :=
    ConstructionTargets.ChartedSpaceModelTransport.chartedSpace
      e.toHomeomorph
  have hc1 : letI := c1
      IsManifold (apm_t96j05_I (m - 1)) ∞ {x : X // f x = r ^ 2} := by
    exact ConstructionTargets.ChartedSpaceModelSmoothTransport.isManifold e
  let c2 :=
    ConstructionTargets.PredicateSubtypeAtlasTransport.chartedSpace hp c1
  have hc2 :=
    ConstructionTargets.PredicateSubtypeAtlasTransport.isManifold hp c1 hc1
  exact ⟨r, hr, hlevel, c2, hc2⟩
