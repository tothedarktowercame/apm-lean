import ConstructionTargets.ManifoldTopFormIntegral

/-!
# APM t94J07 — homotopy invariance of integration of a closed form

This repairs the old circle-only statement by treating an arbitrary compact,
boundaryless, oriented `n`-manifold `X` and a compact manifold with corners
`Y`.

The definitions used below are the standard ones:

* `Form Y n` is an alternating `n`-covector on each tangent space of `Y`.
* `IsSmoothForm J ω` means that the form's coefficients in every extended
  chart are smooth on that chart's target.
* `IsClosedForm J ω` means that the within-exterior derivative of those
  coefficients, computed on each extended chart target, vanishes there.  This
  is the standard local corners definition and includes boundary points.
* `pullback J f ω` composes each covector with the manifold derivative of `f`,
  which is the standard pullback of a differential form.
* `ManifoldTopFormIntegral.Orientation X` is represented by a smooth,
  nowhere-vanishing top form, the standard volume-form description of an
  orientation.
* `ManifoldTopFormIntegral.IntegrableTopForm` is chartwise Lebesgue
  integrability for the finite chart construction, and
  `ManifoldTopFormIntegral.integral` is the resulting oriented integral.
* `t94J07SmoothHomotopy f g H` says that `H : X × ℝ → Y` is smooth and has
  endpoint slices `f` and `g` at `0` and `1`.  This is the usual smooth
  homotopy represented on an open parameter manifold.
-/

open scoped Manifold ContDiff
noncomputable section

namespace T94J07

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The coefficients of a form in a chart on a manifold with corners.  The
inverse extended chart is differentiated within `range J`, the standard
tangent derivative at boundary and corner points. -/
def inChart {m k : ℕ} {H Y : Type*} [TopologicalSpace H] [TopologicalSpace Y]
    (J : ModelWithCorners ℝ (E m) H) [ChartedSpace H Y]
    (form : Y → E m [⋀^Fin k]→L[ℝ] ℝ) (e : OpenPartialHomeomorph Y H)
    (y : E m) : E m [⋀^Fin k]→L[ℝ] ℝ :=
  (form ((e.extend J).symm y)).compContinuousLinearMap
    (mfderivWithin 𝓘(ℝ, E m) J (e.extend J).symm (Set.range J) y)

/-- A form on a manifold with corners is smooth when its coefficients in every
extended manifold chart are smooth on the extended chart target. -/
def IsSmoothForm {m k : ℕ} {H Y : Type*}
    [TopologicalSpace H] [TopologicalSpace Y]
    (J : ModelWithCorners ℝ (E m) H) [ChartedSpace H Y]
    (form : Y → E m [⋀^Fin k]→L[ℝ] ℝ) : Prop :=
  ∀ e ∈ atlas H Y, ContDiffOn ℝ ∞ (inChart J form e) (e.extend J).target

/-- A form on a manifold with corners is closed when the exterior derivative
of its chart coefficients, taking derivatives within each extended chart
target, vanishes there.  This is the standard local definition and avoids the
junk values of a partial chart inverse outside its target; smoothness carries
the interior identity continuously to boundary and corner points. -/
def IsClosedForm {m k : ℕ} {H Y : Type*}
    [TopologicalSpace H] [TopologicalSpace Y]
    (J : ModelWithCorners ℝ (E m) H) [ChartedSpace H Y]
    (form : Y → E m [⋀^Fin k]→L[ℝ] ℝ) : Prop :=
  ∀ e ∈ atlas H Y,
    Set.EqOn (extDerivWithin (inChart J form e) (e.extend J).target) 0
      (e.extend J).target

/-- Pullback of a form from a manifold with corners, using the actual manifold
derivative into its corners model. -/
def pullback {n m k : ℕ} {X H Y : Type*}
    [TopologicalSpace X] [ChartedSpace (E n) X]
    [TopologicalSpace H] [TopologicalSpace Y]
    (J : ModelWithCorners ℝ (E m) H) [ChartedSpace H Y]
    (f : X → Y) (form : Y → E m [⋀^Fin k]→L[ℝ] ℝ) :
    ConstructionTargets.ManifoldFormTargets.Form (E n) X k :=
  fun x ↦ (form (f x)).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, E n) J f x)

/-- A smooth homotopy, represented on the open parameter manifold `ℝ`, whose
time-zero and time-one slices are the specified maps. -/
def SmoothHomotopy {n m : ℕ} {X H Y : Type*}
    [TopologicalSpace X] [ChartedSpace (E n) X]
    [TopologicalSpace H] [TopologicalSpace Y]
    (J : ModelWithCorners ℝ (E m) H) [ChartedSpace H Y]
    (f g : X → Y) (homotopy : X × ℝ → Y) : Prop :=
  ContMDiff (𝓘(ℝ, E n).prod 𝓘(ℝ, ℝ)) J ∞ homotopy ∧
    (∀ x, homotopy (x, 0) = f x) ∧
    ∀ x, homotopy (x, 1) = g x

/-- Sanity check: a smooth map is smoothly homotopic to itself by the
constant-in-time homotopy.  Thus `SmoothHomotopy` is not empty or unrelated to
its endpoint maps. -/
theorem smoothHomotopy_refl {n m : ℕ} {X H Y : Type*}
    [TopologicalSpace X] [ChartedSpace (E n) X]
    [TopologicalSpace H] [TopologicalSpace Y]
    (J : ModelWithCorners ℝ (E m) H) [ChartedSpace H Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℝ, E n) J ∞ f) :
    SmoothHomotopy (n := n) (m := m) J f f
      (fun p : X × ℝ ↦ f p.1) := by
  refine ⟨hf.comp contMDiff_fst, ?_, ?_⟩ <;> simp

/-- Sanity check: the definition really fixes both endpoint slices. -/
theorem smoothHomotopy_endpoints {n m : ℕ} {X H Y : Type*}
    [TopologicalSpace X] [ChartedSpace (E n) X]
    [TopologicalSpace H] [TopologicalSpace Y]
    (J : ModelWithCorners ℝ (E m) H) [ChartedSpace H Y]
    {f g : X → Y} {H : X × ℝ → Y}
    (h : SmoothHomotopy (n := n) (m := m) J f g H) :
    (∀ x, H (x, 0) = f x) ∧ ∀ x, H (x, 1) = g x :=
  ⟨h.2.1, h.2.2⟩

/-- Sanity check: for the boundaryless model, the corners pullback is
definitionally the shared ordinary-manifold pullback. -/
theorem pullback_self_eq {n m k : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (E n) X]
    [TopologicalSpace Y] [ChartedSpace (E m) Y]
    (f : X → Y) (form : Y → E m [⋀^Fin k]→L[ℝ] ℝ) :
    pullback (n := n) 𝓘(ℝ, E m) f form =
      ConstructionTargets.ManifoldFormTargets.pullback f form :=
  rfl

end T94J07

open ConstructionTargets

theorem apm_t94j07
    {n m : ℕ} {X H Y : Type*}
    [TopologicalSpace X] [T2Space X] [ChartedSpace (T94J07.E n) X]
    [IsManifold 𝓘(ℝ, T94J07.E n) ∞ X] [CompactSpace X]
    [TopologicalSpace H] (J : ModelWithCorners ℝ (T94J07.E m) H)
    [TopologicalSpace Y] [T2Space Y] [ChartedSpace H Y]
    [IsManifold J ∞ Y] [CompactSpace Y]
    (orientation : ManifoldTopFormIntegral.Orientation (n := n) X)
    (omega : Y → T94J07.E m [⋀^Fin n]→L[ℝ] ℝ)
    (homega_smooth : T94J07.IsSmoothForm J omega)
    (homega_closed : T94J07.IsClosedForm J omega)
    (f g : X → Y)
    (hf : ContMDiff 𝓘(ℝ, T94J07.E n) J ∞ f)
    (hg : ContMDiff 𝓘(ℝ, T94J07.E n) J ∞ g)
    (homotopy : X × ℝ → Y)
    (hhomotopy : T94J07.SmoothHomotopy (n := n) (m := m) J f g homotopy) :
    ManifoldTopFormIntegral.IntegrableTopForm orientation
        (T94J07.pullback (n := n) (m := m) J f omega) ∧
      ManifoldTopFormIntegral.IntegrableTopForm orientation
        (T94J07.pullback (n := n) (m := m) J g omega) ∧
      ManifoldTopFormIntegral.integral orientation
          (T94J07.pullback (n := n) (m := m) J f omega) =
        ManifoldTopFormIntegral.integral orientation
          (T94J07.pullback (n := n) (m := m) J g omega) := by
  sorry
