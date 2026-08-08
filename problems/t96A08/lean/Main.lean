import Mathlib

/-!
# APM t96A08

## Statement repairs

* The source writes `f : M → M`, although `f(p)` is a real-valued integral.
  The codomain is repaired to `ℝ`.
* The source implicitly assumes that every point can be joined to the chosen
  base point.  This is made explicit by `hreachable`; without it the displayed
  definition of `f` is not available on every connected component.

## Encoding questions

Mathlib has no bundled piecewise-smooth manifold path or manifold one-form
line integral.  A path is therefore represented by a map `ℝ → M` which is
continuous and smooth away from a finite set, and its line integral is defined
concretely by integrating the one-form applied to its manifold derivative over
`[0,1]`.  Smoothness of the one-form means smoothness of its evaluation map on
the tangent bundle.
-/

noncomputable section

open scoped Manifold

def apm_t96a08_IsPiecewiseSmoothPath
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (γ : ℝ → M) : Prop :=
  Continuous γ ∧
    ∃ breaks : Finset ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ breaks →
      ContMDiffAt 𝓘(ℝ, ℝ) I (⊤ : WithTop ℕ∞) γ t

def apm_t96a08_LineIntegral
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (ω : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (γ : ℝ → M) : ℝ :=
  ∫ t : ℝ in (0 : ℝ)..1,
    ω (γ t) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)

theorem apm_t96a08
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (ω : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (base : M)
    (hωsmooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞)
      (fun v : TangentBundle I M => ω v.1 v.2))
    (hreachable : ∀ p : M, ∃ γ : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I γ ∧ γ 0 = base ∧ γ 1 = p)
    (hindependent : ∀ γ₁ γ₂ : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I γ₁ →
      apm_t96a08_IsPiecewiseSmoothPath I γ₂ →
      γ₁ 0 = γ₂ 0 → γ₁ 1 = γ₂ 1 →
      apm_t96a08_LineIntegral I ω γ₁ = apm_t96a08_LineIntegral I ω γ₂) :
    ∃ f : M → ℝ,
      (∀ p : M, ∀ γ : ℝ → M,
        apm_t96a08_IsPiecewiseSmoothPath I γ → γ 0 = base → γ 1 = p →
        f p = apm_t96a08_LineIntegral I ω γ) ∧
      ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f ∧
      ∀ p : M, mfderiv I 𝓘(ℝ, ℝ) f p = ω p := by
  classical
  choose γ hγ using hreachable
  refine ⟨fun p ↦ apm_t96a08_LineIntegral I ω (γ p), ?_, ?_⟩
  · intro p δ hδ hδ0 hδ1
    exact hindependent (γ p) δ (hγ p).1 hδ
      (by rw [(hγ p).2.1, hδ0]) (by rw [(hγ p).2.2, hδ1])
  · /-
    CLOSER HOP 1 boundary. The potential is now constructed by classical
    choice from `hreachable`, and its defining value for every admissible path
    is proved from `hindependent`; well-definedness and endpoint bookkeeping
    are compiled outside this `sorry`.

    The remaining bridge is local calculus for the concrete line integral.
    One must append a short chart-linear path to the chosen base path, prove
    the concatenation piecewise smooth, split and reparameterize its integral,
    and differentiate the short-segment integral with respect to its endpoint.
    This must yield both `ContMDiff` and the exact `mfderiv = ω` equality.
    Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, line-integral
    siblings, Mathlib's manifold derivative, interval-integral, path
    concatenation, tangent-bundle, and differential-form sources, and git
    history found no manifold one-form fundamental theorem or compatible
    piecewise-smooth concatenation API.
    -/
    sorry
