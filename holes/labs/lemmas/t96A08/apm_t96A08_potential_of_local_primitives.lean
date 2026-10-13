import Mathlib

noncomputable section

open scoped Manifold

/-! The repaired definition requires genuine smoothness on each closed member
of a finite subdivision.  This rules out derivatives with non-integrable
oscillatory singularities at the break points. -/

def apm_t96a08_IsPiecewiseSmoothPath
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (γ : ℝ → M) : Prop :=
  Continuous γ ∧
    ∃ (n : ℕ) (cuts : Fin (n + 1) → ℝ),
      StrictMono cuts ∧ cuts 0 = 0 ∧ cuts (Fin.last n) = 1 ∧
      ∀ i : Fin n, ContMDiffOn 𝓘(ℝ, ℝ) I (⊤ : WithTop ℕ∞) γ
        (Set.Icc (cuts i.castSucc) (cuts i.succ))

def apm_t96a08_LineIntegral
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (ω : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (γ : ℝ → M) : ℝ :=
  ∫ t : ℝ in (0 : ℝ)..1,
    ω (γ t) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)

/-- The path operation needed by the fundamental theorem, separated from all
chart calculations. -/
def apm_t96A08_HasAdditiveConcatenation
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) : Prop :=
  ∀ gamma delta : ℝ → M,
    apm_t96a08_IsPiecewiseSmoothPath I gamma →
    apm_t96a08_IsPiecewiseSmoothPath I delta →
    gamma 1 = delta 0 →
    ∃ eta : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I eta ∧
      eta 0 = gamma 0 ∧ eta 1 = delta 1 ∧
      apm_t96a08_LineIntegral I omega eta =
        apm_t96a08_LineIntegral I omega gamma +
          apm_t96a08_LineIntegral I omega delta

/-- The local output of the chart-linear-segment calculation.  Keeping this
as a proposition makes the analytic seat independent of path concatenation. -/
def apm_t96A08_HasLocalRadialPrimitives
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) : Prop :=
  ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
    ∃ g : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) g U ∧
      mfderiv I 𝓘(ℝ, ℝ) g x = omega x ∧
      ∀ z ∈ U, ∃ delta : ℝ → M,
        apm_t96a08_IsPiecewiseSmoothPath I delta ∧
        delta 0 = x ∧ delta 1 = z ∧
        g z - g x = apm_t96a08_LineIntegral I omega delta

/-- Closed-piecewise-smooth paths can be concatenated, and the integral is
additive under the standard affine reparameterizations. -/
theorem apm_t96A08_piecewisePath_concat_additive
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2)) :
    apm_t96A08_HasAdditiveConcatenation I omega := by
  sorry

/-- In a sufficiently small convex chart, integration along the straight
coordinate segment gives a smooth local function whose derivative at the
centre is the prescribed one-form. -/
theorem apm_t96A08_chart_radial_primitive
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2)) :
    apm_t96A08_HasLocalRadialPrimitives I omega := by
  sorry

/-- Abstract local-to-global step: additive concatenation and local radial
primitives identify the path-defined potential locally with a smooth one. -/
-- BEGIN SEAT AREA
theorem apm_t96A08_potential_of_local_primitives
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (base : M)
    (hconcat : apm_t96A08_HasAdditiveConcatenation I omega)
    (hlocal : apm_t96A08_HasLocalRadialPrimitives I omega)
    (hreachable : ∀ p : M, ∃ gamma : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I gamma ∧
        gamma 0 = base ∧ gamma 1 = p)
    (f : M → ℝ)
    (hf : ∀ p : M, ∀ gamma : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I gamma →
      gamma 0 = base → gamma 1 = p →
      f p = apm_t96a08_LineIntegral I omega gamma) :
    ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f ∧
      ∀ p : M, mfderiv I 𝓘(ℝ, ℝ) f p = omega p := by
  have h_at : ∀ x : M,
      ContMDiffAt I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f x ∧
        mfderiv I 𝓘(ℝ, ℝ) f x = omega x := by
    intro x
    rcases hlocal x with ⟨U, hU, hxU, g, hg, hgd, hradial⟩
    rcases hreachable x with ⟨gamma, hgamma, hgamma0, hgamma1⟩
    have heq : ∀ z ∈ U, f z = g z + (f x - g x) := by
      intro z hz
      rcases hradial z hz with ⟨delta, hdelta, hdelta0, hdelta1, hdelta_int⟩
      rcases hconcat gamma delta hgamma hdelta (hgamma1.trans hdelta0.symm) with
        ⟨eta, heta, heta0, heta1, heta_int⟩
      have hfz := hf z eta heta (heta0.trans hgamma0) (heta1.trans hdelta1)
      have hfx := hf x gamma hgamma hgamma0 hgamma1
      linarith
    have hg_at : ContMDiffAt I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) g x :=
      hg.contMDiffAt (hU.mem_nhds hxU)
    have hq_at : ContMDiffAt I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞)
        (fun y ↦ g y + (f x - g x)) x :=
      hg_at.add contMDiffAt_const
    have hfg : Filter.EventuallyEq (nhds x) f (fun y ↦ g y + (f x - g x)) :=
      Filter.mem_of_superset (hU.mem_nhds hxU) (fun z hz ↦ heq z hz)
    refine ⟨hq_at.congr_of_eventuallyEq hfg, ?_⟩
    rw [hfg.mfderiv_eq]
    change mfderiv I 𝓘(ℝ, ℝ) (g + fun _ ↦ f x - g x) x = omega x
    rw [mfderiv_add (hg_at.mdifferentiableAt (by simp)) mdifferentiableAt_const,
      mfderiv_const]
    rw [hgd]
    ext v
    change omega x v + 0 = omega x v
    exact add_zero _
  exact ⟨fun x ↦ (h_at x).1, fun x ↦ (h_at x).2⟩
-- END SEAT AREA

/-- The fundamental theorem assembled from the three independent library
boundaries above. -/
theorem apm_t96A08_piecewise_lineIntegral_fundamental
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E E) [ChartedSpace E M]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (omega : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (base : M)
    (homega_smooth : ContMDiff I.tangent 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞)
      (fun v : TangentBundle I M => omega v.1 v.2))
    (hreachable : ∀ p : M, ∃ gamma : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I gamma ∧
        gamma 0 = base ∧ gamma 1 = p)
    (f : M → ℝ)
    (hf : ∀ p : M, ∀ gamma : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I gamma →
      gamma 0 = base → gamma 1 = p →
      f p = apm_t96a08_LineIntegral I omega gamma) :
    ContMDiff I 𝓘(ℝ, ℝ) (⊤ : WithTop ℕ∞) f ∧
      ∀ p : M, mfderiv I 𝓘(ℝ, ℝ) f p = omega p := by
  apply apm_t96A08_potential_of_local_primitives I omega base
  · exact apm_t96A08_piecewisePath_concat_additive I omega homega_smooth
  · exact apm_t96A08_chart_radial_primitive I omega homega_smooth
  · exact hreachable
  · exact hf

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
  have hreach := hreachable
  choose γ hγ using hreachable
  let f : M → ℝ := fun p ↦ apm_t96a08_LineIntegral I ω (γ p)
  have hf : ∀ p : M, ∀ δ : ℝ → M,
      apm_t96a08_IsPiecewiseSmoothPath I δ → δ 0 = base → δ 1 = p →
      f p = apm_t96a08_LineIntegral I ω δ := by
    intro p δ hδ hδ0 hδ1
    exact hindependent (γ p) δ (hγ p).1 hδ
      (by rw [(hγ p).2.1, hδ0]) (by rw [(hγ p).2.2, hδ1])
  exact ⟨f, hf,
    apm_t96A08_piecewise_lineIntegral_fundamental I ω base hωsmooth
      hreach f hf⟩

#print axioms apm_t96a08
