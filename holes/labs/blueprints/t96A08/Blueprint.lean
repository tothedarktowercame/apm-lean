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

/-- LIBRARY: the fundamental theorem for a smooth manifold one-form along
closed-piecewise-smooth paths, in the exact interface needed by this problem. -/
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
  sorry

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
