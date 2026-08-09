import Mathlib

/-!
# APM a99J06: A holomorphic logarithm on a simply connected domain

## Statement repairs

None.

## Encoding questions

None. Holomorphicity on the open domain is represented by complex
differentiability there, and the source's simple connectivity is encoded by
Mathlib's topological predicate `IsSimplyConnected` on the domain itself.
-/

open Set Complex

/-- The logarithmic derivative is holomorphic wherever the original
holomorphic function does not vanish. -/
lemma apm_a99j06_logDeriv_differentiableOn
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f Ω) (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    DifferentiableOn ℂ (fun z ↦ deriv f z / f z) Ω := by
  exact (hf.deriv hΩopen).div hf hf0

/-- Once the logarithmic derivative has a primitive, the desired holomorphic
logarithm follows.  Thus this lemma closes all downstream analytic algebra and
isolates the sole missing simply-connected-primitives theorem. -/
lemma apm_a99j06_exists_log_of_logDeriv_exact
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩnonempty : Ω.Nonempty)
    (hΩsc : IsSimplyConnected Ω) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f Ω) (hf0 : ∀ z ∈ Ω, f z ≠ 0)
    (hexact : Complex.IsExactOn (fun z ↦ deriv f z / f z) Ω) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ Ω, f z = Complex.exp (g z) := by
  obtain ⟨z₀, hz₀⟩ := hΩnonempty
  obtain ⟨G, hG0, hG⟩ := hexact.with_val_at z₀ 0
  let H : ℂ → ℂ := fun z ↦ f z * Complex.exp (-G z)
  have hH : ∀ z ∈ Ω, HasDerivAt H 0 z := by
    intro z hz
    have hfz : HasDerivAt f (deriv f z) z :=
      (hf.differentiableAt (hΩopen.mem_nhds hz)).hasDerivAt
    have hprod := hfz.mul (hG z hz).neg.cexp
    convert hprod using 1
    field_simp [hf0 z hz]
    ring
  have hHdiff : DifferentiableOn ℂ H Ω := fun z hz ↦ (hH z hz).differentiableAt.differentiableWithinAt
  have hconstdiff : DifferentiableOn ℂ (fun _ : ℂ ↦ H z₀) Ω := differentiableOn_const _
  have hHeq : Ω.EqOn H (fun _ ↦ H z₀) := by
    apply hΩopen.eqOn_of_deriv_eq hΩsc.isPathConnected.isConnected.isPreconnected
      hHdiff hconstdiff
    · intro z hz
      rw [(hH z hz).deriv]
      simp
    · exact hz₀
    · rfl
  let g : ℂ → ℂ := fun z ↦ G z + Complex.log (f z₀)
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    exact (hG z hz).differentiableAt.add_const _ |>.differentiableWithinAt
  · intro z hz
    have hc : H z = f z₀ := by simpa [H, hG0] using hHeq hz
    dsimp [g]
    rw [Complex.exp_add, Complex.exp_log (hf0 z₀ hz₀)]
    dsimp [H] at hc
    calc
      f z = (f z * Complex.exp (-G z)) * Complex.exp (G z) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = f z₀ * Complex.exp (G z) := by rw [hc]
      _ = Complex.exp (G z) * f z₀ := mul_comm _ _

/-- Simple connectivity already supplies a *continuous* logarithm through the
covering-space lifting property of `Complex.exp`.  This bypasses the missing
primitive theorem topologically; the remaining issue is upgrading this lift
to complex differentiability. -/
lemma apm_a99j06_exists_continuous_log
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩnonempty : Ω.Nonempty)
    (hΩsc : IsSimplyConnected Ω) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f Ω) (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ G : C(Ω, ℂ), ∀ z : Ω, f z = Complex.exp (G z) := by
  letI : SimplyConnectedSpace Ω := hΩsc.simplyConnectedSpace
  letI : LocPathConnectedSpace Ω := hΩopen.locPathConnectedSpace
  obtain ⟨z₀, hz₀⟩ := hΩnonempty
  let F : C(Ω, {z : ℂ // z ≠ 0}) :=
    ⟨fun z ↦ ⟨f z, hf0 z z.property⟩,
      (hf.continuousOn.comp_continuous continuous_subtype_val
        (fun z ↦ z.property)).subtype_mk _⟩
  let e₀ : ℂ := Complex.log (f z₀)
  have he₀ : (⟨Complex.exp e₀, Complex.exp_ne_zero e₀⟩ : {z : ℂ // z ≠ 0}) = F ⟨z₀, hz₀⟩ := by
    apply Subtype.ext
    exact Complex.exp_log (hf0 z₀ hz₀)
  obtain ⟨G, hG, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
    F ⟨z₀, hz₀⟩ e₀ he₀
  refine ⟨G, fun z ↦ ?_⟩
  have hcomp := congrFun hG.2 z
  exact (Subtype.ext_iff.mp hcomp).symm

/-- A continuous lift through the complex exponential is holomorphic whenever
its exponential is holomorphic.  This is the missing local-regularity bridge:
locally the lift agrees with a holomorphic inverse branch of `Complex.exp`,
because both are continuous lifts with the same value at the base point. -/
theorem apm_a99j06_continuous_exp_lift_is_holomorphic
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f Ω) (G : C(Ω, ℂ))
    (hG : ∀ z : Ω, f z = Complex.exp (G z)) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ Ω, f z = Complex.exp (g z) := by
  sorry

theorem apm_a99j06
    (Ω : Set ℂ) (hΩopen : IsOpen Ω) (hΩnonempty : Ω.Nonempty)
    (hΩsc : IsSimplyConnected Ω)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω)
    (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ Ω, f z = Complex.exp (g z) := by
  obtain ⟨G, hG⟩ :=
    apm_a99j06_exists_continuous_log hΩopen hΩnonempty hΩsc f hf hf0
  exact apm_a99j06_continuous_exp_lift_is_holomorphic hΩopen f hf G hG
