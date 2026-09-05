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
  classical
  -- Trivial case: empty domain.
  rcases eq_empty_or_nonempty Ω with hΩempty | hΩne
  · exact ⟨0, differentiableOn_const _, fun z hz ↦ absurd hz (by rw [hΩempty]; simp)⟩
  -- Extend the continuous lift to ℂ (arbitrarily outside Ω).
  set γ : ℂ → ℂ := fun z ↦ if h : z ∈ Ω then G ⟨z, h⟩ else 0 with hγdef
  have hγval : ∀ z (hz : z ∈ Ω), γ z = G ⟨z, hz⟩ := fun _ hz ↦ dif_pos hz
  have key : ∀ z₀ ∈ Ω, DifferentiableAt ℂ γ z₀ := by
    intro z₀ hz₀
    -- The value of `f` at the base point is nonzero.
    have ha₀ : f z₀ ≠ 0 := by
      rw [hG ⟨z₀, hz₀⟩]; exact Complex.exp_ne_zero _
    set w₀ : ℂ := G ⟨z₀, hz₀⟩ with hw₀
    -- The candidate holomorphic branch near `z₀`: `w₀ + log (f z / f z₀)`.
    set H : ℂ → ℂ := fun z ↦ Complex.log (f z / f z₀) + w₀ with hHdef
    have hw₀exp : Complex.exp w₀ = f z₀ := (hG ⟨z₀, hz₀⟩).symm
    -- `H` is differentiable at `z₀` since `f z₀ / f z₀ = 1` lies in the slit plane.
    have hHdiff : DifferentiableAt ℂ H z₀ := by
      have hfz₀ : DifferentiableAt ℂ f z₀ :=
        (hf z₀ hz₀).differentiableAt (hΩopen.mem_nhds hz₀)
      have hL : DifferentiableAt ℂ (fun z ↦ Complex.log (f z / f z₀)) z₀ := by
        refine (hfz₀.div_const (f z₀)).clog ?_
        simp only [Complex.slitPlane, Set.mem_setOf_eq, div_self ha₀]
        exact Or.inl (by norm_num)
      exact hL.add_const w₀
    -- `G - H` is continuous on `Ω`, vanishes at `z₀`, and lands in `2πiℤ`.
    have hDcont : ContinuousAt (fun z : Ω ↦ G z - H ↑z) ⟨z₀, hz₀⟩ := by
      refine ContinuousAt.sub ?_ ?_
      · exact (ContinuousMap.continuous G).continuousAt
      · exact hHdiff.continuousAt.comp' continuous_subtype_val.continuousAt
    have hD0 : G ⟨z₀, hz₀⟩ - H z₀ = 0 := by
      simp [hHdef, Complex.log_one, div_self ha₀, hw₀]
    obtain ⟨ε, hε, hεball⟩ :=
      Metric.continuousAt_iff.mp hDcont Real.pi Real.pi_pos
    -- On the small ball, `exp (G z) = exp (H z)`, so `G z - H z ∈ 2πiℤ`;
    -- by continuity and |2πn| ≥ 2π > π the integer is `0`.
    have hEq : ∀ z : Ω, dist z (⟨z₀, hz₀⟩ : Ω) < ε → G z = H ↑z := by
      intro z hzdist
      have hfzne : f ↑z ≠ 0 := by
        rw [hG z]; exact Complex.exp_ne_zero _
      have hHz : Complex.exp (H ↑z) = f ↑z := by
        have : Complex.exp (Complex.log (f ↑z / f z₀)) = f ↑z / f z₀ :=
          Complex.exp_log (div_ne_zero hfzne ha₀)
        calc Complex.exp (H ↑z)
            = Complex.exp (Complex.log (f ↑z / f z₀)) * Complex.exp w₀ := by
              rw [hHdef, Complex.exp_add]
          _ = f z₀ * (f ↑z / f z₀) := by rw [hw₀exp, this]; ring
          _ = f ↑z := by field_simp
      have ⟨n, hn⟩ :=
        Complex.exp_eq_exp_iff_exists_int.mp ((hG z).symm.trans hHz.symm)
      have hsub : G z - H ↑z = n * (2 * Real.pi * Complex.I) := by
        rw [hn]; ring
      have hnorm : ‖n * (2 * Real.pi * Complex.I)‖ < Real.pi := by
        have hdist := hεball hzdist
        rw [Complex.dist_eq, hD0, sub_zero] at hdist
        rwa [hsub] at hdist
      have hn0 : n = 0 := by
        by_contra hnne
        have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hnne
        have h2 : ‖(2 : ℂ) * Real.pi * Complex.I‖ = 2 * Real.pi := by
          simp [Complex.norm_real, Complex.norm_I,
            Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        have hnorm' : |(n : ℝ)| * (2 * Real.pi) < Real.pi := by
          rwa [Complex.norm_mul, Complex.norm_intCast, h2] at hnorm
        nlinarith [Real.pi_pos]
      simp only [hn0, Int.cast_zero, zero_mul, add_zero] at hn
      exact hn
    -- Transport differentiability from `H` to `γ` on `Ω ∩ ball z₀ ε`.
    have hdw : DifferentiableWithinAt ℂ γ (Ω ∩ Metric.ball z₀ ε) z₀ :=
      (hHdiff.differentiableWithinAt).congr
        (fun z hz ↦
          (hγval z hz.1).trans
            (hEq (⟨z, hz.1⟩ : Ω)
              (by simpa [Subtype.dist_eq, Metric.mem_ball] using hz.2)))
        (by simp only [hγval z₀ hz₀, hHdef]
            simp [Complex.log_one, div_self ha₀, hw₀])
    exact hdw.differentiableAt
      ((hΩopen.inter Metric.isOpen_ball).mem_nhds
        ⟨hz₀, Metric.mem_ball_self hε⟩)
  refine ⟨γ, fun z₀ hz₀ ↦ (key z₀ hz₀).differentiableWithinAt,
    fun z hz ↦ by rw [hγval z hz]; exact hG ⟨z, hz⟩⟩

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
