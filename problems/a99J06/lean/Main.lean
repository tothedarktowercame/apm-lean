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

theorem apm_a99j06
    (Ω : Set ℂ) (hΩopen : IsOpen Ω) (hΩnonempty : Ω.Nonempty)
    (hΩsc : IsSimplyConnected Ω)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω)
    (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ Ω, f z = Complex.exp (g z) := by
  /-
  Boundary (closer hop 1): `apm_a99j06_logDeriv_differentiableOn` above now
  compiles the complete analytic reduction: `z ↦ deriv f z / f z` is
  holomorphic on `Ω`.  A renewed source search found
  `Mathlib.Analysis.Complex.HasPrimitives`; its module documentation explicitly
  says that extending primitives from disks to simply connected domains is a
  TODO.  Its available theorem `DifferentiableOn.isExactOn_ball` therefore
  cannot consume the frozen general `IsSimplyConnected Ω` hypothesis.

  Searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`, closed artifacts,
  complex logarithm/lifting/covering-space APIs, and git history found no
  alternate global logarithm or exponential-lifting theorem.  Closer hop 2
  proves `apm_a99j06_exists_log_of_logDeriv_exact`, closing every downstream
  step: normalize a primitive, prove `f * exp (-G)` is constant using
  connectedness, and absorb the nonzero constant via `Complex.log`.  The only
  missing implication is

  `IsSimplyConnected Ω → DifferentiableOn ℂ q Ω → Complex.IsExactOn q Ω`

  Once developed, the new conditional lemma applies immediately.  The bridge
  is thus still open at exactly Mathlib's stated simply-connected-primitives
  TODO; all weaker analytic obligations are now compiled.
  -/
  sorry
