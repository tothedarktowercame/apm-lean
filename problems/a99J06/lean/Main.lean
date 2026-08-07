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
  alternate global logarithm or exponential-lifting theorem.  Once the missing
  implication

  `IsSimplyConnected Ω → DifferentiableOn ℂ q Ω → Complex.IsExactOn q Ω`

  is developed, apply it to the compiled logarithmic derivative, choose its
  primitive `G`, prove `f * exp (-G)` has zero derivative and hence is constant
  on the connected domain, and absorb a complex logarithm of that nonzero
  constant into `G`.  The bridge is thus still open at exactly Mathlib's stated
  simply-connected-primitives TODO; no weaker local analytic obligation remains.
  -/
  sorry
