import Mathlib

/-!
# APM m95A03: the Dirichlet principle for a Sturm--Liouville problem

## Statement repairs

The problem asks for appropriate hypotheses; we take `a < b`, `p ∈ C¹`
uniformly positive, and continuous `q ≥ 0` and `f`.

Uniqueness in part (c) is up to equality on `[a, b]`. The functions are
`ℝ → ℝ` and the energy only sees `[a, b]`, so a minimizer changed outside
`[a, b]` is another minimizer; `∃!` over all of `ℝ → ℝ` is false (compiled
counterexample: holes/labs/solve-loop/refutations/m95A03/Refute.lean).

## Encoding questions

Mathlib has no bundled Sobolev space. The problem's differential equation,
boundary constraints, energy, affine homogenization, minimization claim, and
existence/uniqueness conclusion are therefore encoded directly on `C¹`/`C²`
functions, without replacing any of those objects by a scalar surrogate.
-/

noncomputable section

open Set

/-- The energy from the printed variational problem. -/
def apm_m95A03_energy (a b : ℝ) (p q f u : ℝ → ℝ) : ℝ :=
  ∫ t in a..b, p t * (deriv u t) ^ 2 + q t * (u t) ^ 2 + 2 * u t * f t

/-- The admissible `C¹` functions with the prescribed endpoint data. -/
def apm_m95A03_admissible (a b α β : ℝ) : Set (ℝ → ℝ) :=
  {u | ContDiff ℝ 1 u ∧ u a = α ∧ u b = β}

/-- Classical solutions of `(p u')' - q u = f` with Dirichlet data. -/
def apm_m95A03_solves
    (a b α β : ℝ) (p q f u : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 u ∧ u a = α ∧ u b = β ∧
    ∀ t ∈ Set.Icc a b,
      deriv (fun x => p x * deriv u x) t - q t * u t = f t

/-- Linear interpolant used to homogenize the boundary conditions. -/
def apm_m95A03_boundaryLift (a b α β t : ℝ) : ℝ :=
  α + (β - α) * ((t - a) / (b - a))

/-- Right-hand side after writing `u = v + w`. -/
def apm_m95A03_modifiedRHS
    (p q f w : ℝ → ℝ) (t : ℝ) : ℝ :=
  f t - (deriv (fun x => p x * deriv w x) t - q t * w t)

/-! ## Remaining bridges -/

theorem apm_m95A03_isMinOn_of_solves
    (a b α β p₀ : ℝ) (hab : a < b) (hp₀ : 0 < p₀)
    (p q f u : ℝ → ℝ) (hp : ContDiff ℝ 1 p)
    (hq : Continuous q) (hf : Continuous f)
    (hp_lower : ∀ t ∈ Set.Icc a b, p₀ ≤ p t)
    (hq_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ q t)
    (hu : apm_m95A03_solves a b α β p q f u) :
    IsMinOn (apm_m95A03_energy a b p q f)
      (apm_m95A03_admissible a b α β) u := by
  sorry

theorem apm_m95A03_solves_of_isMinOn
    (a b α β p₀ : ℝ) (hab : a < b) (hp₀ : 0 < p₀)
    (p q f u : ℝ → ℝ) (hp : ContDiff ℝ 1 p)
    (hq : Continuous q) (hf : Continuous f)
    (hp_lower : ∀ t ∈ Set.Icc a b, p₀ ≤ p t)
    (hq_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ q t)
    (hu2 : ContDiff ℝ 2 u) (hua : u a = α) (hub : u b = β)
    (hmin : IsMinOn (apm_m95A03_energy a b p q f)
      (apm_m95A03_admissible a b α β) u) :
    apm_m95A03_solves a b α β p q f u := by
  sorry

theorem apm_m95A03_homogenization
    (a b α β : ℝ) (hab : a < b) (p q f u : ℝ → ℝ) :
    let w := apm_m95A03_boundaryLift a b α β
    apm_m95A03_solves a b α β p q f u ↔
      apm_m95A03_solves a b 0 0 p q
        (apm_m95A03_modifiedRHS p q f w) (u - w) := by
  sorry

theorem apm_m95A03_exists_homogeneous_minimizer
    (a b p₀ : ℝ) (hab : a < b) (hp₀ : 0 < p₀)
    (p q f : ℝ → ℝ) (hp : ContDiff ℝ 1 p)
    (hq : Continuous q) (hf : Continuous f)
    (hp_lower : ∀ t ∈ Set.Icc a b, p₀ ≤ p t)
    (hq_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ q t) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧
      IsMinOn (apm_m95A03_energy a b p q f)
        (apm_m95A03_admissible a b 0 0) u := by
  sorry

theorem apm_m95A03_minimizers_eqOn
    (a b p₀ : ℝ) (hab : a < b) (hp₀ : 0 < p₀)
    (p q f u v : ℝ → ℝ)
    (hp_lower : ∀ t ∈ Set.Icc a b, p₀ ≤ p t)
    (hq_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ q t)
    (hu2 : ContDiff ℝ 2 u)
    (humin : IsMinOn (apm_m95A03_energy a b p q f)
      (apm_m95A03_admissible a b 0 0) u)
    (hv2 : ContDiff ℝ 2 v)
    (hvmin : IsMinOn (apm_m95A03_energy a b p q f)
      (apm_m95A03_admissible a b 0 0) v) :
    Set.EqOn v u (Set.Icc a b) := by
  sorry

theorem apm_m95a03
    (a b α β p₀ : ℝ) (hab : a < b) (hp₀ : 0 < p₀)
    (p q f : ℝ → ℝ)
    (hp : ContDiff ℝ 1 p)
    (hq : Continuous q) (hf : Continuous f)
    (hp_lower : ∀ t ∈ Set.Icc a b, p₀ ≤ p t)
    (hq_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ q t) :
    (∀ u : ℝ → ℝ,
      ContDiff ℝ 2 u → u a = α → u b = β →
      (apm_m95A03_solves a b α β p q f u ↔
        IsMinOn (apm_m95A03_energy a b p q f)
          (apm_m95A03_admissible a b α β) u)) ∧
    (∀ u : ℝ → ℝ,
      let w := apm_m95A03_boundaryLift a b α β
      apm_m95A03_solves a b α β p q f u ↔
        apm_m95A03_solves a b 0 0 p q
          (apm_m95A03_modifiedRHS p q f w) (u - w)) ∧
    ∃ u : ℝ → ℝ,
      ContDiff ℝ 2 u ∧
      IsMinOn (apm_m95A03_energy a b p q f)
        (apm_m95A03_admissible a b 0 0) u ∧
      ∀ v : ℝ → ℝ, ContDiff ℝ 2 v →
        IsMinOn (apm_m95A03_energy a b p q f)
          (apm_m95A03_admissible a b 0 0) v →
        Set.EqOn v u (Set.Icc a b) := by
  constructor
  · intro u hu2 hua hub
    constructor
    · exact apm_m95A03_isMinOn_of_solves a b α β p₀ hab hp₀ p q f u
        hp hq hf hp_lower hq_nonneg
    · exact apm_m95A03_solves_of_isMinOn a b α β p₀ hab hp₀ p q f u
        hp hq hf hp_lower hq_nonneg hu2 hua hub
  constructor
  · exact apm_m95A03_homogenization a b α β hab p q f
  · obtain ⟨u, hu2, humin⟩ :=
      apm_m95A03_exists_homogeneous_minimizer a b p₀ hab hp₀ p q f
        hp hq hf hp_lower hq_nonneg
    refine ⟨u, hu2, humin, ?_⟩
    intro v hv2 hvmin
    exact apm_m95A03_minimizers_eqOn a b p₀ hab hp₀ p q f u v
      hp_lower hq_nonneg hu2 humin hv2 hvmin

#print axioms apm_m95a03
