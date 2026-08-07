import Mathlib

/-!
# APM m95A03: the Dirichlet principle for a Sturm--Liouville problem

## Statement repairs

None. The problem asks for appropriate hypotheses; we take `a < b`, `p ∈ C¹`
uniformly positive, and continuous `q ≥ 0` and `f`.

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
    ∃! u : ℝ → ℝ,
      ContDiff ℝ 2 u ∧
      IsMinOn (apm_m95A03_energy a b p q f)
        (apm_m95A03_admissible a b 0 0) u := by
  /-
  SKIPPED (frozen-statement defect).  The final `∃!` asserts literal equality
  of globally defined functions, but both `apm_m95A03_energy` and
  `apm_m95A03_admissible` inspect a candidate only on `[a,b]` (apart from the
  global regularity predicate).  Consequently, if `u` is any `C²` minimizer,
  adding a nonzero smooth bump supported in an interval strictly to the right
  of `b` gives a different global `C²` function with the same endpoint data,
  the same derivatives on `[a,b]`, and exactly the same energy.  Hence global
  uniqueness is impossible.  The conclusion must instead use `Set.EqOn` on
  `Icc a b`, functions on the interval subtype, or a canonical extension.

  This is the same defect documented in sibling `m02A05`, whose frozen ODE
  statement also incorrectly upgrades interval agreement to global function
  equality. Mathlib's `ContDiffBump` library confirms this counterexample
  directly: `ContDiffBump.support_eq` identifies the support with its chosen
  ball, while its coercion is smooth by the `ContDiff.contDiffBump` API; a
  center beyond `b` and sufficiently small outer radius gives the required
  perturbation. The fully closed artifact scan supplied no quotient/extension
  convention that changes the meaning of equality here.

  Even after repairing uniqueness, the intended analytic proof would require
  an interval integration-by-parts theorem, the fundamental lemma of the
  calculus of variations for the chosen global `ContDiff` representation,
  coercive minimization/Lax--Milgram, and one-dimensional regularity.  Searches
  of `LEMMA-INDEX.md`, Mathlib, `ConstructionTargets/`, and `YoungL2.lean`
  found no assembled theorem bridging those layers.  Partial siblings
  `m98A06`, `m01J06`, and `m99A01` stop at the fundamental-lemma/integration-
  by-parts boundary, while `m95A05` records the absence of a packaged
  Lax--Milgram route for its custom encoding.  Since the theorem is already
  false before those analytic issues arise, no local replacement was made.
  -/
  sorry
