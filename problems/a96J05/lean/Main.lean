import Mathlib

/-!
# APM a96J05 — the sum of two Lp spaces

## Statement repairs

None.

The underlying measure is Lebesgue measure restricted to `[0,1]`.  Membership
in `L^p + L^q` and the infimum norm are represented directly using Mathlib's
`Lp` and `AEEqFun` types.  Completeness is stated by the Cauchy criterion for
this norm, avoiding any surrogate normed-space structure.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

def apm_a96J05_measure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

def apm_a96J05_mem (p q : ℝ≥0∞)
    (f : AEEqFun ℝ ℝ apm_a96J05_measure) : Prop :=
  ∃ g : Lp ℝ p apm_a96J05_measure,
    ∃ h : Lp ℝ q apm_a96J05_measure,
      (g : AEEqFun ℝ ℝ apm_a96J05_measure) +
        (h : AEEqFun ℝ ℝ apm_a96J05_measure) = f

def apm_a96J05_norm (p q : ℝ≥0∞)
    (f : AEEqFun ℝ ℝ apm_a96J05_measure) : ℝ :=
  sInf {r : ℝ | ∃ g : Lp ℝ p apm_a96J05_measure,
    ∃ h : Lp ℝ q apm_a96J05_measure,
      (g : AEEqFun ℝ ℝ apm_a96J05_measure) +
          (h : AEEqFun ℝ ℝ apm_a96J05_measure) = f ∧
        ‖g‖ + ‖h‖ = r}

/-- On the finite measure space `[0,1]`, `L^q` embeds in `L^p` for `p ≤ q`.
Consequently the algebraic sum encoded by `apm_a96J05_mem` is exactly the
image of `L^p` in `AEEqFun`.  This is the key simplification beyond the
quotient-space approach: completeness can ultimately be inherited directly
from `Lp ℝ p`. -/
lemma apm_a96J05_mem_iff_exists_Lp
    {p q : ℝ≥0∞} (hpq : p ≤ q)
    (f : AEEqFun ℝ ℝ apm_a96J05_measure) :
    apm_a96J05_mem p q f ↔
      ∃ k : Lp ℝ p apm_a96J05_measure,
        (k : AEEqFun ℝ ℝ apm_a96J05_measure) = f := by
  letI : IsFiniteMeasure apm_a96J05_measure := by
    unfold apm_a96J05_measure
    infer_instance
  constructor
  · rintro ⟨g, h, rfl⟩
    have hh : (h : AEEqFun ℝ ℝ apm_a96J05_measure) ∈
        Lp ℝ p apm_a96J05_measure :=
      Lp.antitone hpq h.prop
    let h' : Lp ℝ p apm_a96J05_measure := ⟨h, hh⟩
    refine ⟨g + h', ?_⟩
    rfl
  · rintro ⟨k, rfl⟩
    refine ⟨k, 0, ?_⟩
    simp

theorem apm_a96j05 (p q : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p < q) :
    let X := apm_a96J05_mem p q
    let N := apm_a96J05_norm p q
    -- `X` is a real vector space.
    X 0 ∧
    (∀ f g, X f → X g → X (f + g)) ∧
    (∀ (c : ℝ) f, X f → X (c • f)) ∧
    -- The displayed infimum is a norm on `X`.
    (∀ f, X f → 0 ≤ N f) ∧
    (∀ f, X f → (N f = 0 ↔ f = 0)) ∧
    (∀ (c : ℝ) f, X f → N (c • f) = |c| * N f) ∧
    (∀ f g, X f → X g → N (f + g) ≤ N f + N g) ∧
    -- Every Cauchy sequence in this norm converges in `X`.
    (∀ u : ℕ → AEEqFun ℝ ℝ apm_a96J05_measure,
      (∀ n, X (u n)) →
      (∀ ε > 0, ∃ k, ∀ m ≥ k, ∀ n ≥ k, N (u m - u n) < ε) →
      ∃ f, X f ∧ Tendsto (fun n => N (u n - f)) atTop (nhds 0)) := by
  /-
  CLOSER HOP 2 (2026-08-08): the compiled lemma
  `apm_a96J05_mem_iff_exists_Lp` uses `Lp.antitone` and finiteness of the
  restricted Lebesgue measure to identify the frozen sum space with `L^p`
  itself.  This goes beyond the previous generic quotient observation and
  removes the need to construct an antidiagonal quotient.

  The remaining bridge is the isometry statement for the *literal* `sInf`:
  prove `apm_a96J05_norm p q f = ‖k‖` whenever the `Lp p` element `k` coerces
  to `f`.  The upper bound uses the decomposition `(k,0)`.  The lower bound
  needs the finite-measure norm comparison `‖h_as_Lp_p‖ ≤ ‖h‖_q`; Mathlib's
  `Lp.antitone` gives membership but is not a norm-nonincreasing bundled map,
  so this comparison still requires the measure-one specialization of the
  `eLpNorm` monotonicity theorem and coercion bookkeeping.  Once compiled,
  definiteness, triangle inequality and completeness follow directly from
  the normed complete space `Lp ℝ p`.

  Searches covered `LEMMA-INDEX.md`, all `ConstructionTargets/`, Mathlib's
  `Lp.antitone`, `Lp` completeness and quotient APIs, git history, and related
  artifacts `m95A04` and `m02J05`; none packages this exact `sInf` equality.
  The frozen statement is unchanged and no unproved helper was introduced.
  -/
  sorry
