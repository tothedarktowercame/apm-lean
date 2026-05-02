# Proof outline — a97A05

Source: claude-1 batch 20260502 (sequence apm-daily-batch.md).

## Theorem statements (Lean)

```lean
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.Analytic.Basic

open Complex Set

noncomputable section

/-- The open upper half-plane in ℂ. -/
def UHP : Set ℂ := {z : ℂ | 0 < z.im}

/-- The open right half-plane in ℂ. -/
def RHP : Set ℂ := {z : ℂ | 0 < z.re}

/-- The Cayley-type map (w - 1)/(w + 1) sends the right half-plane to the
    open unit disk. -/
theorem apm_a97A05_cayley_maps_RHP_to_disk
    (w : ℂ) (hw : 0 < w.re) :
    ‖(w - 1) / (w + 1)‖ < 1 := by sorry

/-- Helper: shifting f by (M + 1) sends Re(f) ≥ -M into RHP. -/
theorem apm_a97A05_shift_to_RHP
    (f : ℂ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hbdd : ∀ z ∈ UHP, |(f z).re| ≤ M) :
    ∀ z ∈ UHP, 0 < ((f z) + (M + 1)).re := by sorry

/-- Auxiliary bounded function ψ = (f₁ - 1)/(f₁ + 1) where f₁ = f + (M+1). -/
def apm_a97A05_psi (f : ℂ → ℂ) (M : ℝ) (z : ℂ) : ℂ :=
  ((f z) + M) / ((f z) + (M + 2))

theorem apm_a97A05_psi_bdd
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f UHP)
    (M : ℝ) (hM : 0 ≤ M)
    (hbdd : ∀ z ∈ UHP, |(f z).re| ≤ M) :
    ∀ z ∈ UHP, ‖apm_a97A05_psi f M z‖ < 1 := by sorry

theorem apm_a97A05_psi_analytic
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f UHP)
    (M : ℝ) (hM : 0 ≤ M)
    (hbdd : ∀ z ∈ UHP, |(f z).re| ≤ M) :
    AnalyticOn ℂ (apm_a97A05_psi f M) UHP := by sorry

/-- Main theorem: an analytic function on H with bounded real part is the
    quotient of two bounded analytic functions on H. -/
theorem apm_a97A05_main
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f UHP)
    (M : ℝ) (hM : 0 ≤ M)
    (hbdd : ∀ z ∈ UHP, |(f z).re| ≤ M) :
    ∃ (g h : ℂ → ℂ) (Cg Ch : ℝ),
      AnalyticOn ℂ g UHP ∧
      AnalyticOn ℂ h UHP ∧
      (∀ z ∈ UHP, ‖g z‖ ≤ Cg) ∧
      (∀ z ∈ UHP, ‖h z‖ ≤ Ch) ∧
      (∀ z ∈ UHP, h z ≠ 0) ∧
      (∀ z ∈ UHP, f z = g z / h z) := by sorry
```


## Mathlib cross-references

**Types/structures:**
- `ℂ` / `Complex` — the complex numbers
- `Complex.re`, `Complex.im` — real/imaginary parts
- `AnalyticOn ℂ f S`, `AnalyticAt ℂ f z` — analyticity
- `UpperHalfPlane` — Mathlib's upper half-plane (subtype, may or may not be needed)
- `Set.Ioi`, `Set.Icc` — interval primitives
- `Metric.ball (0:ℂ) 1` — open unit disk

**Key lemmas:**
- `Complex.normSq_eq_abs` / `Complex.sq_abs` — |z|² = z·z̄
- `Complex.normSq_add`, `Complex.normSq_sub` — |a ± b|² expansions
- `Complex.add_re`, `Complex.add_im` — real/imaginary parts of sum
- `Complex.sub_re`, `Complex.div_re`, `Complex.mul_re` — algebra of re/im
- `Complex.abs_div` — |z/w| = |z|/|w|
- `AnalyticOn.add`, `AnalyticOn.sub`, `AnalyticOn.mul`, `AnalyticOn.div` — closure properties
- `AnalyticOn.const_add` / `AnalyticOn.const_smul` — shifting/scaling
- `analyticOn_const` — constant function analyticity
- `analyticOn_id` — identity is analytic
- `Complex.differentiable_id` / `differentiableAt_const`
- `div_ne_zero_iff` — denominator nonvanishing
- `Complex.norm_eq_abs` — bridge to `Complex.abs`
- `sub_eq_zero` / `eq_div_iff` — algebraic manipulation of f = g/h
- `Complex.add_div`, `Complex.div_add_div` — fraction algebra
- `IsOpen.upperHalfPlane` / `Complex.isOpen_setOf_im_pos` — UHP is open
- `norm_le_one_iff_normSq_le_one` — |z| < 1 ⟺ |z|² < 1
- `Complex.normSq_pos` — |z|² > 0 if z ≠ 0

**Tactic hints:**
- `field_simp` — clear (f + 1), (1 - ψ) denominators
- `ring` / `ring_nf` — verify f = (g₁ - g₂)/h₁ algebra after clearing denominators
- `nlinarith` — close (Re(w))²-based inequalities like |w-1|² < |w+1|² for Re(w) > 0
- `positivity` — for M ≥ 0, |ψ|² > 0, etc.
- `apply AnalyticOn.div` / `apply AnalyticOn.add` — assemble analyticity
- `simp [Complex.normSq, Complex.sub_re, Complex.add_re]` — expand norm squared
- `gcongr` — monotonicity in bound chains
- `intro z hz` — work pointwise on UHP
- `refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` — assemble the seven-part witness
- `exact?` / `apply?` — search for Möbius / Cayley lemmas
- `have hne : (f z) + (M + 2) ≠ 0 := by ...` — nonvanishing side condition
- `rcases hbdd z hz with ⟨_, _⟩` — destructure two-sided bound

## Blockers

- All theorem bodies are `sorry`. Codex cleanup pass to attempt closure.
- Mathlib lemma names above are conjectural — verify via `exact?` / `apply?`.
