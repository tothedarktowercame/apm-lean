

## 1. Informal proof

**Why it's hard:** The space X = L^p + L^q is not a standard L^r space, so completeness doesn't follow from the usual Riesz-Fischer theorem directly. You have to work with the infimum definition of the norm, which means Cauchy sequences in X must be carefully decomposed into convergent pieces in L^p and L^q separately.

**The key insight:** X = L^p + L^q is isometrically isomorphic to the quotient of the product space L^p × L^q by the closed subspace {(g, -g) : g ∈ L^p ∩ L^q}. Since L^p × L^q (with norm ‖(g,h)‖ = ‖g‖_p + ‖h‖_q) is a Banach space and the kernel of the addition map is closed, the quotient is automatically a Banach space.

**Proof:**

*X is a vector space.* If f₁ = g₁ + h₁ and f₂ = g₂ + h₂ with gᵢ ∈ L^p, hᵢ ∈ L^q, then f₁ + f₂ = (g₁ + g₂) + (h₁ + h₂) ∈ X and αf₁ = αg₁ + αh₁ ∈ X. The zero function is 0 + 0 ∈ X. So X is closed under addition and scalar multiplication.

*‖·‖_X is a norm.* First, ‖f‖_X ≥ 0 is immediate. For homogeneity: ‖αf‖_X = inf{‖g‖_p + ‖h‖_q : αf = g + h} = inf{‖αg'‖_p + ‖αh'‖_q : f = g' + h'} = |α| · ‖f‖_X. For the triangle inequality: given ε > 0, choose decompositions f₁ = g₁ + h₁ and f₂ = g₂ + h₂ with ‖gᵢ‖_p + ‖hᵢ‖_q ≤ ‖fᵢ‖_X + ε. Then f₁ + f₂ = (g₁ + g₂) + (h₁ + h₂), so ‖f₁ + f₂‖_X ≤ ‖g₁ + g₂‖_p + ‖h₁ + h₂‖_q ≤ (‖g₁‖_p + ‖g₂‖_p) + (‖h₁‖_q + ‖h₂‖_q) ≤ ‖f₁‖_X + ‖f₂‖_X + 2ε. Since ε is arbitrary, ‖f₁ + f₂‖_X ≤ ‖f₁‖_X + ‖f₂‖_X.

For definiteness: suppose ‖f‖_X = 0. Then there exist sequences gₙ ∈ L^p, hₙ ∈ L^q with f = gₙ + hₙ and ‖gₙ‖_p + ‖hₙ‖_q → 0. So gₙ → 0 in L^p and hₙ → 0 in L^q. Both converge to 0 in measure (since [0,1] has finite measure and p, q ≥ 1). Hence f = gₙ + hₙ → 0 in measure, so f = 0 a.e.

*Completeness.* Consider the surjective linear map T: L^p × L^q → X defined by T(g, h) = g + h, where L^p × L^q carries the norm ‖(g,h)‖ = ‖g‖_p + ‖h‖_q. The kernel K = {(g, -g) : g ∈ L^p ∩ L^q} is closed: if (gₙ, -gₙ) → (u, v) in L^p × L^q, then gₙ → u in L^p and gₙ → -v in L^q; passing to subsequences converging a.e., u = -v a.e., so (u, v) = (u, -u) ∈ K.

By definition, ‖f‖_X = inf{‖(g,h)‖ : T(g,h) = f} = ‖(g,h) + K‖_{(L^p × L^q)/K}, so T induces an isometric isomorphism X ≅ (L^p × L^q)/K. Since L^p × L^q is a Banach space (both factors are complete under Riesz-Fischer) and K is a closed subspace, the quotient (L^p × L^q)/K is a Banach space. Therefore X is complete.

**What connects:** The quotient-of-product technique is the standard way to show sum spaces are Banach. The finite measure of [0,1] is used twice: it ensures L^q ⊂ L^p (since q > p and ν([0,1]) = 1), which means X = L^p as a set — but with a potentially different (in fact equivalent) norm. It also ensures convergence in L^p or L^q implies convergence in measure, which is needed for the definiteness argument. The closedness of the kernel K uses the fact that L^p ∩ L^q convergence can be checked via subsequences converging a.e.

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.NormedSpace.BanachQuotient
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

noncomputable section

variable {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p ≤ q)
variable (μ : Measure (Set.Icc (0:ℝ) 1))

/-- The sum space L^p + L^q as the range of the addition map from L^p × L^q. -/
def LpSumSpace (p q : ℝ≥0∞) (μ : Measure (Set.Icc (0:ℝ) 1)) :
    Set (Lp ℝ p μ → Lp ℝ q μ → Lp ℝ 1 μ) :=
  sorry

/-- The sum norm on L^p + L^q. -/
def lpSumNorm (p q : ℝ≥0∞) (μ : Measure (Set.Icc (0:ℝ) 1))
    (f : MeasureTheory.AEEqFun μ) : ℝ :=
  sorry

/-- The kernel of the addition map T(g,h) = g + h is closed in L^p × L^q. -/
theorem apm_a96J05_kernel_closed
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (μ : Measure (Set.Icc (0:ℝ) 1)) [IsFiniteMeasure μ] :
    IsClosed {gh : (Lp ℝ p μ) × (Lp ℝ q μ) | gh.1 + gh.2 = 0} := by sorry

/-- The sum norm is a seminorm (triangle inequality and homogeneity). -/
theorem apm_a96J05_sum_seminorm
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (μ : Measure (Set.Icc (0:ℝ) 1)) [IsFiniteMeasure μ]
    (f₁ f₂ : Lp ℝ p μ) :
    True := by sorry  -- placeholder: seminorm properties

/-- The sum norm is definite: ‖f‖_X = 0 implies f = 0 a.e. -/
theorem apm_a96J05_sum_norm_definite
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p ≤ q)
    (μ : Measure (Set.Icc (0:ℝ) 1)) [IsFiniteMeasure μ]
    (f : MeasureTheory.AEEqFun μ)
    (hf : ∀ ε > (0:ℝ), ∃ (g : Lp ℝ p μ) (h : Lp ℝ q μ),
      (↑g + ↑h : MeasureTheory.AEEqFun μ) = f ∧
      ‖g‖ + ‖h‖ < ε) :
    f = 0 := by sorry

/-- Main theorem: L^p + L^q with the sum norm is a Banach space,
    via isometric isomorphism with the quotient (L^p × L^q) / ker(T). -/
theorem apm_a96J05_main
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p ≤ q)
    (μ : Measure (Set.Icc (0:ℝ) 1)) [IsFiniteMeasure μ] :
    CompleteSpace ((Lp ℝ p μ) × (Lp ℝ q μ) ⧸
      ({gh : (Lp ℝ p μ) × (Lp ℝ q μ) | gh.1 + gh.2 = 0} : Set _).toFinset.toSubmodule) := by
  sorry
```

Note: The Lean 4 formalization is awkward because Mathlib doesn't have a direct `Lp + Lq` sum space construction. The cleanest route is through the quotient of the product, but the submodule/quotient coercion requires care. A realistic formalization would define a custom `SumLp` type and build the `NormedAddCommGroup` and `CompleteSpace` instances on it.

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.Lp` — the L^p space as a subtype of `AEEqFun`
- `MeasureTheory.AEEqFun` — equivalence classes of a.e.-equal functions
- `MeasureTheory.Measure` — measure type
- `MeasureTheory.IsFiniteMeasure` — typeclass for finite measures
- `ENNReal` (`ℝ≥0∞`) — extended nonneg reals for the exponent
- `NormedAddCommGroup` — the normed group structure on Lp
- `CompleteSpace` — typeclass for Banach property
- `Submodule.Quotient` / `HasQuotient` — quotient of normed spaces
- `Prod.instNormedAddCommGroup` — product norm on L^p × L^q

**Key lemmas:**
- `MeasureTheory.Lp.instCompleteSpace` — L^p is complete (Riesz-Fischer)
- `MeasureTheory.Lp.instNormedAddCommGroup` — norm structure on Lp
- `MeasureTheory.snorm_mono_measure` — snorm monotonicity
- `MeasureTheory.Memℒp.mono` — if f ∈ L^q and q ≥ p on finite measure, then f ∈ L^p
- `MeasureTheory.Lp.tendsto_Lp_iff_tendsto_ℒp` — convergence in Lp
- `MeasureTheory.TendstoInMeasure.of_tendsto_snorm` — L^p convergence implies convergence in measure
- `Submodule.Quotient.instCompleteSpace` — quotient of Banach by closed subspace is Banach
- `IsClosed.isComplete` — closed subspace of complete space is complete
- `NormedAddGroupHom.ker` — kernel of a normed group hom
- `Metric.cauchySeq_iff` — characterization of Cauchy sequences
- `MeasureTheory.ae_eq_of_tendsto_measure` — a.e. equality from measure-theoretic convergence

**Tactic hints:**
- `refine` / `exact` — for assembling the quotient isomorphism
- `positivity` — for norm nonnegativity goals
- `gcongr` — for inequality chaining (norm estimates)
- `calc` — for the triangle inequality chain
- `filter_upwards` — for a.e. arguments
- `exact?` / `apply?` — searching for the right Mathlib quotient-completeness lemma
- `continuity` — for showing the addition map is continuous
- `isClosed_iff_clusterPt` / `isSeqClosed` — for kernel closedness via sequential characterization