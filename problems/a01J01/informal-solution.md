

# APM a01J01: Uniform integrability from L³ bounds (equi-integrability)

## Why It's Hard

Part (a) asks for **uniform** absolute continuity of the integrals: the same δ must work for *all* n simultaneously. If you only had one function f with ∫|f|³ ≤ 1, then absolute continuity of the integral gives δ depending on f. But with infinitely many f\_n, you can't just take the minimum of infinitely many δ's. The L³ bound provides the extra room via Hölder's inequality, which gives a *uniform* bound that depends on m(E) but not on n. Part (b) shows that L¹ bounds alone lack this room — concentration on shrinking sets can defeat uniform absolute continuity.

## The Key Insight

**(a)** Hölder's inequality with exponents 3 and 3/2: ∫\_E |f\_n| ≤ ||f\_n||\_{L³} · m(E)^{2/3}. Since ||f\_n||\_{L³} ≤ 1, we get ∫\_E |f\_n| ≤ m(E)^{2/3}, which is < ε whenever m(E) < δ = ε^{3/2}. The bound is uniform in n because the Hölder estimate only uses the L³ norm.

**(b)** The sequence f\_n = n · 1\_{[0,1/n]} has ∫|f\_n| = 1 for all n, but ∫\_{[0,1/n]} |f\_n| = 1 while m([0,1/n]) = 1/n → 0. So no δ works uniformly: for any δ > 0, take n > 1/δ and E = [0, 1/n].

## Complete Proof

### Part (a): Uniform absolute continuity from L³ bounds

**Theorem.** Let f\_n : [0,1] → ℝ be measurable with ∫₀¹ |f\_n|³ dm ≤ 1 for all n. Then for every ε > 0 there exists δ > 0 such that for every measurable E ⊆ [0,1] with m(E) < δ and every n ∈ ℕ: ∫\_E |f\_n| dm < ε.

**Proof.** Fix ε > 0. Apply Hölder's inequality with p = 3 and q = 3/2 (so 1/p + 1/q = 1/3 + 2/3 = 1):

$$\int_E |f_n|\,dm = \int_E |f_n| \cdot 1\,dm \leq \left(\int_E |f_n|^3\,dm\right)^{1/3} \cdot \left(\int_E 1^{3/2}\,dm\right)^{2/3}.$$

The first factor satisfies (∫\_E |f\_n|³)^{1/3} ≤ (∫₀¹ |f\_n|³)^{1/3} ≤ 1. The second factor is m(E)^{2/3}. So:

$$\int_E |f_n|\,dm \leq 1 \cdot m(E)^{2/3} = m(E)^{2/3}.$$

Set δ = ε^{3/2}. Then m(E) < δ implies m(E)^{2/3} < (ε^{3/2})^{2/3} = ε. So ∫\_E |f\_n| < ε for all n. ∎

### Part (b): Counterexample with only L¹ bounds

**Claim.** There exist measurable f\_n : [0,1] → ℝ with ∫₀¹ |f\_n| dm ≤ 1 for all n, but the uniform absolute continuity conclusion fails.

**Construction.** Define f\_n = n · 1\_{[0, 1/n]}.

**L¹ bound:** ∫₀¹ |f\_n| dm = n · m([0, 1/n]) = n · (1/n) = 1 ≤ 1. ✓

**Failure of uniform absolute continuity:** Let ε = 1/2. For any δ > 0, choose n > 1/δ and set E = [0, 1/n]. Then m(E) = 1/n < δ, but:

$$\int_E |f_n|\,dm = n \cdot \frac{1}{n} = 1 > \frac{1}{2} = \varepsilon.$$

So no δ works for all n simultaneously. ∎

**Why L¹ fails but L³ works.** The f\_n = n · 1\_{[0,1/n]} satisfy ∫|f\_n| = 1 but ∫|f\_n|³ = n³ · (1/n) = n² → ∞. They are not bounded in L³. The L³ bound prevents concentration: if a function has large values on a small set, the cube amplifies those values disproportionately, forcing either the L³ norm to be large or the function to be moderate. The L¹ norm doesn't penalise concentration enough.

## What Connects

**To equi-integrability (uniform integrability).** Part (a) proves that a family bounded in Lp (p > 1) is uniformly integrable (equi-integrable). This is a standard sufficient condition. Part (b) shows that Lp = L¹ (p = 1) is the critical case where this fails.

**To the Vitali convergence theorem.** The Vitali convergence theorem says: if f\_n → f in measure and {f\_n} is uniformly integrable on a finite measure space, then f\_n → f in L¹. Part (a) provides the uniform integrability hypothesis whenever the family is Lp-bounded for p > 1.

**To the Dunford-Pettis theorem.** The Dunford-Pettis theorem characterises relatively weakly compact subsets of L¹: they are exactly the uniformly integrable families. Part (a) shows that Lp-bounded sets (p > 1) are relatively weakly compact in L¹.

**To the de la Vallée-Poussin criterion.** A family is uniformly integrable if and only if it is bounded by a function with superlinear growth: sup\_n ∫ Φ(|f\_n|) < ∞ for some convex Φ with Φ(t)/t → ∞. Here Φ(t) = t³ satisfies this.

**To problem a01J01 from the same exam.** This is closely related to a00J04 (weak-Lp estimates) — both problems use Hölder's inequality to convert a stronger integrability condition into a uniform control on integrals over small sets.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Set ENNReal Filter

noncomputable section

/-- The L³-bounded family hypothesis. -/
def L3Bounded (f : ℕ → ℝ → ℝ) : Prop :=
  ∀ n, ∫ t in Icc (0 : ℝ) 1, ‖f n t‖ ^ 3 ∂volume ≤ 1

/-- Hölder's inequality gives the uniform bound:
    ∫_E |f_n| ≤ (∫_E |f_n|³)^{1/3} · m(E)^{2/3} ≤ m(E)^{2/3}. -/
lemma integral_le_measure_rpow
    {f : ℕ → ℝ → ℝ} (hf : L3Bounded f)
    (hfm : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Icc 0 1)))
    {E : Set ℝ} (hE : MeasurableSet E) (hEsub : E ⊆ Icc 0 1)
    (n : ℕ) :
    ∫ t in E, ‖f n t‖ ∂volume ≤ (volume E).toReal ^ (2 / 3 : ℝ) := by
  sorry

/-- Part (a): uniform absolute continuity of integrals.
    For all ε > 0, ∃ δ > 0 such that m(E) < δ ⟹ ∫_E |f_n| < ε
    for all n. -/
theorem equi_integrable_of_L3_bound
    {f : ℕ → ℝ → ℝ} (hf : L3Bounded f)
    (hfm : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Icc 0 1)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (E : Set ℝ), MeasurableSet E → E ⊆ Icc 0 1 →
      volume E < ENNReal.ofReal δ →
      ∀ n, ∫ t in E, ‖f n t‖ ∂volume < ε := by
  sorry

/-- The explicit δ = ε^{3/2} works. -/
lemma equi_integrable_delta (ε : ℝ) (hε : 0 < ε) :
    ∀ (E : Set ℝ), volume E < ENNReal.ofReal (ε ^ (3 / 2 : ℝ)) →
      (volume E).toReal ^ (2 / 3 : ℝ) < ε := by
  sorry

/-- Part (b): the counterexample. f_n = n · 𝟙_{[0, 1/n]}. -/
def counterex (n : ℕ) : ℝ → ℝ :=
  (Icc (0 : ℝ) (1 / (↑n + 1))).indicator (fun _ => (↑n + 1 : ℝ))

/-- Each f_n has ∫ |f_n| = 1. -/
lemma counterex_L1_eq_one (n : ℕ) :
    ∫ t in Icc (0 : ℝ) 1, ‖counterex n t‖ ∂volume = 1 := by
  sorry

/-- The L³ norms blow up: ∫ |f_n|³ = (n+1)². -/
lemma counterex_L3_unbounded :
    ¬ ∃ C : ℝ, ∀ n, ∫ t in Icc (0 : ℝ) 1, ‖counterex n t‖ ^ 3 ∂volume ≤ C := by
  sorry

/-- Uniform absolute continuity fails for the counterexample:
    for ε = 1/2, no δ works. -/
theorem counterex_not_equi_integrable :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (E : Set ℝ), MeasurableSet E → E ⊆ Icc 0 1 →
        volume E < ENNReal.ofReal δ →
        ∀ n, ∫ t in E, ‖counterex n t‖ ∂volume < ε) := by
  sorry

/-- The specific failure: E_n = [0, 1/(n+1)] has m(E_n) → 0
    but ∫_{E_n} |f_n| = 1. -/
lemma counterex_concentrates (n : ℕ) :
    ∫ t in Icc (0 : ℝ) (1 / (↑n + 1)),
      ‖counterex n t‖ ∂volume = 1 := by
  sorry

lemma counterex_support_shrinks :
    Tendsto (fun n : ℕ => (1 : ℝ) / (↑n + 1)) atTop (𝓝 0) := by
  sorry

end
```

**Mathlib notes:**

- `∫ t in E, ‖f n t‖ ∂volume` is the Bochner integral of the norm over E — the standard way to express ∫\_E |f\_n| dm in Lean.
- The Hölder inequality used in part (a) is available in Mathlib via `MeasureTheory.NNReal.inner_le_Lnorm_mul_Lnorm` or the more direct `MeasureTheory.integral_mul_le_Lp_mul_Lq`. Here p = 3, q = 3/2.
- `(volume E).toReal ^ (2/3 : ℝ)` converts the ENNReal measure to a real number for the rpow. This is valid since E ⊆ [0,1] gives volume E ≤ 1 < ⊤.
- The counterexample `counterex n` uses `Set.indicator` on `Icc 0 (1/(n+1))` with constant value `n+1` (using `n+1` instead of `n` to avoid division by zero).
- The negation in `counterex_not_equi_integrable` is existential after pushing negations through the quantifiers: there exists ε (namely 1/2) such that for every δ, there exist E and n with m(E) < δ but ∫\_E |f\_n| ≥ ε.
