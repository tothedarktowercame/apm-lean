

# APM a94J02: AC strictly monotone integrable function with h' = 0 on a positive-measure set

## 1. Informal proof

**Why it's hard.** The requirements seem contradictory: strictly monotone means h is always increasing, yet h' = 0 on a set of positive measure means h is "flat" in a derivative sense on a substantial set. For smooth functions, h' > 0 wherever h is strictly increasing, so the construction must exploit the gap between pointwise derivative and strict monotonicity that only exists for non-smooth functions.

**The key insight.** Use a "fat Cantor set" (a nowhere-dense closed set C ⊂ [0,1] with m(C) > 0) and define h as the integral of a strictly positive L¹ function that concentrates most of its mass on [0,1] \ C. Specifically, let g be a nonneg L¹ function with g > 0 on [0,1] \ C and g = 0 on C, then h(x) = ∫₋∞ˣ g(t) dt + εx for a small ε > 0. The εx term makes h strictly monotone, but since g = 0 on C and ε can be made part of a decaying envelope, h' = g + ε, which... actually that makes h' > 0 everywhere.

Better construction: use h(x) = ∫₋∞ˣ g(t) dt where g ≥ 0, g > 0 a.e. on (0,1) \ C, g = 0 on C, but this gives h constant on intervals complementary to C... no, C is nowhere dense, so (0,1) \ C is dense.

Actually the cleanest: let C be a fat Cantor set with m(C) = 1/2, and let g = 1_{[0,1]\C}. Then h(x) = ∫₀ˣ g(t) dt is AC, nondecreasing, h' = g = 0 on C (measure 1/2). But h is NOT strictly monotone: it's constant on any interval contained in C. Since C is nowhere dense, every interval intersects [0,1]\C, so h is actually strictly monotone on [0,1]? No: C is nowhere dense means every interval contains points of [0,1]\C, so h increases on every interval. But need strict: h(x) < h(y) whenever x < y.

Yes! If x < y, then (x,y) contains a point of [0,1]\C (since C is nowhere dense), and near that point g > 0, so ∫ₓʸ g > 0, hence h(y) > h(x). So h is strictly monotone. And h' = g = 0 on C with m(C) > 0. ✓

For integrability on all of ℝ: extend by h(x) = 0 for x ≤ 0 and h(x) = h(1)·e^{-(x-1)} for x > 1, or simply define h(x) = e^{-x²} · H(x) where H is the construction above. Alternatively, set g(t) = e^{-t²} · 1_{ℝ\C'}(t) where C' is a fat Cantor set inside [0,1]. Then h(x) = ∫₋∞ˣ g(t) dt is AC, integrable (since h(x) → 0 as x → -∞ and h(x) → ∫g < ∞ as x → +∞ — but h need not be integrable; it converges to a constant). For integrability, multiply by a decaying envelope: h(x) = e^{-x²} ∫₀ˣ 1_{[0,1]\C}(t)dt works — but checking AC and h'=0 on C requires care.

Simplest construction satisfying all conditions:

**Proof/Construction.**

Let C ⊂ [0,1] be a fat Cantor set (nowhere dense, closed, m(C) = 1/2).

Define g : ℝ → ℝ by g(t) = 1_{[0,1]\C}(t) · e^{-t²}. Then g ∈ L¹(ℝ), g ≥ 0.

Define h(x) = e^{-x²} + ∫₋∞ˣ g(t) dt. Then:

Hmm, that's not right either — h(x) → 1 + ∫g as x → ∞, not integrable.

Let me just construct on [0,1] (the problem says "on ℝ" but the construction is the key):

h(x) = ∫₀ˣ 1_{[0,1]\C}(t) dt for x ∈ [0,1].

- AC: h is the integral of an L¹ function. ✓
- Nonneg: h(0) = 0, h nondecreasing, so h ≥ 0. ✓
- Strictly monotone: if 0 ≤ x < y ≤ 1, then (x,y) meets [0,1]\C (nowhere dense), so ∫ₓʸ 1_{[0,1]\C} > 0, hence h(y) > h(x). ✓
- h' = 1_{[0,1]\C} = 0 on C with m(C) = 1/2 > 0. ✓
- Integrable on [0,1]: h is bounded (0 ≤ h ≤ 1/2), so ∫₀¹ h < ∞. ✓

To extend to ℝ with h integrable: define h(x) = 0 for x < 0, h(x) = above for x ∈ [0,1], and h(x) = h(1)·e^{-(x-1)} for x > 1. Then h is still nonneg, continuous, strictly monotone on [0,1], decreasing for x > 1 — WAIT, that breaks strict monotonicity on all of ℝ. The problem says "strictly monotone on ℝ."

OK: redefine. Let φ(x) = e^{-|x|}/4. Let ψ(x) = ∫₀ˣ 1_{[0,1]\C}(t) dt. Define h = φ + ψ on [0,1]. Outside [0,1], h = φ. Then h' = φ' + ψ' on [0,1]. On C: ψ' = 0, h' = φ' = -sign(x)e^{-|x|}/4. For x ∈ C ⊂ [0,1], h'(x) = -e^{-x}/4 < 0. Not monotone.

Actually, the problem just says "on ℝ" but likely means "on [0,1]" or an interval. If truly on all of ℝ and integrable, then h(x) → 0 as x → ±∞, contradicting strict monotonicity (which requires h to be unbounded or at least non-convergent in both directions). So "integrable" + "strictly monotone" on ℝ is impossible for a nonneg function (h increasing ⟹ h(x) → L > 0 as x → ∞, but then h ≥ L on [0,∞), not integrable unless L = 0, which contradicts strict monotonicity from the left).

So the problem must mean on a compact interval, say [0,1]. The construction is:

**h(x) = ∫₀ˣ 1_{[0,1]\C}(t) dt** where C is a fat Cantor set with m(C) > 0.

This satisfies all four conditions on [0,1]: AC, nonneg, strictly monotone, h' = 0 on C. ∎

**What connects.** This construction uses a fat Cantor set — a nowhere dense set of positive measure — which is one of the classic pathological objects in real analysis. The key tension is between "strictly monotone" (topological — needs increase on every interval, hence uses nowhere-denseness of C) and "h'=0 on a big set" (measure-theoretic — uses positive measure of C). The fat Cantor set resolves this because it is simultaneously "topologically small" (nowhere dense) and "measure-theoretically large" (positive measure). This is the standard example showing that the Cantor function's pathology (derivative zero a.e. but monotone) can be partially replicated in the AC setting, though AC prevents the function from being singular.

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Basic

open MeasureTheory Set

noncomputable section

/-- A fat Cantor set: nowhere dense, closed, positive measure. -/
lemma exists_fat_cantor :
    ∃ C : Set ℝ, C ⊆ Icc 0 1 ∧ IsClosed C ∧
      Interior C = ∅ ∧ 0 < volume C := by
  sorry

/-- Main theorem: there exists h satisfying all four conditions on [0,1]. -/
theorem exists_ac_strictly_mono_deriv_zero_on_pos_measure :
    ∃ (h : ℝ → ℝ),
      -- absolutely continuous on [0,1]
      (∀ a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 → a ≤ b →
        h b - h a = ∫ x in a..b, deriv h x) ∧
      -- nonneg
      (∀ x ∈ Icc (0:ℝ) 1, 0 ≤ h x) ∧
      -- strictly monotone on [0,1]
      (StrictMonoOn h (Icc 0 1)) ∧
      -- h' = 0 on a set of positive measure
      (0 < volume {x ∈ Icc (0:ℝ) 1 | deriv h x = 0}) := by
  sorry

/-- The construction: h(x) = ∫₀ˣ 1_{[0,1]\C} dt. -/
def fatCantorIntegral (C : Set ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..x, (Cᶜ ∩ Icc 0 1).indicator (fun _ => (1:ℝ)) t

/-- The constructed function is AC. -/
lemma fatCantorIntegral_absolutelyContinuous (C : Set ℝ) (hC : MeasurableSet C) :
    ∀ a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 → a ≤ b →
      fatCantorIntegral C b - fatCantorIntegral C a =
        ∫ x in a..b, (Cᶜ ∩ Icc 0 1).indicator (fun _ => (1:ℝ)) x := by
  sorry

/-- Strictly monotone when C is nowhere dense. -/
lemma fatCantorIntegral_strictMonoOn
    {C : Set ℝ} (hC_sub : C ⊆ Icc 0 1) (hC_nd : Interior C = ∅) :
    StrictMonoOn (fatCantorIntegral C) (Icc 0 1) := by
  sorry

/-- Derivative is 0 on C. -/
lemma fatCantorIntegral_deriv_zero_on
    {C : Set ℝ} (hC : MeasurableSet C) (hC_sub : C ⊆ Icc 0 1) :
    ∀ᵐ x ∂(volume.restrict C), deriv (fatCantorIntegral C) x = 0 := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.volume` — Lebesgue measure
- `Set.Icc 0 1` — the interval [0,1]
- `Set.indicator` — indicator/characteristic function
- `StrictMonoOn f S` — strict monotonicity on a set
- `Interior C` — interior of a set (for nowhere dense: Interior C = ∅)
- `IsClosed C` — closed set
- `intervalIntegral` — ∫ in a..b

**Key lemmas:**
- `intervalIntegral.integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae` / FTC variants — relating the integral of an L¹ function to an AC antiderivative
- `intervalIntegral.integral_pos_of_pos_of_support` — ∫ₐᵇ g > 0 when g > 0 on a set meeting (a,b). Key for strict monotonicity
- `MeasureTheory.integral_indicator` — computing ∫ 1_S
- `dense_compl_of_isClosed_of_interior_eq_empty` — complement of a nowhere-dense closed set is dense (so every interval meets [0,1]\C)
- `MeasureTheory.ae_restrict_of_ae` — a.e. statements on restricted measures
- `Real.volume_Icc` — measure of intervals
- `IsCompact.exists_isClopen_of_isTopologicalBasis` — not directly, but existence of fat Cantor sets
- `MeasureTheory.integral_nonneg` — ∫ g ≥ 0 when g ≥ 0

**Tactic hints:**
- `refine ⟨fatCantorIntegral C, ?_, ?_, ?_, ?_⟩` — packaging the four properties
- `exact fatCantorIntegral_strictMonoOn hC_sub hC_nd` — applying strict monotonicity lemma
- `simp [fatCantorIntegral, intervalIntegral.integral_indicator]` — unfolding the definition
- `positivity` — for volume positivity
- `exact?` — finding the right FTC / indicator integral lemma
- `intro x hx; simp [Set.indicator, Set.mem_compl_iff]` — for the derivative computation
- `linarith` — combining bounds