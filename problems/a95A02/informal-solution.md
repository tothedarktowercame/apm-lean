

# APM a95A02: AC functions satisfy Lusin's condition (N) and preserve measurability

## 1. Informal proof

**Why it's hard.** Part (b) extends the AC condition from finite unions of intervals to *arbitrary* sets E — you need to approximate E by intervals using outer measure regularity. Part (c) goes further: images of measurable sets under AC functions are measurable, which requires (b) plus inner regularity and the fact that continuous images of compact sets are compact (hence measurable).

**The key insight.** (b) is Lusin's condition (N): AC functions map null sets to null sets, and more generally m*(f(E)) is controlled by m*(E). The AC definition directly handles finite unions of intervals; outer regularity extends this to arbitrary E. (c) Write E = K ∪ N where K is σ-compact and N is null; f(K) is σ-compact (hence measurable) and f(N) is null (by (b)), so f(E) = f(K) ∪ f(N) is measurable.

**Proof.**

**(a) Definition.** f : [0,1] → ℝ is absolutely continuous if for every ε > 0 there exists δ > 0 such that for every finite collection of non-overlapping intervals (a₁,b₁), ..., (aₙ,bₙ) in [0,1] with Σ(bₖ-aₖ) < δ, we have Σ|f(bₖ)-f(aₖ)| < ε.

**(b) m*(f(E)) ≤ ε when m*(E) ≤ δ.**

*Case 1: E is a finite union of non-overlapping intervals.* If E = ∪(aₖ,bₖ) with Σ(bₖ-aₖ) < δ, then f maps each [aₖ,bₖ] to an interval of length ≤ sup-inf ≤ max-min over [aₖ,bₖ]. By the intermediate value theorem (f is continuous since AC ⟹ continuous), f([aₖ,bₖ]) is an interval, and its length = sup_{[aₖ,bₖ]} f - inf_{[aₖ,bₖ]} f. This length might exceed |f(bₖ)-f(aₖ)| (f could oscillate within the interval). However, the total variation of f on ∪[aₖ,bₖ] is bounded: the AC condition gives Σ|f(bₖ)-f(aₖ)| < ε, but we need to bound the total oscillation.

Better approach for case 1: use the fact that f is AC, hence f(x) = f(0) + ∫₀ˣ f'(t)dt with f' ∈ L¹. For a subinterval [a,b]: m*(f([a,b])) ≤ ∫ₐᵇ |f'| (the image is contained in an interval of length ≤ the total variation on [a,b]). For a finite union: m*(f(∪[aₖ,bₖ])) ≤ Σ m*(f([aₖ,bₖ])) ≤ Σ ∫_{aₖ}^{bₖ} |f'| = ∫_E |f'|. By absolute continuity of the integral (f' ∈ L¹): given ε > 0, there exists δ > 0 with ∫_E |f'| < ε whenever m(E) < δ.

*Case 2: General E.* Given ε, choose δ from the absolute continuity of the integral for f'. If m*(E) < δ, by definition of outer measure, there exists an open set U ⊇ E with m(U) < δ. Write U = ∪(aₖ,bₖ) (countable union of disjoint open intervals). Then f(E) ⊆ f(U) = ∪f((aₖ,bₖ)), and m*(f(U)) ≤ Σ m*(f([aₖ,bₖ])) ≤ Σ ∫_{aₖ}^{bₖ} |f'| = ∫_U |f'| < ε. ✓

**(c) f(E) is measurable when E is measurable.**

Since E ⊆ [0,1] is measurable, by regularity: E = K ∪ N where K is a countable union of compact sets (Kₘ ↑ K) and m(N) = 0.

- f(Kₘ) is compact (continuous image of compact) hence measurable. So f(K) = ∪f(Kₘ) is an Fσ set, hence measurable.
- m*(N) = 0, so by part (b), m*(f(N)) = 0. A set of outer measure zero is Lebesgue measurable.

f(E) = f(K ∪ N) = f(K) ∪ f(N). Union of two measurable sets is measurable. ✓ ∎

**What connects.** Part (b) is Lusin's condition (N): the property that null sets map to null sets. This is the defining feature that distinguishes absolutely continuous functions from merely continuous or BV functions — the Cantor function is continuous and BV but violates condition (N) (it maps the Cantor set, measure 0, onto [0,1], measure 1). Part (c) shows AC functions preserve measurability — a much stronger statement than just preserving null sets, using the decomposition of measurable sets into σ-compact + null. The result fails for general continuous functions (there exist continuous functions mapping measurable sets to non-measurable sets, via the composition of a continuous surjection onto a Cantor-type set with a non-measurable subset).

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Basic

open MeasureTheory Set

noncomputable section

/-- (a) Absolute continuity on [0,1]. -/
def AbsolutelyContinuousOn (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (n : ℕ) (a b : Fin n → ℝ),
    (∀ i, a i ∈ Icc 0 1) → (∀ i, b i ∈ Icc 0 1) →
    (∀ i, a i ≤ b i) →
    (∀ i j, i < j → b i ≤ a j) →
    ∑ i, (b i - a i) < δ →
    ∑ i, |f (b i) - f (a i)| < ε

/-- (b) Lusin's condition (N): m*(f(E)) is controlled by m*(E). -/
theorem ac_lusin_condition_N
    {f : ℝ → ℝ}
    (hac : AbsolutelyContinuousOn f)
    (hf : ContinuousOn f (Icc 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ E ⊆ Icc (0:ℝ) 1,
      MeasureTheory.OuterMeasure.measureOf volume.toOuterMeasure E < ENNReal.ofReal δ →
      MeasureTheory.OuterMeasure.measureOf volume.toOuterMeasure (f '' E) <
        ENNReal.ofReal ε := by
  sorry

/-- (b) Special case: AC maps null sets to null sets. -/
theorem ac_maps_null_to_null
    {f : ℝ → ℝ}
    (hac : AbsolutelyContinuousOn f)
    (hf : ContinuousOn f (Icc 0 1))
    {E : Set ℝ} (hE : E ⊆ Icc 0 1)
    (hE_null : volume E = 0) :
    volume (f '' E) = 0 := by
  sorry

/-- (c) AC maps measurable sets to measurable sets. -/
theorem ac_maps_measurable_to_measurable
    {f : ℝ → ℝ}
    (hac : AbsolutelyContinuousOn f)
    (hf : ContinuousOn f (Icc 0 1))
    {E : Set ℝ} (hE : E ⊆ Icc 0 1)
    (hE_meas : MeasurableSet E) :
    MeasurableSet (f '' E) := by
  sorry

/-- Measurable set = σ-compact ∪ null (inner regularity). -/
lemma measurableSet_eq_sigma_compact_union_null
    {E : Set ℝ} (hE : MeasurableSet E) (hE_sub : E ⊆ Icc 0 1) :
    ∃ (K : ℕ → Set ℝ) (N : Set ℝ),
      (∀ n, IsCompact (K n)) ∧
      volume N = 0 ∧
      E = (⋃ n, K n) ∪ N := by
  sorry

/-- Continuous image of a compact set is compact (hence measurable). -/
lemma isCompact_image_of_continuousOn
    {f : ℝ → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hK_sub : K ⊆ Icc 0 1)
    (hf : ContinuousOn f (Icc 0 1)) :
    IsCompact (f '' K) := by
  sorry

/-- Using f' ∈ L¹: m*(f(E)) ≤ ∫_E |f'| for intervals. -/
lemma outer_measure_image_le_integral_deriv
    {f : ℝ → ℝ}
    (hac : AbsolutelyContinuousOn f)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ Icc 0 1) :
    volume (f '' Icc a b) ≤
      ENNReal.ofReal (∫ x in a..b, ‖deriv f x‖) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.OuterMeasure` / `volume.toOuterMeasure` — Lebesgue outer measure
- `MeasurableSet` — measurable sets
- `IsCompact` — compact sets
- `ContinuousOn f (Icc 0 1)` — continuity (AC ⟹ continuous)
- `Set.image` / `f '' E` — image of a set

**Key lemmas:**
- `IsCompact.image` — continuous image of compact is compact. In `Mathlib.Topology.CompactOpen`
- `IsCompact.measurableSet` — compact sets are measurable
- `MeasurableSet.iUnion` — countable union of measurable sets is measurable
- `MeasurableSet.union` — union of measurable sets
- `measure_iUnion_le` — σ-subadditivity of measure
- `MeasureTheory.Measure.InnerRegularWRT` — inner regularity of Lebesgue measure (compact sets approximate from inside)
- `MeasureTheory.Measure.OuterRegular` — outer regularity (open sets approximate from outside)
- `MeasureTheory.ae_eq_zero_of_forall_setIntegral_eq_zero` — not directly, but related to null set arguments
- `intervalIntegral.norm_integral_le_of_norm_le` — ∫|f'| controls variation
- `measure_mono` — monotonicity of outer measure

**Tactic hints:**
- `intro ε hε` — starting the ε-δ arguments
- `obtain ⟨δ, hδ, hδ_ac⟩ := absolute_continuity_of_integral ...` — getting δ from AC of ∫|f'|
- `obtain ⟨U, hU_open, hE_sub_U, hU_meas⟩ := MeasureTheory.Measure.OuterRegular ...` — outer regularity
- `refine ⟨⋃ n, f '' K n, f '' N, ?_, ?_, ?_⟩` — decomposing the image
- `exact (hK.image (hf.mono hK_sub)).measurableSet` — compact image is measurable
- `exact ac_maps_null_to_null hac hf hN_sub hN_null` — null image from (b)
- `gcongr` — monotonicity steps
- `positivity` — for ε > 0, δ > 0
- `measurability` — for measurability goals