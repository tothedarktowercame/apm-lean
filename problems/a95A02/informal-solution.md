# APM a95A02: AC functions satisfy Lusin's condition (N) and preserve measurability

## 1. Informal proof

**Why it's hard.** Part (b) extends the AC condition from finite unions of intervals to *arbitrary* sets $E$ — you need to approximate $E$ by intervals using outer measure regularity. Part (c) goes further: images of measurable sets under AC functions are measurable, which requires (b) plus inner regularity and the fact that continuous images of compact sets are compact (hence measurable).

**The key insight.** (b) is Lusin's condition (N): AC functions map null sets to null sets, and more generally $m^{*}(f(E))$ is controlled by $m^{*}(E)$. The AC definition directly handles finite unions of intervals; outer regularity extends this to arbitrary $E$. (c) Write $E = K \cup N$ where $K$ is $\sigma$-compact and $N$ is null; $f(K)$ is $\sigma$-compact (hence measurable) and $f(N)$ is null (by (b)), so $f(E) = f(K) \cup f(N)$ is measurable.

**Proof.**

**(a) Definition.** $f : [0,1] \to \mathbb{R}$ is absolutely continuous if for every $\varepsilon > 0$ there exists $\delta > 0$ such that for every finite collection of non-overlapping intervals $(a_{1},b_{1}), \ldots, (a_{n},b_{n})$ in $[0,1]$ with $\sum(b_{k}-a_{k}) < \delta$, we have $\sum|f(b_{k})-f(a_{k})| < \varepsilon$.

**(b) $m^{*}(f(E)) \leq \varepsilon$ when $m^{*}(E) \leq \delta$.**

*Case 1: $E$ is a finite union of non-overlapping intervals.* If $E = \cup(a_{k},b_{k})$ with $\sum(b_{k}-a_{k}) < \delta$, then $f$ maps each $[a_{k},b_{k}]$ to an interval of length $\leq$ sup-inf $\leq$ max-min over $[a_{k},b_{k}]$. By the intermediate value theorem ($f$ is continuous since AC ⟹ continuous), $f([a_{k},b_{k}])$ is an interval, and its length $= \sup_{[a_{k},b_{k}]} f - \inf_{[a_{k},b_{k}]} f$. This length might exceed $|f(b_{k})-f(a_{k})|$ ($f$ could oscillate within the interval). However, the total variation of $f$ on $\cup[a_{k},b_{k}]$ is bounded: the AC condition gives $\sum|f(b_{k})-f(a_{k})| < \varepsilon$, but we need to bound the total oscillation.

Better approach for case 1: use the fact that $f$ is AC, hence $f(x) = f(0) + \int_{0}^{x} f'(t)dt$ with $f' \in L^{1}$. For a subinterval $[a,b]$: $m^{*}(f([a,b])) \leq \int_{a}^{b} |f'|$ (the image is contained in an interval of length $\leq$ the total variation on $[a,b]$). For a finite union: $m^{*}(f(\cup[a_{k},b_{k}])) \leq \sum m^{*}(f([a_{k},b_{k}])) \leq \sum \int_{a_{k}}^{b_{k}} |f'| = \int_E |f'|$. By absolute continuity of the integral ($f' \in L^{1}$): given $\varepsilon > 0$, there exists $\delta > 0$ with $\int_E |f'| < \varepsilon$ whenever $m(E) < \delta$.

*Case 2: General $E$.* Given $\varepsilon$, choose $\delta$ from the absolute continuity of the integral for $f'$. If $m^{*}(E) < \delta$, by definition of outer measure, there exists an open set $U \supseteq E$ with $m(U) < \delta$. Write $U = \cup(a_{k},b_{k})$ (countable union of disjoint open intervals). Then $f(E) \subseteq f(U) = \cup f((a_{k},b_{k}))$, and $m^{*}(f(U)) \leq \sum m^{*}(f([a_{k},b_{k}])) \leq \sum \int_{a_{k}}^{b_{k}} |f'| = \int_U |f'| < \varepsilon$. ✓

**(c) $f(E)$ is measurable when $E$ is measurable.**

Since $E \subseteq [0,1]$ is measurable, by regularity: $E = K \cup N$ where $K$ is a countable union of compact sets ($K_{m} \uparrow K$) and $m(N) = 0$.

- $f(K_{m})$ is compact (continuous image of compact) hence measurable. So $f(K) = \cup f(K_{m})$ is an $F_{\sigma}$ set, hence measurable.
- $m^{*}(N) = 0$, so by part (b), $m^{*}(f(N)) = 0$. A set of outer measure zero is Lebesgue measurable.

$f(E) = f(K \cup N) = f(K) \cup f(N)$. Union of two measurable sets is measurable. ✓ ∎

**What connects.** Part (b) is Lusin's condition (N): the property that null sets map to null sets. This is the defining feature that distinguishes absolutely continuous functions from merely continuous or BV functions — the Cantor function is continuous and BV but violates condition (N) (it maps the Cantor set, measure 0, onto $[0,1]$, measure 1). Part (c) shows AC functions preserve measurability — a much stronger statement than just preserving null sets, using the decomposition of measurable sets into $\sigma$-compact + null. The result fails for general continuous functions (there exist continuous functions mapping measurable sets to non-measurable sets, via the composition of a continuous surjection onto a Cantor-type set with a non-measurable subset).

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
- `measure_iUnion_le` — $\sigma$-subadditivity of measure
- `MeasureTheory.Measure.InnerRegularWRT` — inner regularity of Lebesgue measure (compact sets approximate from inside)
- `MeasureTheory.Measure.OuterRegular` — outer regularity (open sets approximate from outside)
- `MeasureTheory.ae_eq_zero_of_forall_setIntegral_eq_zero` — not directly, but related to null set arguments
- `intervalIntegral.norm_integral_le_of_norm_le` — $\int|f'|$ controls variation
- `measure_mono` — monotonicity of outer measure

**Tactic hints:**
- `intro ε hε` — starting the $\varepsilon$-$\delta$ arguments
- `obtain ⟨δ, hδ, hδ_ac⟩ := absolute_continuity_of_integral ...` — getting $\delta$ from AC of $\int|f'|$
- `obtain ⟨U, hU_open, hE_sub_U, hU_meas⟩ := MeasureTheory.Measure.OuterRegular ...` — outer regularity
- `refine ⟨⋃ n, f '' K n, f '' N, ?_, ?_, ?_⟩` — decomposing the image
- `exact (hK.image (hf.mono hK_sub)).measurableSet` — compact image is measurable
- `exact ac_maps_null_to_null hac hf hN_sub hN_null` — null image from (b)
- `gcongr` — monotonicity steps
- `positivity` — for $\varepsilon > 0$, $\delta > 0$
- `measurability` — for measurability goals
