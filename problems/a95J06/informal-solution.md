

# APM a95J06: Homeomorphism fixing the Cantor set, AC on complementary intervals, is AC on [0,1]

## 1. Informal proof

**Why it's hard.** f is AC on each complementary interval of C but the Cantor set has infinitely many complementary intervals, and the AC constants could degenerate. Piecing together infinitely many AC conditions into a single global AC condition requires controlling the total variation contribution from the Cantor set itself.

**The key insight.** Since f(x) = x on C (a set of measure zero), f contributes zero total oscillation on C: for any collection of intervals with endpoints in C, the function values agree with the identity. The oscillation of f on each complementary interval is controlled by AC on that interval. Since the Cantor set has measure zero, intervals covering parts of C contribute zero to Σ|f(bᵢ)-f(aᵢ)| when the total length is small.

**Proof.**

Fix ε > 0. We need δ > 0 such that for any collection of non-overlapping intervals {(aₖ, bₖ)} ⊂ [0,1] with Σ(bₖ-aₖ) < δ, we have Σ|f(bₖ)-f(aₖ)| < ε.

*Step 1: The Cantor set has measure zero.* m(C) = 0, so f = id on a null set.

*Step 2: Structure of [0,1] \ C.* [0,1] \ C = ∪ⱼ Iⱼ where the Iⱼ are the countably many open complementary intervals. f is AC on each Iⱼ (and on its closure, since f is AC on every closed subinterval of [0,1] \ C).

*Step 3: f is of bounded variation.* Since f is a homeomorphism [0,1] → [0,1], f is monotone (continuous injective on an interval ⟹ strictly monotone). So V(f, [0,1]) = |f(1) - f(0)| ≤ 1. (BV is automatic for monotone functions.)

*Step 4: Combine BV + continuity + AC on complementary intervals.* Take any collection of non-overlapping intervals {(aₖ, bₖ)} with Σ(bₖ-aₖ) < δ. Each (aₖ, bₖ) can be decomposed:

(aₖ, bₖ) = [(aₖ, bₖ) ∩ C] ∪ [(aₖ, bₖ) ∩ (∪ⱼ Iⱼ)].

Since f(x) = x on C and f is monotone:

|f(bₖ) - f(aₖ)| ≤ |f(bₖ) - bₖ| + |bₖ - aₖ| + |aₖ - f(aₖ)|.

Wait — that's not quite right. Since f = id on C, if aₖ, bₖ ∈ C then |f(bₖ) - f(aₖ)| = |bₖ - aₖ|. But the endpoints need not be in C.

Better approach using monotonicity directly: since f is an increasing homeomorphism [0,1] → [0,1] (assuming orientation-preserving; if not, consider 1-f):

Σ|f(bₖ) - f(aₖ)| = Σ(f(bₖ) - f(aₖ)) = total measure of f(∪(aₖ,bₖ)).

Now f(∪(aₖ,bₖ)) = ∪f((aₖ,bₖ)) (disjoint since f is injective). Each f((aₖ,bₖ)) is an interval. Need: total length of f(∪(aₖ,bₖ)) is small when total length of ∪(aₖ,bₖ) is small.

Since f is a homeomorphism fixing C and AC on each complementary interval, f satisfies Lusin's condition (N) on [0,1] \ C (AC ⟹ condition N on each piece). Also f = id on C (so f trivially satisfies condition N on C). Thus f satisfies condition N globally.

Combined with BV (monotone): f is AC on [0,1]. This uses the theorem: **a continuous function of bounded variation satisfying Lusin's condition (N) is absolutely continuous.**

More explicitly: f is monotone (hence BV and continuous), and f maps null sets to null sets (condition N: on C, f = id maps null to null; on each Iⱼ, f is AC hence satisfies condition N). BV + continuous + condition N ⟹ AC. ✓ ∎

**What connects.** This uses the characterisation theorem: a continuous function on [0,1] is absolutely continuous if and only if it is of bounded variation and satisfies Lusin's condition (N) (null sets map to null sets). The hypotheses decompose perfectly: monotone homeomorphism gives BV + continuity; f = id on C gives condition N on C (trivially); AC on each complementary interval gives condition N on [0,1] \ C. Together they yield global condition N, hence global AC. The problem is a cousin of a93J01/a97J04: there, f was assumed AC on [a,1] for all a > 0 and BV + continuous on [0,1]; here, f is AC on each complementary interval and fixes the Cantor set. Both reduce to the BV + condition N characterisation.

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.Basic

open Set MeasureTheory

noncomputable section

/-- The standard Cantor set in [0,1]. -/
def cantorSet : Set ℝ := sorry -- the standard middle-thirds Cantor set

/-- Absolute continuity on a closed interval. -/
def AbsolutelyContinuousOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (n : ℕ) (a b : Fin n → ℝ),
    (∀ i, a i ∈ s) → (∀ i, b i ∈ s) →
    (∀ i, a i ≤ b i) →
    (∀ i j, i < j → b i ≤ a j) →
    ∑ i, (b i - a i) < δ →
    ∑ i, |f (b i) - f (a i)| < ε

/-- Lusin's condition (N): f maps null sets to null sets. -/
def LusinConditionN (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ E ⊆ s, volume E = 0 → volume (f '' E) = 0

/-- Main theorem. -/
theorem ac_on_01_of_homeo_fixing_cantor
    {f : ℝ → ℝ}
    (hf_homeo : Set.BijOn f (Icc 0 1) (Icc 0 1))
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_cont_inv : ContinuousOn (Set.invFunOn f (Icc 0 1)) (Icc 0 1))
    (hf_fix : ∀ x ∈ cantorSet, f x = x)
    (hf_ac_compl : ∀ (a b : ℝ),
      Icc a b ⊆ Icc 0 1 → Icc a b ⊆ cantorSetᶜ →
      AbsolutelyContinuousOn f (Icc a b)) :
    AbsolutelyContinuousOn f (Icc 0 1) := by
  sorry

/-- BV + continuous + condition N ⟹ AC
    (the characterisation theorem). -/
lemma ac_of_bv_continuous_conditionN
    {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_mono : MonotoneOn f (Icc 0 1))
    (hf_N : LusinConditionN f (Icc 0 1)) :
    AbsolutelyContinuousOn f (Icc 0 1) := by
  sorry

/-- A homeomorphism [0,1] → [0,1] is monotone. -/
lemma monotone_of_homeomorphism
    {f : ℝ → ℝ}
    (hf_homeo : Set.BijOn f (Icc 0 1) (Icc 0 1))
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_cont_inv : ContinuousOn (Set.invFunOn f (Icc 0 1)) (Icc 0 1)) :
    MonotoneOn f (Icc 0 1) ∨ AntitoneOn f (Icc 0 1) := by
  sorry

/-- f = id on C implies condition N on C (trivially). -/
lemma conditionN_on_cantor_of_fix
    {f : ℝ → ℝ} (hf_fix : ∀ x ∈ cantorSet, f x = x) :
    LusinConditionN f cantorSet := by
  sorry

/-- AC on complementary intervals implies condition N on [0,1] \ C. -/
lemma conditionN_on_complement_of_ac
    {f : ℝ → ℝ}
    (hf_ac : ∀ (a b : ℝ),
      Icc a b ⊆ Icc 0 1 → Icc a b ⊆ cantorSetᶜ →
      AbsolutelyContinuousOn f (Icc a b)) :
    LusinConditionN f (Icc 0 1 \ cantorSet) := by
  sorry

/-- The Cantor set has measure zero. -/
lemma cantorSet_measure_zero : volume cantorSet = 0 := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MonotoneOn f s` / `AntitoneOn f s` — monotonicity on a set
- `ContinuousOn f s` — continuity on [0,1]
- `Set.BijOn f s t` — bijection between sets (homeomorphism)
- `MeasureTheory.volume` — Lebesgue measure
- `Set.Icc`, `Set.invFunOn` — intervals and inverse function

**Key lemmas:**
- `ContinuousOn.injOn_of_isPreconnected` — continuous injection on connected set (for monotonicity)
- `StrictMonoOn.bijOn` — strict monotone continuous on [a,b] is a bijection onto [f(a),f(b)]
- `MonotoneOn.totalVariationOn_eq` — total variation of monotone function = f(b) - f(a) (for BV)
- `measure_image_le_of_lipschitzOnWith` — or AC ⟹ condition N
- `Set.image_eq_iUnion` — f(∪ Eₖ) = ∪ f(Eₖ) for injective f
- `measure_iUnion_null` — countable union of null sets is null
- `Set.compl_inter` / `Set.diff_union_of_subset` — decomposing [0,1] into C and its complement

**Tactic hints:**
- `apply ac_of_bv_continuous_conditionN hf_cont` — reducing to the characterisation theorem
- `rcases monotone_of_homeomorphism hf_homeo hf_cont hf_cont_inv with h | h` — case split on mono/anti
- `intro E hE hE_null` — for verifying condition N
- `have : E = (E ∩ cantorSet) ∪ (E \ cantorSet) := by simp [union_diff_cancel]` — splitting E
- `exact measure_iUnion_null ...` — combining null image pieces
- `simp [hf_fix x hx]` — f(x) = x on C
- `exact?` — finding the BV + condition N characterisation
- `linarith` — for interval arithmetic