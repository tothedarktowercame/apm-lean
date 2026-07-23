

# APM a01J02: Lebesgue measurable sets and functions have Borel representatives

## Why It's Hard

Both statements are **true**, but they test whether you understand the precise relationship between the Lebesgue and Borel σ-algebras. The Lebesgue σ-algebra is the *completion* of the Borel σ-algebra with respect to Lebesgue measure — it contains all Borel sets plus all subsets of Borel null sets. This means every Lebesgue measurable set differs from a Borel set by a null set, and every Lebesgue measurable function agrees with a Borel function a.e. But proving these requires understanding how the completion construction works, not just stating it.

## The Key Insight

**(a)** The Lebesgue σ-algebra is the completion of the Borel σ-algebra. This means: for every Lebesgue measurable A, there exist Borel sets B₁ ⊆ A ⊆ B₂ with m(B₂ \ B₁) = 0. Taking B = B₁ (or B₂) gives m(A △ B) = 0.

**(b)** A Lebesgue measurable function is measurable with respect to the completed σ-algebra. Since the completion adds only null sets, the function can be modified on a null set to become Borel measurable. Concretely: approximate f by simple functions, each of whose level sets differs from a Borel set by a null set (by part (a)), and assemble a Borel function g that agrees with f a.e.

## Complete Proof

### Part (a): TRUE

**Statement.** If A ⊂ ℝ is Lebesgue measurable, there exists a Borel set B with m(A △ B) = 0, where A △ B = (A \ B) ∪ (B \ A) is the symmetric difference.

**Proof.** By the regularity of Lebesgue measure, for each n ∈ ℕ there exists an open set Uₙ ⊇ A with m(Uₙ \ A) < 1/n. (Outer regularity: m(A) = inf{m(U) : U open, U ⊇ A}.)

Define B = ⋂ₙ Uₙ. Then:
- B is a Gδ set (countable intersection of open sets), hence Borel.
- A ⊆ Uₙ for all n, so A ⊆ B.
- B \ A ⊆ Uₙ \ A for each n, so m(B \ A) ≤ m(Uₙ \ A) < 1/n for all n. Hence m(B \ A) = 0.
- A ⊆ B, so A \ B = ∅ and m(A \ B) = 0.

Therefore m(A △ B) = m(A \ B) + m(B \ A) = 0 + 0 = 0. ∎

**Remark.** We could also use inner regularity (approximate from inside by compact/closed sets) to find a Borel set C ⊆ A with m(A \ C) = 0. Either direction works.

### Part (b): TRUE

**Statement.** If f : [0,1] → ℝ is Lebesgue measurable, there exists a Borel measurable g : [0,1] → ℝ with m({t : f(t) ≠ g(t)}) = 0.

**Proof.**

**Step 1: Simple function case.** If f = Σᵢ cᵢ 1\_{Aᵢ} is a simple function with Lebesgue measurable sets Aᵢ, then by part (a), for each i there exists a Borel set Bᵢ with m(Aᵢ △ Bᵢ) = 0. Define g = Σᵢ cᵢ 1\_{Bᵢ}. Then g is Borel measurable, and {f ≠ g} ⊆ ⋃ᵢ (Aᵢ △ Bᵢ), which has measure zero.

**Step 2: Nonnegative measurable function.** If f ≥ 0 is Lebesgue measurable, there exist simple measurable functions sₙ ↑ f pointwise (standard approximation theorem). By Step 1, for each n there is a Borel simple function tₙ with m({sₙ ≠ tₙ}) = 0. Let N = ⋃ₙ {sₙ ≠ tₙ}; then m(N) = 0 (countable union of null sets).

Define g(x) = lim sup tₙ(x). Since each tₙ is Borel, g is Borel measurable. For x ∉ N: tₙ(x) = sₙ(x) for all n, so g(x) = lim sₙ(x) = f(x). Thus {f ≠ g} ⊆ N has measure zero.

**Step 3: General case.** Write f = f⁺ - f⁻. Apply Step 2 to f⁺ and f⁻ separately to get Borel functions g⁺, g⁻ agreeing a.e. Then g = g⁺ - g⁻ is Borel and agrees with f a.e. ∎

## What Connects

**To the Lebesgue completion.** Both results are consequences of the fact that the Lebesgue σ-algebra is the completion of the Borel σ-algebra with respect to Lebesgue measure. The completion adds all subsets of null sets, and removing them recovers the Borel structure up to null sets.

**To the theory of measurable selections.** In more abstract settings (Polish spaces, analytic sets), the question "can a measurable function be replaced by a Borel one a.e.?" becomes subtle. In ℝ with Lebesgue measure, it is always possible because the completion is relatively well-behaved.

**To Lusin's theorem.** A stronger result: for any ε > 0, there exists a compact K ⊆ [0,1] with m([0,1] \ K) < ε such that f|\_K is *continuous*. This gives a continuous (hence Borel) function agreeing with f on K. Part (b) is the "ε = 0 limit" of this idea (at the cost of dropping continuity).

**To the Borel hierarchy.** Part (a) shows that every Lebesgue set is a Borel set modulo null sets. But not every Lebesgue set *is* Borel: the Lebesgue σ-algebra is strictly larger than the Borel σ-algebra (it has cardinality 2^c vs c). The symmetric difference being null is the best you can do.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory Set Filter

noncomputable section

/-- Part (a): Every Lebesgue measurable set has a Borel representative
    with null symmetric difference.

    In Mathlib, Lebesgue measure on ℝ is already the completion of its
    restriction to Borel sets. We state: for any measurable A, there
    exists a Borel B with μ(A △ B) = 0. -/
theorem exists_borel_symmDiff_null
    {A : Set ℝ} (hA : MeasurableSet A) :
    ∃ B : Set ℝ, MeasurableSet[borel ℝ] B ∧
      volume (A ∆ B) = 0 := by
  sorry

/-- Outer regularity ingredient: A can be approximated from outside
    by open (hence Borel) sets. -/
lemma exists_isOpen_symmDiff_null
    {A : Set ℝ} (hA : MeasurableSet A) (hfin : volume A ≠ ⊤) :
    ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ U : Set ℝ, IsOpen U ∧ A ⊆ U ∧ volume (U \ A) < ε := by
  sorry

/-- The Gδ envelope: intersecting the approximating open sets gives
    a Borel set B ⊇ A with m(B \ A) = 0. -/
lemma exists_gdelta_superset_null_diff
    {A : Set ℝ} (hA : MeasurableSet A) (hfin : volume A ≠ ⊤) :
    ∃ B : Set ℝ, MeasurableSet[borel ℝ] B ∧ A ⊆ B ∧ volume (B \ A) = 0 := by
  sorry

/-- Part (b): Every Lebesgue measurable function has a Borel
    measurable representative agreeing a.e.

    Stated: for any Lebesgue measurable f, there exists g that is
    Borel measurable and f =ᵐ[volume] g. -/
theorem exists_borel_ae_eq
    {f : ℝ → ℝ}
    (hf : Measurable f) :
    ∃ g : ℝ → ℝ, Measurable[borel ℝ] g ∧ f =ᵐ[volume] g := by
  sorry

/-- Simple function case: a Lebesgue-measurable simple function
    has a Borel simple function agreeing a.e. -/
lemma exists_borel_simpleFunc_ae_eq
    (s : SimpleFunc ℝ ℝ) :
    ∃ t : @SimpleFunc ℝ (borel ℝ) ℝ,
      (s : ℝ → ℝ) =ᵐ[volume] (t : ℝ → ℝ) := by
  sorry

/-- Nonnegative case via monotone approximation: the pointwise limit
    of Borel simple functions is Borel. -/
lemma exists_borel_ae_eq_of_nonneg
    {f : ℝ → ℝ} (hf : Measurable f) (hnn : 0 ≤ f) :
    ∃ g : ℝ → ℝ, Measurable[borel ℝ] g ∧ 0 ≤ g ∧ f =ᵐ[volume] g := by
  sorry

/-- The Lebesgue σ-algebra on ℝ is the completion of the Borel σ-algebra.
    This is the structural fact underlying both parts. -/
lemma lebesgue_eq_borel_completion :
    (volume : Measure ℝ).completion.toMeasurableSpace = ‹MeasurableSpace ℝ› := by
  sorry

end
```

**Mathlib notes:**

- In Mathlib, `MeasurableSet A` for `A : Set ℝ` refers to the *default* measurable space on ℝ, which is the Lebesgue σ-algebra (the completion of `borel ℝ`). `MeasurableSet[borel ℝ] B` explicitly asks for Borel measurability.
- `A ∆ B` is `symmDiff A B` = `(A \ B) ∪ (B \ A)` — Mathlib has `Set.symmDiff`.
- `f =ᵐ[volume] g` is `Filter.EventuallyEq (ae volume) f g`, the standard "equal a.e." predicate.
- `Measurable[borel ℝ] g` means g is measurable with respect to the Borel σ-algebra, which is strictly contained in the Lebesgue σ-algebra.
- `SimpleFunc ℝ ℝ` is a simple function measurable w.r.t. the default (Lebesgue) σ-algebra; `@SimpleFunc ℝ (borel ℝ) ℝ` is one measurable w.r.t. the Borel σ-algebra.
- The structural fact `lebesgue_eq_borel_completion` is that Lebesgue measure on ℝ is the completion of its restriction to Borel sets. In Mathlib, this is essentially `Real.instMeasurableSpace` being defined as the completion of `borel ℝ`.
- Outer regularity `Measure.OuterRegular` for Lebesgue measure is available in Mathlib and provides the approximation by open sets used in part (a).
