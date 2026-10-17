# APM a01J02: Lebesgue measurable sets and functions have Borel representatives

## Why It's Hard

Both statements are **true**, but they test whether you understand the precise relationship between the Lebesgue and Borel $\sigma$-algebras. The Lebesgue $\sigma$-algebra is the *completion* of the Borel $\sigma$-algebra with respect to Lebesgue measure — it contains all Borel sets plus all subsets of Borel null sets. This means every Lebesgue measurable set differs from a Borel set by a null set, and every Lebesgue measurable function agrees with a Borel function a.e. But proving these requires understanding how the completion construction works, not just stating it.

## The Key Insight

**(a)** The Lebesgue $\sigma$-algebra is the completion of the Borel $\sigma$-algebra. This means: for every Lebesgue measurable $A$, there exist Borel sets $B_{1} \subseteq A \subseteq B_{2}$ with $m(B_{2} \setminus B_{1}) = 0$. Taking $B = B_{1}$ (or $B_{2}$) gives $m(A \triangle B) = 0$.

**(b)** A Lebesgue measurable function is measurable with respect to the completed $\sigma$-algebra. Since the completion adds only null sets, the function can be modified on a null set to become Borel measurable. Concretely: approximate $f$ by simple functions, each of whose level sets differs from a Borel set by a null set (by part (a)), and assemble a Borel function $g$ that agrees with $f$ a.e.

## Complete Proof

### Part (a): TRUE

**Statement.** If $A \subset \mathbb{R}$ is Lebesgue measurable, there exists a Borel set $B$ with $m(A \triangle B) = 0$, where $A \triangle B = (A \setminus B) \cup (B \setminus A)$ is the symmetric difference.

**Proof.** By the regularity of Lebesgue measure, for each $n \in \mathbb{N}$ there exists an open set $U_{n} \supseteq A$ with $m(U_{n} \setminus A) < 1/n$. (Outer regularity: $m(A) = \inf\{m(U) : U \text{ open}, U \supseteq A\}$.)

Define $B = \bigcap_{n} U_{n}$. Then:
- $B$ is a $G_\delta$ set (countable intersection of open sets), hence Borel.
- $A \subseteq U_{n}$ for all $n$, so $A \subseteq B$.
- $B \setminus A \subseteq U_{n} \setminus A$ for each $n$, so $m(B \setminus A) \leq m(U_{n} \setminus A) < 1/n$ for all $n$. Hence $m(B \setminus A) = 0$.
- $A \subseteq B$, so $A \setminus B = \emptyset$ and $m(A \setminus B) = 0$.

Therefore $m(A \triangle B) = m(A \setminus B) + m(B \setminus A) = 0 + 0 = 0$. ∎

**Remark.** We could also use inner regularity (approximate from inside by compact/closed sets) to find a Borel set $C \subseteq A$ with $m(A \setminus C) = 0$. Either direction works.

### Part (b): TRUE

**Statement.** If $f : [0,1] \to \mathbb{R}$ is Lebesgue measurable, there exists a Borel measurable $g : [0,1] \to \mathbb{R}$ with $m(\{t : f(t) \neq g(t)\}) = 0$.

**Proof.**

**Step 1: Simple function case.** If $f = \sum_{i} c_{i} 1_{A_{i}}$ is a simple function with Lebesgue measurable sets $A_{i}$, then by part (a), for each $i$ there exists a Borel set $B_{i}$ with $m(A_{i} \triangle B_{i}) = 0$. Define $g = \sum_{i} c_{i} 1_{B_{i}}$. Then $g$ is Borel measurable, and $\{f \neq g\} \subseteq \bigcup_{i} (A_{i} \triangle B_{i})$, which has measure zero.

**Step 2: Nonnegative measurable function.** If $f \geq 0$ is Lebesgue measurable, there exist simple measurable functions $s_{n} \uparrow f$ pointwise (standard approximation theorem). By Step 1, for each $n$ there is a Borel simple function $t_{n}$ with $m(\{s_{n} \neq t_{n}\}) = 0$. Let $N = \bigcup_{n} \{s_{n} \neq t_{n}\}$; then $m(N) = 0$ (countable union of null sets).

Define $g(x) = \limsup t_{n}(x)$. Since each $t_{n}$ is Borel, $g$ is Borel measurable. For $x \notin N$: $t_{n}(x) = s_{n}(x)$ for all $n$, so $g(x) = \lim s_{n}(x) = f(x)$. Thus $\{f \neq g\} \subseteq N$ has measure zero.

**Step 3: General case.** Write $f = f^{+} - f^{-}$. Apply Step 2 to $f^{+}$ and $f^{-}$ separately to get Borel functions $g^{+}$, $g^{-}$ agreeing a.e. Then $g = g^{+} - g^{-}$ is Borel and agrees with $f$ a.e. ∎

## What Connects

**To the Lebesgue completion.** Both results are consequences of the fact that the Lebesgue $\sigma$-algebra is the completion of the Borel $\sigma$-algebra with respect to Lebesgue measure. The completion adds all subsets of null sets, and removing them recovers the Borel structure up to null sets.

**To the theory of measurable selections.** In more abstract settings (Polish spaces, analytic sets), the question "can a measurable function be replaced by a Borel one a.e.?" becomes subtle. In $\mathbb{R}$ with Lebesgue measure, it is always possible because the completion is relatively well-behaved.

**To Lusin's theorem.** A stronger result: for any $\varepsilon > 0$, there exists a compact $K \subseteq [0,1]$ with $m([0,1] \setminus K) < \varepsilon$ such that $f|_K$ is *continuous*. This gives a continuous (hence Borel) function agreeing with $f$ on $K$. Part (b) is the "$\varepsilon = 0$ limit" of this idea (at the cost of dropping continuity).

**To the Borel hierarchy.** Part (a) shows that every Lebesgue set is a Borel set modulo null sets. But not every Lebesgue set *is* Borel: the Lebesgue $\sigma$-algebra is strictly larger than the Borel $\sigma$-algebra (it has cardinality $2^c$ vs $c$). The symmetric difference being null is the best you can do.

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

- In Mathlib, `MeasurableSet A` for `A : Set ℝ` refers to the *default* measurable space on $\mathbb{R}$, which is the Lebesgue $\sigma$-algebra (the completion of `borel ℝ`). `MeasurableSet[borel ℝ] B` explicitly asks for Borel measurability.
- `A ∆ B` is `symmDiff A B` = `(A \ B) ∪ (B \ A)` — Mathlib has `Set.symmDiff`.
- `f =ᵐ[volume] g` is `Filter.EventuallyEq (ae volume) f g`, the standard "equal a.e." predicate.
- `Measurable[borel ℝ] g` means $g$ is measurable with respect to the Borel $\sigma$-algebra, which is strictly contained in the Lebesgue $\sigma$-algebra.
- `SimpleFunc ℝ ℝ` is a simple function measurable w.r.t. the default (Lebesgue) $\sigma$-algebra; `@SimpleFunc ℝ (borel ℝ) ℝ` is one measurable w.r.t. the Borel $\sigma$-algebra.
- The structural fact `lebesgue_eq_borel_completion` is that Lebesgue measure on $\mathbb{R}$ is the completion of its restriction to Borel sets. In Mathlib, this is essentially `Real.instMeasurableSpace` being defined as the completion of `borel ℝ`.
- Outer regularity `Measure.OuterRegular` for Lebesgue measure is available in Mathlib and provides the approximation by open sets used in part (a).
