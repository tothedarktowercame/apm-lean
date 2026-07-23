

## apm-a96J04 — AC monotone increasing maps null sets to null sets

**Problem.** Let $f:[a,b]\to\mathbb{R}$ be absolutely continuous and monotone increasing. Show that if $E\subseteq[a,b]$ has Lebesgue measure zero, then $f(E)$ has Lebesgue measure zero.

### Informal proof sketch

Since $f$ is absolutely continuous, for every $\varepsilon>0$ there exists $\delta>0$ such that for any finite collection of disjoint intervals $\{(a_k,b_k)\}$ with $\sum(b_k-a_k)<\delta$, we have $\sum|f(b_k)-f(a_k)|<\varepsilon$. Since $f$ is monotone increasing, $|f(b_k)-f(a_k)|=f(b_k)-f(a_k)$, so each interval $(a_k,b_k)$ maps into an interval of length $f(b_k)-f(a_k)$.

Given $m(E)=0$, cover $E$ by countably many disjoint open intervals $\{(a_k,b_k)\}$ with $\sum(b_k-a_k)<\delta$. By monotonicity, $f((a_k,b_k))\subseteq[f(a_k),f(b_k)]$, so $f(E)\subseteq\bigcup_k[f(a_k),f(b_k)]$. Then $m^*(f(E))\leq\sum(f(b_k)-f(a_k))<\varepsilon$. Since $\varepsilon$ is arbitrary, $m(f(E))=0$. $\square$

### Lean 4 statement

```lean
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Order.Monotone.Basic

open MeasureTheory Set

/-- An absolutely continuous monotone increasing function on [a,b]
    maps Lebesgue-null sets to Lebesgue-null sets. -/
theorem ac_monotone_maps_null_to_null
    {a b : ℝ} (hab : a ≤ b)
    (f : ℝ → ℝ)
    (hf_mono : MonotoneOn f (Icc a b))
    (hf_ac : ∀ ε > 0, ∃ δ > 0, ∀ (I : Finset (ℝ × ℝ)),
      (∀ p ∈ I, p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b ∧ p.1 ≤ p.2) →
      (∀ p q, p ∈ I → q ∈ I → p ≠ q → Icc p.1 p.2 ∩ Icc q.1 q.2 = ∅ ∨
        Icc p.1 p.2 ∩ Icc q.1 q.2 = {p.2} ∨ Icc p.1 p.2 ∩ Icc q.1 q.2 = {q.2}) →
      ∑ p ∈ I, (p.2 - p.1) < δ →
      ∑ p ∈ I, |f p.2 - f p.1| < ε)
    (E : Set ℝ) (hE : E ⊆ Icc a b)
    (hE_null : volume E = 0) :
    volume (f '' E) = 0 := by
  sorry
```

### Mathlib cross-references

| Concept | Mathlib | Note |
|---|---|---|
| Lebesgue measure | `MeasureTheory.volume` | Default volume on `ℝ` |
| Monotone on interval | `MonotoneOn` | `Order.Monotone.Basic` |
| Outer measure zero | `MeasureTheory.OuterMeasure` | Used for null-set covering arguments |
| Image of set | `Set.image` | `f '' E` |
| Absolute continuity (function) | — | No direct Mathlib predicate for AC functions on intervals; encoded manually via the ε-δ condition |
| AC ⇒ maps null to null | — | Not in Mathlib as of current; sometimes called the "Lusin N-property" |

**Note.** The property that AC functions satisfy the Lusin N-condition (map null sets to null sets) is classical. The converse direction—monotone + N-property implies AC—is the Banach–Zaretsky theorem. Monotonicity is used here to ensure the image of each interval is again an interval (no folding), making the covering estimate clean.