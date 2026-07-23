## apm-a93J05 — Doubly periodic entire function is constant

### Informal proof

Let $f : \mathbb{C} \to \mathbb{C}$ be entire with periods $\omega_1, \omega_2$ where $\omega_2/\omega_1 \notin \mathbb{R}$. The fundamental parallelogram $P = \{s\omega_1 + t\omega_2 : s,t \in [0,1]\}$ is compact. Since $f$ is continuous, $|f|$ attains a maximum $M$ on $P$. For any $z \in \mathbb{C}$, write $z = z_0 + m\omega_1 + n\omega_2$ with $z_0 \in P$ and $m,n \in \mathbb{Z}$. Then $f(z) = f(z_0)$, so $|f(z)| \leq M$. Thus $f$ is bounded and entire, hence constant by Liouville's theorem. $\blacksquare$

### Lean 4 statement

```lean
import Mathlib

/-- A doubly periodic entire function is constant.
    If f is differentiable on ℂ and periodic with respect to two
    ℝ-linearly independent periods, then f is constant. -/
theorem doubly_periodic_entire_is_const
    (f : ℂ → ℂ)
    (hf : Differentiable ℂ f)
    (ω₁ ω₂ : ℂ)
    (hω₁ : ω₁ ≠ 0)
    (hind : ¬ ∃ r : ℝ, ω₂ = r • ω₁)
    (hper₁ : ∀ z, f (z + ω₁) = f z)
    (hper₂ : ∀ z, f (z + ω₂) = f z) :
    ∃ c, ∀ z, f z = c := by
  sorry
```

### Mathlib cross-references

| Concept | Mathlib name |
|---|---|
| Differentiable on ℂ | `Differentiable ℂ f` |
| Liouville's theorem | `Complex.isConst_of_differentiable_of_bounded` or `Liouville.apply` |
| Bounded implies constant (entire) | `Complex.Liouville.module` |
| Compact → continuous → bounded | `IsCompact.exists_bound_of_continuousOn` |
| Entire = differentiable everywhere | `Differentiable ℂ f` (no domain restriction) |

The key Mathlib path: show `f` is bounded via compactness of the fundamental domain + periodicity, then apply `Complex.isConst_of_differentiable_of_bounded` to conclude constancy.