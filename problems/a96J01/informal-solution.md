## apm-a96J01

**Problem.** Does there exist a sequence $(f_n)$ of nonnegative continuous functions on $[0,1]$ such that $\sum f_n$ converges uniformly but $\sum \|f_n\|_\infty = \infty$?

**Answer: Yes.**

**Informal proof.** Take disjointly supported bump functions. Partition $[0,1]$ into consecutive intervals $I_n$ of length $\ell_n = 1/(n(n+1))$ (these sum to 1 via telescoping). Define $f_n$ as a continuous "tent" on $I_n$ with peak height $1/n$ and support exactly $I_n$, zero elsewhere.

Then $\|f_n\|_\infty = 1/n$, so $\sum \|f_n\|_\infty = \sum 1/n = \infty$.

For uniform convergence: since supports are pairwise disjoint, for each $x \in [0,1]$, at most one $f_n(x)$ is nonzero. The tail $\sup_x \sum_{n > N} f_n(x) \le \sup_{n > N} \|f_n\|_\infty = 1/(N+1) \to 0$, so convergence is uniform.

**Lean 4 statement:**

```lean
/-- apm-a96J01: uniformly convergent series of nonneg continuous functions
    whose sup-norms diverge. -/
theorem apm_a96J01 :
    ∃ f : ℕ → C(Set.Icc (0:ℝ) 1, ℝ),
      (∀ n, ∀ x, 0 ≤ (f n) x) ∧
      (∃ g : C(Set.Icc (0:ℝ) 1, ℝ),
        Filter.Tendsto (fun N => ∑ n in Finset.range N, f n)
          Filter.atTop (nhds g)) ∧
      ¬ Summable (fun n => ‖f n‖) := by
  sorry
```

**Mathlib cross-refs:** `ContinuousMap` (`C(X, Y)`), `Filter.Tendsto`, `Summable`, `ContinuousMap.norm_def`.

---

That covers the last outstanding problem from the batch. Let me know if you'd like to continue with more APM problems, return to the UKRN working paper, or work on something else.