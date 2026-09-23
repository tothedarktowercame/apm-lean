## apm-a96J02 — Steinhaus: a sumset of positive-measure sets contains an interval

**Problem.** Let $A,B\subseteq\mathbb R$ be Lebesgue measurable with $m(A)>0$ and $m(B)>0$. Show that $A+B=\{a+b : a\in A,\ b\in B\}$ contains a nonempty open interval.

**Informal proof.** First reduce to finite measure. Since $m(A)>0$, some bounded piece $A'=A\cap[-N,N]$ already has $m(A')>0$, and $m(A')<\infty$; choose $B'\subseteq B$ the same way. It suffices to find an interval inside $A'+B'$, because $A'+B'\subseteq A+B$.

Consider the convolution of the two indicators,
$$f(t)=(\chi_{A'}*\chi_{B'})(t)=\int_{\mathbb R}\chi_{A'}(x)\,\chi_{B'}(t-x)\,dx=m\bigl(A'\cap(t-B')\bigr),$$
where $t-B'=\{t-b : b\in B'\}$.

*Two facts about $f$ do all the work.*

**$f$ is continuous.** This is continuity of translation in $L^1$: $\|\chi_{B'}(\cdot+h)-\chi_{B'}\|_1\to0$ as $h\to0$ for any set of finite measure, so
$$|f(t+h)-f(t)|\le\int\chi_{A'}(x)\,\bigl|\chi_{B'}(t+h-x)-\chi_{B'}(t-x)\bigr|\,dx\le\|\chi_{B'}(\cdot+h)-\chi_{B'}\|_1\longrightarrow 0.$$
Equivalently, $m\bigl(A'\cap(t-B')\bigr)$ moves continuously because the symmetric difference $(t-B')\,\triangle\,(s-B')$ has small measure when $t$ is near $s$, and intersecting with $A'$ does not increase it.

**$f$ is somewhere positive.** By Tonelli,
$$\int_{\mathbb R}f(t)\,dt=\int\!\!\int\chi_{A'}(x)\chi_{B'}(t-x)\,dx\,dt=m(A')\,m(B')>0,$$
so $f(t_0)>0$ for at least one $t_0$. (Both factors are finite, so the product is a genuine positive real.)

Now combine them. Since $f$ is continuous and $f(t_0)>0$, the set $\{t : f(t)>0\}$ is open and nonempty, so it contains an open interval $I\ni t_0$. And $f(t)>0$ forces $A'\cap(t-B')\neq\emptyset$: pick $x$ in that intersection, so $x\in A'$ and $t-x\in B'$, whence
$$t=x+(t-x)\in A'+B'\subseteq A+B.$$
Therefore $I\subseteq A+B$, a nonempty open interval. $\blacksquare$

**Remark (the density-point route).** The same conclusion follows from the Lebesgue density theorem: pick density points $a$ of $A$ and $b$ of $B$, and an interval $J$ around $a$ on which $A$ occupies more than $\tfrac34$ of the length, similarly for $B$. For $t$ close enough to $a+b$, the sets $A\cap J$ and $t-(B\cap J')$ are both more than three-quarters of a common interval and so must meet. The convolution argument is the same fact stated analytically, and is the one that formalises cleanly.

**Lean 4 statement:**

```lean
/-- apm-a96J02 (Steinhaus): A + B contains a nonempty open interval. -/
theorem apm_a96J02 (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : 0 < volume A) (hB0 : 0 < volume B) :
    ∃ a b : ℝ, a < b ∧ Set.Ioo a b ⊆ A + B := by
  sorry
```

**Mathlib cross-refs:** `MeasureTheory.convolution`, `integral_convolution`,
`tendsto_measure_symmDiff_preimage_nhds_zero`, `MeasureTheory.integral_indicator_one`,
`Set.add` on sets.
