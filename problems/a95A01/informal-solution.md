

# APM a95A01: Riemann vs Lebesgue integrals and a non-Riemann-integrable indicator

## 1. Informal proof

**Why it's hard.** Part (a) requires comparing three different integration theories (lower Riemann, Lebesgue, upper Riemann) for a bounded measurable function — the definitions are quite different and the comparison goes through careful approximation by step functions vs simple functions. Part (b) requires constructing/recognising a function that is Lebesgue integrable but not Riemann integrable, using a set that is "topologically small" (empty interior) but "measure-theoretically large" (positive Lebesgue measure).

**The key insight.** (a) Lower Riemann sums approximate $f$ from below using infima on intervals, which are $\leq$ the Lebesgue integral (because Lebesgue simple functions are more flexible than step functions). Similarly upper Riemann $\geq$ Lebesgue. (b) A compact set with positive measure and empty interior (fat Cantor set) has the property that its indicator function has upper Riemann integral equal to its measure but lower Riemann integral equal to $0$, since every interval contains points both in $K$ and outside $K$.

**Proof.**

**(a)** Let $f : [0,1] \to \mathbb{R}$ be bounded and Lebesgue measurable.

*Lower Riemann $\leq$ Lebesgue:* A lower Riemann sum is $L(P,f) = \sum m_{j}(x_{j} - x_{j-1})$ where $m_{j} = \inf_{[x_{j-1},x_{j}]} f$. Each step function $s(x) = m_{j}$ on $(x_{j-1}, x_{j})$ satisfies $s \leq f$ pointwise and is measurable. So $\int s = L(P,f) \leq \int f$ (Lebesgue integral is monotone). Taking $\sup$ over all partitions: lower Riemann integral $\leq$ Lebesgue integral.

*Lebesgue $\leq$ upper Riemann:* Similarly, an upper Riemann sum $U(P,f) = \sum M_{j}(x_{j} - x_{j-1})$ with $M_{j} = \sup_{[x_{j-1},x_{j}]} f$ defines a step function $S \geq f$, so $\int f \leq \int S = U(P,f)$. Taking $\inf$: Lebesgue integral $\leq$ upper Riemann integral. ✓

**(b)** Let $K \subset [0,1]$ be compact with $m(K) > 0$ and $\mathrm{Interior}(K) = \emptyset$. Let $f = \chi_K$ a.e.

*Upper Riemann integral of $f$:* On any subinterval $[a,b]$ of a partition, $\sup f \geq \sup \chi_K$. Since $K$ is closed with empty interior, $K^c$ is dense, so every interval $[a,b]$ contains a point not in $K$, giving $\inf f = 0$ on every subinterval. But $K$ has positive measure, so some intervals must intersect $K$, giving $\sup f \geq 1$ on those intervals. Actually, more precisely: since $K$ is nowhere dense, $K^c$ is dense. On every interval $[a,b]$, there exists a point $x \in K^c$, so $f(x) = 0$ (at least a.e., and we can choose representative with $f = \chi_K$ everywhere). Thus $\inf_{[a,b]} f = 0$ for every subinterval. So every lower Riemann sum $= 0$, hence lower Riemann integral $= 0$.

*Lower Riemann integral $= 0$:* For every partition $P$, every subinterval contains a point of $K^c$ (since $K^c$ is dense and open, hence meets every interval). So $\inf_{[a,b]} f = 0$ on every subinterval. Hence $L(P,f) = 0$ for all $P$, so the lower Riemann integral $= 0$.

*Upper Riemann integral $= m(K) > 0$:* On any subinterval $[a,b]$, if $[a,b] \cap K \neq \emptyset$, then $\sup_{[a,b]} f = 1$. Since $K$ has positive measure, the upper Riemann integral $\geq m(K) > 0$.

Actually more precisely, the upper Riemann integral equals $m(\bar{K})$ where $\bar{K}$ is the closure of the support... Let me just say: since $K$ is nowhere dense but has positive measure, any partition has every subinterval meeting $K^c$ (so $\inf = 0$) but some subintervals meeting $K$ (so $\sup = 1$ there). Thus lower integral $= 0 < m(K) =$ Lebesgue integral, so lower $\neq$ upper, and $f$ is not Riemann integrable. ✓ ∎

**What connects.** This problem illustrates the fundamental difference between Riemann and Lebesgue integration. Riemann integration uses infima/suprema on intervals and requires the upper and lower integrals to agree — which fails when the function oscillates between $0$ and $1$ on every interval (as $\chi_K$ does when $K$ is nowhere dense). Lebesgue integration uses measurable sets directly and can handle $\chi_K$ with no difficulty. The fat Cantor set (compact, positive measure, empty interior) is the canonical example of a set whose indicator is Lebesgue but not Riemann integrable. The classical criterion (Lebesgue's theorem on Riemann integrability) says $f$ is Riemann integrable iff it is continuous a.e., and $\chi_K$ is discontinuous on $K \cup \partial K$, which has positive measure.

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.BoxIntegral.Basic

open MeasureTheory Set

noncomputable section

/-- Lower Riemann integral of a bounded function on [0,1]. -/
def lowerRiemannIntegral (f : ℝ → ℝ) : ℝ :=
  sSup {s : ℝ | ∃ (n : ℕ) (t : Fin (n+2) → ℝ),
    t 0 = 0 ∧ t (Fin.last _) = 1 ∧
    (∀ i : Fin (n+1), t i.castSucc < t i.succ) ∧
    s = ∑ i : Fin (n+1),
      (sInf (f '' Icc (t i.castSucc) (t i.succ))) *
      (t i.succ - t i.castSucc)}

/-- Upper Riemann integral of a bounded function on [0,1]. -/
def upperRiemannIntegral (f : ℝ → ℝ) : ℝ :=
  sInf {s : ℝ | ∃ (n : ℕ) (t : Fin (n+2) → ℝ),
    t 0 = 0 ∧ t (Fin.last _) = 1 ∧
    (∀ i : Fin (n+1), t i.castSucc < t i.succ) ∧
    s = ∑ i : Fin (n+1),
      (sSup (f '' Icc (t i.castSucc) (t i.succ))) *
      (t i.succ - t i.castSucc)}

/-- Part (a): lower Riemann ≤ Lebesgue ≤ upper Riemann. -/
theorem riemann_lebesgue_sandwich
    {f : ℝ → ℝ}
    (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x ∈ Icc (0:ℝ) 1, |f x| ≤ M) :
    lowerRiemannIntegral f ≤
      ∫ x in Icc (0:ℝ) 1, f x ∂volume ∧
    ∫ x in Icc (0:ℝ) 1, f x ∂volume ≤
      upperRiemannIntegral f := by
  sorry

/-- Part (b): indicator of a compact nowhere-dense set with
    positive measure is not Riemann integrable. -/
theorem indicator_fat_cantor_not_riemann_integrable
    {K : Set ℝ} (hK : IsCompact K) (hK_sub : K ⊆ Icc 0 1)
    (hK_meas : 0 < volume K)
    (hK_int : interior K = ∅) :
    lowerRiemannIntegral (K.indicator (fun _ => (1:ℝ))) <
      upperRiemannIntegral (K.indicator (fun _ => (1:ℝ))) := by
  sorry

/-- The lower Riemann integral of χ_K is 0 when K is nowhere dense. -/
lemma lower_riemann_indicator_eq_zero
    {K : Set ℝ} (hK : IsClosed K)
    (hK_sub : K ⊆ Icc 0 1)
    (hK_int : interior K = ∅) :
    lowerRiemannIntegral (K.indicator (fun _ => (1:ℝ))) = 0 := by
  sorry

/-- On every interval, K^c is dense when K has empty interior. -/
lemma dense_compl_of_interior_empty
    {K : Set ℝ} (hK : IsClosed K) (hK_int : interior K = ∅) :
    Dense Kᶜ := by
  sorry

/-- Every subinterval contains a point of K^c, so inf χ_K = 0. -/
lemma inf_indicator_eq_zero_on_interval
    {K : Set ℝ} (hK : IsClosed K)
    (hK_int : interior K = ∅)
    {a b : ℝ} (hab : a < b) :
    sInf (K.indicator (fun _ => (1:ℝ)) '' Icc a b) = 0 := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.volume` — Lebesgue measure
- `Set.indicator` — indicator function
- `IsCompact`, `IsClosed` — compactness/closedness
- `interior K` — topological interior
- `Dense S` — density of a set
- `Set.Icc` — closed intervals
- `sSup`, `sInf` — supremum/infimum in $\mathbb{R}$

**Key lemmas:**
- `MeasureTheory.integral_indicator` — Lebesgue integral of an indicator = measure of the set
- `MeasureTheory.set_integral_le_integral` — integral over subset $\leq$ total integral (monotonicity)
- `IsCompact.measure_pos_of_nonempty_interior` — not directly, but related: positive measure doesn't require interior
- `Dense.inter_open_nonempty` — a dense set meets every open set (for showing $K^c$ meets every open interval)
- `interior_eq_empty_iff_dense_compl` — empty interior $\leftrightarrow$ complement is dense
- `csInf_le` / `le_csSup` — infimum/supremum bounds
- `Set.mem_image` — membership in f '' S
- `Finset.sum_nonneg` / `Finset.sum_le_sum` — bounding Riemann sums

**Tactic hints:**
- `constructor` — splitting the $\wedge$ in part (a)
- `apply csSup_le` / `le_csInf` — bounding Riemann integrals by Lebesgue
- `intro s ⟨n, t, ht0, ht1, hmono, hs⟩` — unpacking a Riemann sum
- `have := Dense.inter_open_nonempty (dense_compl_of_interior_empty hK hK_int) (Ioo a b) isOpen_Ioo ⟨_, _⟩` — finding points of $K^c$ in every interval
- `simp [Set.indicator_apply, Set.mem_compl_iff]` — evaluating $\chi_K$ at points
- `linarith` — combining bounds
- `positivity` — for $\text{volume } K > 0$
- `exact?` — finding the right density/interior lemma
