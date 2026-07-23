

# APM a93A03: Weak convergence + norm convergence ⟹ strong convergence, and weak lower semicontinuity of the norm

## 1. Informal proof

**Why it's hard.** Weak convergence means ⟨hₙ, k⟩ → ⟨h, k⟩ for every k, but this controls only one "direction" at a time and says nothing directly about ||hₙ - h||. The norm involves all directions simultaneously. Part (b) says the norm can only drop under weak limits (it's lower semicontinuous), which is the opposite of what one might naively expect.

**The key insight.** Expand ||hₙ - h||² = ||hₙ||² - 2 Re⟨hₙ, h⟩ + ||h||². Weak convergence gives ⟨hₙ, h⟩ → ⟨h, h⟩ = ||h||² (take k = h). So ||hₙ - h||² = ||hₙ||² - 2Re⟨hₙ, h⟩ + ||h||² → ||h||² - 2||h||² + ||h||² = 0 if ||hₙ|| → ||h||.

**Proof.**

**(a)** Expand the norm squared:

||hₙ - h||² = ⟨hₙ - h, hₙ - h⟩ = ||hₙ||² - 2 Re⟨hₙ, h⟩ + ||h||².

Since hₙ ⇀ h (weak convergence), taking k = h:

⟨hₙ, h⟩ → ⟨h, h⟩ = ||h||².

So Re⟨hₙ, h⟩ → ||h||² (in the real case, ⟨hₙ, h⟩ is real; in the complex case, Re⟨hₙ, h⟩ → Re(||h||²) = ||h||²).

By hypothesis, ||hₙ|| → ||h||, so ||hₙ||² → ||h||².

Therefore:

||hₙ - h||² → ||h||² - 2||h||² + ||h||² = 0.

Hence ||hₙ - h|| → 0. ✓

**(b)** From the expansion above (without the norm convergence hypothesis):

0 ≤ ||hₙ - h||² = ||hₙ||² - 2 Re⟨hₙ, h⟩ + ||h||².

So 2 Re⟨hₙ, h⟩ ≤ ||hₙ||² + ||h||².

Taking lim inf (and using Re⟨hₙ, h⟩ → ||h||²):

2||h||² ≤ lim inf(||hₙ||² + ||h||²) = lim inf ||hₙ||² + ||h||².

So ||h||² ≤ lim inf ||hₙ||².

Taking square roots (using monotonicity of sqrt and the fact that lim inf of nonneg terms behaves well):

||h|| ≤ lim inf ||hₙ||.

More directly: 0 ≤ lim inf ||hₙ - h||² = lim inf ||hₙ||² - 2||h||² + ||h||² = lim inf ||hₙ||² - ||h||². So ||h||² ≤ lim inf ||hₙ||², hence ||h|| ≤ lim inf ||hₙ||. ✓ ∎

**What connects.** Part (a) is the Kadec-Klee property (or Radon-Riesz property) for Hilbert spaces: weak convergence + norm convergence ⟹ strong convergence. This holds in all uniformly convex spaces (Milman-Pettis), and Hilbert spaces are uniformly convex. Part (b) is the weak lower semicontinuity of the norm, which holds in every normed space (not just Hilbert). Together they characterise the relationship between weak and strong topologies in Hilbert space. Part (a) is crucial for proving strong convergence from variational methods (minimising sequences in PDE theory often converge weakly by compactness, and the norm convergence is established separately). Part (b) is used in the direct method of the calculus of variations (the energy can only decrease under weak limits).

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.LiminfLimsup

open Filter Topology InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Weak convergence in a Hilbert space. -/
def WeakTendsto (h : ℕ → H) (x : H) : Prop :=
  ∀ k : H, Tendsto (fun n => ⟪h n, k⟫_ℝ) atTop (𝓝 ⟪x, k⟫_ℝ)

/-- The key identity: ‖hₙ - h‖² = ‖hₙ‖² - 2⟨hₙ,h⟩ + ‖h‖². -/
lemma norm_sub_sq_expansion (a b : H) :
    ‖a - b‖ ^ 2 = ‖a‖ ^ 2 - 2 * ⟪a, b⟫_ℝ + ‖b‖ ^ 2 := by
  sorry

/-- Weak convergence gives ⟨hₙ, h⟩ → ‖h‖². -/
lemma inner_tendsto_norm_sq
    {h : ℕ → H} {x : H}
    (hweak : WeakTendsto h x) :
    Tendsto (fun n => ⟪h n, x⟫_ℝ) atTop (𝓝 (‖x‖ ^ 2)) := by
  sorry

/-- Part (a): weak + norm convergence ⟹ strong convergence (Kadec-Klee). -/
theorem strong_of_weak_and_norm
    {h : ℕ → H} {x : H}
    (hweak : WeakTendsto h x)
    (hnorm : Tendsto (fun n => ‖h n‖) atTop (𝓝 ‖x‖)) :
    Tendsto (fun n => ‖h n - x‖) atTop (𝓝 0) := by
  sorry

/-- Equivalent: hₙ → h strongly. -/
theorem tendsto_of_weak_and_norm
    {h : ℕ → H} {x : H}
    (hweak : WeakTendsto h x)
    (hnorm : Tendsto (fun n => ‖h n‖) atTop (𝓝 ‖x‖)) :
    Tendsto h atTop (𝓝 x) := by
  sorry

/-- Part (b): weak lower semicontinuity of the norm.
    ‖h‖ ≤ lim inf ‖hₙ‖. -/
theorem norm_le_liminf_of_weak
    {h : ℕ → H} {x : H}
    (hweak : WeakTendsto h x) :
    ‖x‖ ≤ liminf (fun n => (‖h n‖ : ℝ)) atTop := by
  sorry

/-- Equivalent via squares: ‖h‖² ≤ lim inf ‖hₙ‖². -/
theorem norm_sq_le_liminf_norm_sq_of_weak
    {h : ℕ → H} {x : H}
    (hweak : WeakTendsto h x) :
    ‖x‖ ^ 2 ≤ liminf (fun n => ‖h n‖ ^ 2) atTop := by
  sorry

/-- Complex Hilbert space version of part (a). -/
theorem strong_of_weak_and_norm_complex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {h : ℕ → E} {x : E}
    (hweak : ∀ k : E, Tendsto (fun n => ⟪h n, k⟫_ℂ) atTop (𝓝 ⟪x, k⟫_ℂ))
    (hnorm : Tendsto (fun n => ‖h n‖) atTop (𝓝 ‖x‖)) :
    Tendsto h atTop (𝓝 x) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `InnerProductSpace ℝ H` — real inner product (Hilbert) space
- `CompleteSpace H` — completeness (making it a Hilbert space)
- `inner` / `⟪·, ·⟫_ℝ` — the real inner product
- `Filter.liminf` — lim inf along a filter
- `Filter.atTop` — cofinite filter on ℕ
- `Filter.Tendsto` — convergence along a filter

**Key lemmas:**
- `inner_self_eq_norm_sq` — ⟨x, x⟩ = ‖x‖² (connects inner product to norm)
- `norm_sub_sq_real` / `@inner_sub_left` / `@inner_sub_right` — expansion ‖a-b‖² = ‖a‖² - 2⟨a,b⟩ + ‖b‖². Mathlib likely has this as `norm_sub_sq_real`
- `real_inner_comm` — ⟨a,b⟩ = ⟨b,a⟩ (symmetry of real inner product)
- `Tendsto.sub` / `Tendsto.add` / `Tendsto.mul_const` — algebra of limits
- `tendsto_nhds_of_tendsto_nhds_nonneg_sq` — if ‖xₙ‖² → 0 then ‖xₙ‖ → 0
- `sq_nonneg` — ‖hₙ - h‖² ≥ 0 (for part (b))
- `Filter.liminf_le_liminf` — monotonicity of liminf
- `Filter.le_liminf_of_le` — lower bounds on liminf
- `tendsto_iff_norm_sub_tendsto_zero` — ‖hₙ - h‖ → 0 ↔ hₙ → h in norm
- `Real.sqrt_le_sqrt` — for passing from ‖h‖² ≤ lim inf ‖hₙ‖² to ‖h‖ ≤ lim inf ‖hₙ‖

**Tactic hints:**
- `simp only [norm_sub_sq_real]` — expanding ‖hₙ - h‖²
- `have h1 := hweak x` — specialising weak convergence to k = h
- `rw [inner_self_eq_norm_sq] at h1` — converting ⟨x,x⟩ to ‖x‖²
- `calc ‖h n - x‖^2 = ...` — for the expansion chain
- `linarith [sq_nonneg (‖h n - x‖)]` — for part (b), 0 ≤ ‖hₙ-h‖²
- `exact tendsto_iff_norm_sub_tendsto_zero.mpr ...` — converting norm convergence
- `nlinarith` — combining the algebraic identity with the limits
- `exact?` — finding the norm expansion lemma
- `filter_upwards` — for passing between filter statements