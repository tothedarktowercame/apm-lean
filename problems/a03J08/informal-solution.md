

# APM a03J08: Surjectivity of an analytic function blowing up at all boundary points

## 1. Informal proof

**Why it's hard.** The domain D = ℂ \ F is open but not simply connected, and f is not assumed injective or proper in the usual sense. Showing surjectivity (every complex value is attained) requires ruling out omitted values, which suggests using either the open mapping theorem, Picard's theorem, or a topological/compactness argument.

**The key insight.** If f omits a value w₀ ∈ ℂ, then 1/(f(z) - w₀) is analytic on D and bounded (since |f| → ∞ at every boundary point of D, including ∞, forces |f - w₀| → ∞ at every boundary point, making 1/|f - w₀| → 0). But a bounded analytic function on D with removable singularities at the finite set F extends to an entire bounded function, hence is constant by Liouville — contradicting |f| → ∞.

**Proof.**

Suppose for contradiction that there exists w₀ ∈ ℂ \ f(D). Define g(z) = 1/(f(z) - w₀) on D. Then g is analytic on D (since f(z) ≠ w₀ for all z ∈ D).

*g is bounded near each point of F:* For each zα ∈ F, |f(z)| → ∞ as z → zα, so |f(z) - w₀| → ∞, hence |g(z)| = 1/|f(z) - w₀| → 0 as z → zα. In particular, g is bounded in a punctured neighbourhood of each zα.

*g is bounded near ∞:* |f(z)| → ∞ as |z| → ∞, so |g(z)| → 0 as |z| → ∞.

*g extends to an entire function:* At each zα ∈ F, g is analytic on a punctured neighbourhood and bounded, so by the Riemann removable singularity theorem, g extends analytically to zα (with g(zα) = 0). After extending at all points of F, g becomes entire.

*g is bounded:* g is continuous on all of ℂ (entire), and |g(z)| → 0 as |z| → ∞. A continuous function tending to 0 at infinity is bounded (it is bounded on the compact set {|z| ≤ R} by continuity, and bounded by ε outside for R large).

*Liouville:* g is entire and bounded, so g is constant by Liouville's theorem.

*Contradiction:* Since |g(z)| → 0 as |z| → ∞, the constant must be 0, so g ≡ 0. But g(z) = 1/(f(z) - w₀) ≠ 0 for all z ∈ D. Contradiction.

Therefore f(D) = ℂ. ∎

**What connects.** This result is a concrete manifestation of the Casorati-Weierstrass / great Picard philosophy: an analytic function that blows up at every boundary component of its domain (including the point at infinity) must hit every complex value. The proof uses the trio of Riemann removable singularities + Liouville, which is the elementary substitute for Picard's theorem in situations where the singularities are all poles (or at least where 1/f is bounded near each singularity). The result generalises: f(D) misses at most one value if f has essential singularities (by great Picard), and misses no values if all singularities are poles (as in this problem, where |f| → ∞ forces poles). The properness condition (|f| → ∞ at every boundary point, including ∞) makes f a proper map ℂ \ F → ℂ, and proper holomorphic maps are surjective onto connected targets.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.ContinuousOn
import Mathlib.Order.Filter.Basic

open Complex Metric Set Filter Topology

noncomputable section

/-- Main theorem: if f is analytic on ℂ \ F (F finite),
    |f(z)| → ∞ as |z| → ∞ and as z → zα for each zα ∈ F,
    then f is surjective. -/
theorem analytic_blowup_surjective
    {F : Finset ℂ}
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (↑F)ᶜ)
    (hf_infty : Tendsto (‖f ·‖) (cocompact ℂ) atTop)
    (hf_poles : ∀ zα ∈ F,
      Tendsto (‖f ·‖) (𝓝[≠] zα) atTop) :
    Function.Surjective (Set.restrict (↑F)ᶜ f) := by
  sorry

/-- Equivalently: f(ℂ \ F) = ℂ. -/
theorem analytic_blowup_range
    {F : Finset ℂ}
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (↑F)ᶜ)
    (hf_infty : Tendsto (‖f ·‖) (cocompact ℂ) atTop)
    (hf_poles : ∀ zα ∈ F,
      Tendsto (‖f ·‖) (𝓝[≠] zα) atTop) :
    f '' (↑F)ᶜ = univ := by
  sorry

/-- Key step: if w₀ is omitted, then 1/(f - w₀) is bounded
    near each point of F (hence has removable singularities). -/
lemma reciprocal_bounded_near_poles
    {F : Finset ℂ}
    {f : ℂ → ℂ} {w₀ : ℂ}
    (hf_poles : ∀ zα ∈ F,
      Tendsto (‖f ·‖) (𝓝[≠] zα) atTop)
    (zα : ℂ) (hzα : zα ∈ F) :
    ∃ r > 0, BddAbove ((fun z => ‖1 / (f z - w₀)‖) ''
      (punctured_nhds_ball zα r)) := by
  sorry

/-- After removing singularities, 1/(f - w₀) extends to
    an entire function. -/
lemma reciprocal_extends_entire
    {F : Finset ℂ}
    {f : ℂ → ℂ} {w₀ : ℂ}
    (hf_holo : DifferentiableOn ℂ f (↑F)ᶜ)
    (hf_omits : ∀ z ∈ (↑F)ᶜ, f z ≠ w₀)
    (hf_poles : ∀ zα ∈ F,
      Tendsto (‖f ·‖) (𝓝[≠] zα) atTop) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ z ∈ (↑F)ᶜ, g z = 1 / (f z - w₀) := by
  sorry

/-- The extended function vanishes at infinity, so
    Liouville forces it to be identically zero — contradiction. -/
lemma reciprocal_vanishes_at_infty
    {f : ℂ → ℂ} {w₀ : ℂ}
    (hf_infty : Tendsto (‖f ·‖) (cocompact ℂ) atTop) :
    Tendsto (fun z => ‖1 / (f z - w₀)‖) (cocompact ℂ) (𝓝 0) := by
  sorry

/-- Liouville: a bounded entire function is constant. -/
lemma liouville_constant
    {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hbdd : ∃ M, ∀ z, ‖g z‖ ≤ M) :
    ∃ c, ∀ z, g z = c := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `DifferentiableOn ℂ f S` — holomorphicity on the punctured plane
- `Differentiable ℂ g` — entirety (after removing singularities)
- `Finset ℂ` — the finite set F
- `Filter.cocompact ℂ` — filter for |z| → ∞
- `nhdsWithin z {z}ᶜ` / `𝓝[≠] z` — punctured neighbourhood filter
- `Filter.atTop` — for |f| → ∞
- `Function.Surjective` — surjectivity predicate

**Key lemmas:**
- `Complex.differentiableOn_update_of_bounded_of_isOpen` / `Complex.differentiable_update_of_bounded` — Riemann removable singularity theorem: bounded + analytic near a puncture ⟹ extends analytically. In `Mathlib.Analysis.Complex.RemovableSingularity`
- `Complex.Polynomial.liouville` / `Differentiable.apply_eq_apply_of_bounded` — Liouville's theorem: bounded entire function is constant. In `Mathlib.Analysis.Complex.Liouville`
- `Filter.Tendsto.norm_atTop` — if ‖f(z)‖ → ∞ then |1/(f(z) - w₀)| → 0
- `Filter.Tendsto.inv_tendsto_atTop` — 1/x → 0 as x → ∞
- `Filter.Tendsto.comp` — composition of tendsto statements
- `DifferentiableOn.div` — analyticity of 1/(f - w₀)
- `isCompact_closedBall` — for compactness arguments
- `ContinuousOn.norm` — continuity of the norm
- `Finset.prod_dvd_prod_of_dvd` — not directly, but finiteness of F used throughout
- `Set.compl_iUnion` / `Finset.coe_compl` — complement of a finite set is open

**Tactic hints:**
- `by_contra h; push_neg at h` — assume w₀ is omitted, derive contradiction
- `obtain ⟨w₀, hw₀⟩ := h` — extract the omitted value
- `refine ⟨fun z => ..., ?_, ?_⟩` — construct the extended function
- `exact?` — finding the removable singularity theorem
- `simp [div_ne_zero]` — for 1/(f-w₀) ≠ 0
- `positivity` — for ‖f(z) - w₀‖ > 0
- `filter_upwards` — for eventually-holds arguments near poles and at infinity
- `norm_num` — for basic arithmetic in the Liouville contradiction
- `absurd` — the final contradiction (g ≡ 0 but g ≠ 0)