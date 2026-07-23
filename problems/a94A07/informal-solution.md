

# APM a94A07: Injective entire functions are affine linear

## 1. Informal proof

**Why it's hard.** An entire function can be very wild (e.g., e^z is entire but not injective). Showing that injectivity forces f to be a polynomial of degree exactly 1 requires classifying the singularity at ∞ and ruling out both essential singularities and poles of order ≥ 2.

**The key insight.** Consider g(w) = f(1/w) near w = 0, which captures the behaviour of f at ∞. If f has an essential singularity at ∞, Casorati-Weierstrass (or Picard) says the image of f near ∞ is dense — destroying injectivity. If f has a pole of order n ≥ 2 at ∞, then f is a polynomial of degree n, which takes every value n times (counting multiplicity) — also destroying injectivity for n ≥ 2. So f must have a simple pole at ∞, meaning f is a degree-1 polynomial.

**Proof.**

The function f is entire, so g(w) = f(1/w) is analytic on ℂ \ {0} with an isolated singularity at w = 0. The singularity at w = 0 for g corresponds to the behaviour of f at z = ∞. There are three cases:

*Case 1: Removable singularity.* Then f is bounded as |z| → ∞, hence bounded on all of ℂ. By Liouville, f is constant — contradicting injectivity (a constant function is not one-to-one since the domain is uncountable, or more precisely not injective on any two distinct points). ✗

*Case 2: Essential singularity.* By the Casorati-Weierstrass theorem, for every w₀ ∈ ℂ and every ε > 0, the image f({|z| > R}) is dense in ℂ for every R. In particular, f takes values arbitrarily close to f(0) in the region {|z| > R}. Since f is continuous and the image of large |z| is dense, f cannot be injective: the image of {|z| > R} and the image of {|z| < 1} must overlap for R large enough (by density, f({|z|>R}) comes within ε of f(0), and by continuity there exists z₁ near 0 and z₂ far away with f(z₁) = f(z₂)). More precisely, by the great Picard theorem, f takes every value (with at most one exception) infinitely often near ∞, contradicting injectivity. ✗

*Case 3: Pole of order n.* Then f is a polynomial of degree n. If n ≥ 2, the fundamental theorem of algebra says f(z) - w₀ = 0 has n roots (with multiplicity) for every w₀. For a generic w₀, these roots are distinct (the discriminant is nonzero for all but finitely many w₀), so f takes the value w₀ at n ≥ 2 distinct points. This contradicts injectivity. ✗ for n ≥ 2.

If n = 1, then f(z) = a₀ + a₁z with a₁ ≠ 0. This is injective (f(z₁) = f(z₂) ⟹ a₁z₁ = a₁z₂ ⟹ z₁ = z₂). ✓

Therefore f(z) = a₀ + a₁z with a₁ ≠ 0. ∎

**What connects.** This classifies the automorphisms of ℂ: Aut(ℂ) = {z ↦ a₀+a₁z : a₁ ≠ 0} ≅ Aff(1, ℂ), the affine group. The proof uses the trichotomy of isolated singularities (removable / pole / essential) applied at ∞, which is a standard technique in complex analysis. The result fails for non-injective functions (e.g., z² is entire but not linear) and for functions on proper subdomains (e.g., z² is injective on the right half-plane). The analogous result for injective holomorphic maps between disks gives rise to the Schwarz lemma and Möbius transformations.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Polynomial

open Complex Polynomial

noncomputable section

/-- Main theorem: an injective entire function is affine linear. -/
theorem entire_injective_is_affine
    {f : ℂ → ℂ}
    (hf_holo : Differentiable ℂ f)
    (hf_inj : Function.Injective f) :
    ∃ a₀ a₁ : ℂ, a₁ ≠ 0 ∧ ∀ z, f z = a₀ + a₁ * z := by
  sorry

/-- f is a polynomial (the singularity at ∞ is not essential). -/
lemma entire_injective_is_polynomial
    {f : ℂ → ℂ}
    (hf_holo : Differentiable ℂ f)
    (hf_inj : Function.Injective f) :
    ∃ p : ℂ[X], ∀ z, f z = Polynomial.aeval z p := by
  sorry

/-- An injective polynomial has degree exactly 1. -/
lemma injective_polynomial_degree_one
    {p : ℂ[X]}
    (hp_inj : Function.Injective (fun z : ℂ => Polynomial.aeval z p)) :
    p.natDegree = 1 := by
  sorry

/-- Degree ≥ 2 polynomial is not injective (takes generic values
    at multiple points). -/
lemma polynomial_degree_ge_two_not_injective
    {p : ℂ[X]} (hdeg : 2 ≤ p.natDegree) :
    ¬Function.Injective (fun z : ℂ => Polynomial.aeval z p) := by
  sorry

/-- Casorati-Weierstrass: essential singularity at ∞ implies
    f is not injective. -/
lemma essential_singularity_not_injective
    {f : ℂ → ℂ}
    (hf_holo : Differentiable ℂ f)
    (hf_ess : ¬∃ p : ℂ[X], ∀ z, f z = Polynomial.aeval z p)
    (hf_unbdd : ¬∃ M, ∀ z, ‖f z‖ ≤ M) :
    ¬Function.Injective f := by
  sorry

/-- A degree-1 polynomial is injective. -/
lemma degree_one_injective
    {a₀ a₁ : ℂ} (ha₁ : a₁ ≠ 0) :
    Function.Injective (fun z : ℂ => a₀ + a₁ * z) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `Differentiable ℂ f` — entirety
- `Function.Injective f` — injectivity
- `Polynomial ℂ` / `ℂ[X]` — complex polynomials
- `Polynomial.aeval` — polynomial evaluation
- `Polynomial.natDegree` — degree

**Key lemmas:**
- `Differentiable.apply_eq_apply_of_bounded` — Liouville's theorem (rules out bounded entire ⟹ constant). In `Mathlib.Analysis.Complex.Liouville`
- `Polynomial.card_roots_le_degree` — a degree-n polynomial has at most n roots
- `Polynomial.roots_eq_multiset_ofList` / `Polynomial.card_roots_eq_degree` — over ℂ (algebraically closed), a degree-n polynomial has exactly n roots with multiplicity
- `IsAlgClosed.exists_eq_mul_self` / `Complex.isAlgClosed` — ℂ is algebraically closed (FTA)
- `Polynomial.degree_eq_one_iff_of_ne_zero` — characterisation of degree-1 polynomials
- `Polynomial.aeval_eq_sum_range` — evaluation as coefficient sum
- `mul_left_cancel₀` — a₁z₁ = a₁z₂ ⟹ z₁ = z₂ when a₁ ≠ 0 (for degree-1 injectivity)

**Tactic hints:**
- `by_contra h_not_poly` — case split: is f a polynomial or not?
- `rcases hdeg with _ | _ | n` — case split on degree: 0, 1, or ≥ 2
- `exact absurd (Liouville ...) hf_inj.ne_const` — ruling out constant (degree 0)
- `obtain ⟨a₀, a₁, rfl⟩ := Polynomial.degree_eq_one_iff ...` — extracting coefficients from degree 1
- `refine ⟨a₀, a₁, ?_, fun z => ?_⟩` — packaging the result
- `field_simp` — for a₀ + a₁z₁ = a₀ + a₁z₂ ⟹ z₁ = z₂
- `exact?` — finding the right algebraic closure / root-counting lemma
- `omega` — for degree arithmetic (2 ≤ n)