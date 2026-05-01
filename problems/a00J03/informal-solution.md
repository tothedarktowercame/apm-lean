# Informal Solution: a00J03

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Claim.** T_φ : f ↦ f ∘ φ is an isometric isomorphism on Lp(X,μ) for 1 ≤ p < ∞.

**Isometry.** For f ∈ Lp:

‖T_φ(f)‖_p^p = ∫ |f(φ(x))|^p dμ(x).

Change of variables y = φ(x), with μ(φ⁻¹(A)) = μ(A) (measure preservation):

= ∫ |f(y)|^p dμ(y) = ‖f‖_p^p.

Taking p-th roots: ‖T_φ(f)‖_p = ‖f‖_p. So T_φ is an isometry.

(This is the one-step core: the change of variables formula for measure-preserving maps gives the isometry immediately. The measure-preservation hypothesis μ(φ⁻¹A) = μ(A) is exactly what makes the substitution work.)

**Linearity.** T_φ(f+g) = (f+g) ∘ φ = f∘φ + g∘φ = T_φ(f) + T_φ(g). Similarly T_φ(cf) = c·T_φ(f). Trivial.

**Surjectivity.** For g ∈ Lp, define f = g ∘ φ⁻¹. Then T_φ(f) = f ∘ φ = g ∘ φ⁻¹ ∘ φ = g.

We must check f ∈ Lp: ‖f‖_p = ‖g ∘ φ⁻¹‖_p = ‖g‖_p (by the isometry applied to φ⁻¹, which is also measure-preserving since μ((φ⁻¹)⁻¹A) = μ(φ(A)) = μ(A) — the last equality uses μ(φ⁻¹(φA)) = μ(φA) but we actually need μ(φA) = μ(A); this follows from φ measure-preserving + bijectivity: φ(A) = (φ⁻¹)⁻¹(A), so μ(φ(A)) = μ((φ⁻¹)⁻¹(A)) = μ(A) since φ⁻¹ is also measure-preserving).

**Bijectivity.** T_φ has inverse T_{φ⁻¹}: T_{φ⁻¹} ∘ T_φ(f) = f ∘ φ ∘ φ⁻¹ = f, and T_φ ∘ T_{φ⁻¹}(f) = f ∘ φ⁻¹ ∘ φ = f.

Therefore T_φ is a surjective isometry = isometric isomorphism. ∎

**Stage 2 — LEMMA DEPENDENCY GRAPH**

| # | Lemma | Lean type | Source | Critical? |
|---|-------|-----------|--------|-----------|
| 1 | **Change of variables** | `eLpNorm (g ∘ f) p μ = eLpNorm g p ν` for MeasurePreserving f | Mathlib: `eLpNorm_comp_measurePreserving` | YES |
| 2 | **Isometry on Lp** | `Isometry (compMeasurePreserving f hf)` | Mathlib: `isometry_compMeasurePreserving` | YES |
| 3 | **Bijectivity** | φ bijection + φ⁻¹ measurable → T_φ has inverse T_{φ⁻¹} | Custom: compose `compMeasurePreserving` for φ and φ⁻¹ | YES |
| 4 | **φ⁻¹ is measure-preserving** | `MeasurePreserving φ⁻¹ μ μ` from bijectivity + μ(φ⁻¹A) = μ(A) | Custom from hypotheses | Foundation |

**Stage 3 — LEAN FORMALIZATION**

The isometry direction is a SINGLE Mathlib lemma: `isometry_compMeasurePreserving`. The isomorphism requires showing φ⁻¹ is also measure-preserving and composing the two maps. See Main.lean.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The isometry direction is genuinely trivial — both on paper and in Lean. The change of variables formula for measure-preserving maps (`eLpNorm_comp_measurePreserving`) is the entire content. In Lean, the isometry is literally one line: `isometry_compMeasurePreserving hφ`.

The surjectivity/bijectivity is the slightly harder part: you need φ⁻¹ to be measure-preserving too. On paper this follows from μ(φ(A)) = μ(A) (which uses bijectivity to write φ(A) = (φ⁻¹)⁻¹(A)). In Lean, this needs `MeasurePreserving` for the inverse map, which may require composing `MeasurableEquiv` with the measure-preservation hypothesis.
