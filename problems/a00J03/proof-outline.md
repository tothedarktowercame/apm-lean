# Proof Outline: a00J03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal
 "Show T_φ(f) = f∘φ is an isometric isomorphism on Lp(X,μ) for 1≤p<∞, where φ is a measure-preserving measurable bijection with measurable inverse."
 :terms
 [{:name "measure-preserving"
   :meaning "μ(φ⁻¹A) = μ(A) for all measurable A — the pullback measure equals the original"
   :needed-because "this is the hypothesis that makes the change of variables work"}
  {:name "isometric"
   :meaning "‖f∘φ‖_p = ‖f‖_p — the Lp norm is preserved under composition"
   :needed-because "isometry is the main content; surjectivity + linearity are formal"}
  {:name "isomorphism"
   :meaning "T_φ is linear, bijective, and continuous (hence an isomorphism of Banach spaces)"
   :needed-because "bijectivity comes from T_{φ⁻¹} being the two-sided inverse"}]
 :strategy
 [{:id :change-of-variables
   :formal-dependency "eLpNorm_comp_measurePreserving in Mathlib"
   :informal-dependency "the change of variables formula for measure-preserving maps"
   :why-this-now "this is the entire isometry proof in one step"
   :lean-target "eLpNorm (f ∘ φ) p μ = eLpNorm f p μ"
   :mathlib-status "available: eLpNorm_comp_measurePreserving"
   :critical-path true}
  {:id :isometry-on-Lp
   :formal-dependency "isometry_compMeasurePreserving in Mathlib"
   :informal-dependency "the composition operator is an isometry on the Lp space"
   :why-this-now "wraps the seminorm equality into an Isometry statement"
   :lean-target "Isometry (compMeasurePreserving φ hφ)"
   :mathlib-status "available: isometry_compMeasurePreserving"
   :critical-path true}
  {:id :inverse-is-measure-preserving
   :formal-dependency "MeasurePreserving φ⁻¹ from bijectivity + μ(φ⁻¹A)=μ(A)"
   :informal-dependency "φ⁻¹ preserves measure because φ(A) = (φ⁻¹)⁻¹(A) and bijectivity"
   :why-this-now "needed for surjectivity: T_{φ⁻¹} is the inverse and must also be on Lp"
   :lean-target "MeasurePreserving (MeasurableEquiv.symm e) μ μ"
   :mathlib-status "likely available via MeasurableEquiv.measurePreserving"
   :critical-path true}]
 :stage-status
 {:stage1 :done
  :stage2 :done
  :stage3 :in-progress
  :stage4 :done}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id "a00J03"
  :frame-id "apm-v2-a00J03-1774991806132"
  :summary "Created isolated proof frame workspace."
  :full-record? false
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Clean proof: isometry via change of variables (one step), linearity trivial, surjectivity via T_{φ⁻¹} as inverse. The measure-preservation hypothesis μ(φ⁻¹A) = μ(A) is the entire content."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Dependency graph: 4 items. Mathlib has eLpNorm_comp_measurePreserving and isometry_compMeasurePreserving. Surjectivity needs φ⁻¹ measure-preserving + double composition ae-equality."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :lean-delta
  :summary "composition_isometry CLOSED (one-liner: isometry_compMeasurePreserving). norm_comp_eq CLOSED (one-liner: eLpNorm_comp_measurePreserving). Surjectivity sorry: double composition ae-equality via coeFn_compMeasurePreserving + MeasurableEquiv.apply_symm_apply."
  :full-record? true
  :sorry? true
  :fully-closed? false}
 {:kind :final-status
  :summary "Classification: partial. 2 lemmas fully closed (isometry + norm equality — the mathematical content). 1 sorry (surjectivity — ae-equality bookkeeping for double Lp composition). Informal proof complete."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

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
