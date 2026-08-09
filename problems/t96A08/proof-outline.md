# Proof Outline: t96A08

## Compiled progress

Classical choice selects an admissible path from `base` to each point. The
potential is defined as its concrete line integral, and `hindependent` proves
that its value equals the integral along every other admissible path with the
same endpoints. Thus existence and well-definedness of the potential are fully
compiled.

Constant paths are now proved admissible and their concrete line integral is
computed as zero. Consequently every function satisfying the path-integral
specification is proved to obey the canonical normalization `f base = 0`.
Moreover `apm_t96a08_potential_unique` proves that any two functions satisfying
the specification agree, so all global existence, normalization, and
uniqueness bookkeeping is compiled.

## Remaining Lean boundary

Local chart calculus must prove the potential smooth and identify its
manifold derivative with `ω`. This requires concatenating the chosen path with
a short chart-linear segment, splitting and reparameterizing the integral, and
differentiating the endpoint-dependent segment. No compatible manifold
one-form fundamental theorem or piecewise-smooth concatenation API was found.
The chart-linear derivative helper in `t00J04` only realizes a prescribed
cotangent vector at one point and does not supply the endpoint-dependent
integral identity needed here.

Hop 4 states this missing interface verbatim as `apm_t96A08_bridge_1`.  Its
hypotheses expose the smooth one-form, reachability, and the full path-integral
specification; its conclusion is exactly the smoothness and `mfderiv = omega`
pair needed by the final conjunct.  The bridge is intentionally left with a
`sorry` for a subsequent proof and the frozen main theorem is unchanged.

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Show that a path-independent smooth 1-form has a smooth potential and is exact."
 :terms [{:name "Path independence"
          :meaning "Line integrals of ω depend only on endpoints."
          :needed-because "It ensures f(p)=∫_γ ω is well defined and allows differentiation under the integral sign."}
         {:name "Local coordinates"
          :meaning "Choose charts so ω = Σ a_i dx^i with smooth a_i."
          :needed-because "Smoothness of f follows by differentiating coordinate expressions."}
         {:name "Exterior derivative"
          :meaning "df is the 1-form determined by directional derivatives of f."
          :needed-because "Once df=ω, exactness is immediate."}]
 :strategy [{:id :s1
             :formal-dependency "omega_path_independent_exact"
             :informal-dependency "Define f by integrating ω from the base point, check smoothness in charts, then show df=ω."
             :why-this-now "This mirrors the textbook proof: well-defined potential + calculus ⇒ exactness."
             :lean-target "exact_of_path_independent_form"
             :mathlib-status "Needs basic facts about smooth line integrals and exterior derivatives; Mathlib has smooth manifolds and differential forms but will require assembling existing lemmas."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't96A08'
  :frame-id 'apm-v2-t96A08-1775012559877'
  :summary "Created frame, sketched Mayer–Vietoris-style plan for ω."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1+2-completed
  :summary "Wrote the full path-independence solution plus lemma dependencies in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-attempt
  :summary "Explained the missing Mathlib infrastructure (manifold line integrals) blocking the Lean formalization; Main.lean currently holds only the module skeleton."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** “Path independence” screams conservative field, but on a manifold you no longer integrate along straight segments or quote the fundamental theorem of line integrals without work. The trap is to assert that the coordinate-wise antiderivative you would write down in ℝⁿ automatically patches together smoothly; you must use the hypothesis to show that the locally defined potentials agree on overlaps.

**Key insight.** Because every integral from the base point depends only on the endpoint, the function
\[f(p)=\int_{\gamma_{0,p}} \omega\]
is well defined. In local coordinates, differentiating this integral with respect to the endpoint recovers the coefficients of ω, so f is smooth and df=ω. Exactness then follows because ω= df by construction.

**Complete proof.**
Let M be connected and fix a base point 0∈M. For p∈M define f(p) as the integral of ω along any piecewise-smooth path γ from 0 to p. The hypothesis guarantees that f(p) is independent of γ.

*(a) f is smooth.* Pick a chart (U,φ) with coordinates x¹,…,xⁿ. For p∈U choose the path γ formed by following γ₀ to φ⁻¹(φ(p₀)) and then traveling inside U along coordinate lines; path-independence lets us replace any other path by this one. In coordinates ω can be written ω=Σ_i a_i(x) dx^i with smooth functions a_i. The contribution of the last leg inside U is simply ∫ Σ_i a_i(x(t)) x˙^i(t) dt, i.e. an integral of a smooth function of the endpoint. Differentiating f∘φ⁻¹ along the i-th coordinate gives a_i, so all partial derivatives exist and are continuous; hence f is C¹. Repeating the argument for higher derivatives shows f is smooth.

*(b) ω is exact.* Let v∈T_pM and pick a curve σ with σ(0)=p and σ˙(0)=v. Then
\[(df)_p(v)=\frac{d}{dt}\Big|_{t=0} f(σ(t)) = \frac{d}{dt}\Big|_{t=0} \int_{0\to σ(t)} ω = \omega_p(v),\]
where the last equality comes from shrinking the path integral to the short segment of σ. Thus ω=df, so ω is exact.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Path-independent integrals define a function.** Needed to show f is well defined on M.
- **Local expression ω=Σ a_i dx^i.** This allows us to differentiate f inside charts.
- **Differentiation under the integral sign.** Provides the equality of partial derivatives with the coefficients a_i, hence smoothness.
- **df matches ω.** Concluding step: evaluating df on tangent vectors reproduces ω, so ω is exact.

**Stage 3 — LEAN FORMALIZATION**

Mathlib currently lacks the manifold-level line-integral machinery needed to formalize this proof. There is no API for integrating smooth 1-forms along piecewise smooth paths or for defining primitives via integration from a base point. To complete the formalization we would need:
1. A definition of the integral of a differential 1-form along a smooth curve in a manifold together with functoriality under reparametrization and concatenation.
2. A theorem identifying the derivative of the potential f with the 1-form’s coefficients in coordinates.
3. A bridge between the coordinate-level calculations and the exterior derivative `df` implemented in Mathlib’s `SmoothVectorBundle`/`Cotangent` framework.
Until these pieces exist, the Lean file `/home/joe/code/apm-lean/ApmCanaries/Frames/T96A08/Apm_v2_t96A08_1775012559877/Main.lean` only contains the module skeleton.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once Mathlib gains line-integral infrastructure, the formal proof will mirror Stage 1: define `f` by integration, differentiate inside charts to show `f` is smooth, and use the short-curve calculation to deduce `df = ω`. The current textual solution documents exactly which statements need to be formalized.
