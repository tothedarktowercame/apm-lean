# Informal Solution: t96A08

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

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
