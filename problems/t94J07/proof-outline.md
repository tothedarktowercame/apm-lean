# Proof Outline: t94J07

## Closer hop 1

Three concrete prerequisites for the direct cylinder calculation now compile:
the standard parametrization has unit norm, its velocity is tangent to the
circle, and its values at `0` and `2π` agree.  Mathlib's
`extDeriv_pullback` was identified as the local differential identity needed
for the main argument.  The remaining work is to combine it with
differentation under the θ-integral, tangency of both homotopy partial
derivatives, periodic cancellation, and interval FTC in the homotopy
parameter.  The detailed searched boundary is recorded at the remaining
`sorry`.

## Closer hop 2

The endpoint cancellation is now established at the correct level.
`t94J07CircleVelocity_two_pi` supplements periodicity of the point, and
`t94J07PullbackCircleIntegrand_two_pi` proves equality of the entire frozen
integrand at `0` and `2π`, including the derivative applied to the velocity.
The corresponding statement is specialized to every homotopy slice.

The remaining work is tangency of the two homotopy partial derivatives and
the parametric-integral/exterior-derivative assembly; no endpoint algebra
remains hidden in that boundary.

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Use Stokes' theorem on the homotopy cylinder to show that homotopic pullbacks of a closed form have equal integrals."
 :terms [{:name "closed form"
          :meaning "A differential form ω with dω = 0."
          :needed-because "It makes the Stokes integral over the cylinder vanish (the exterior derivative of the pulled-back form is zero)."}
         {:name "homotopy cylinder"
          :meaning "The manifold X × [0,1] with boundary components X × {0}, X × {1}."
          :needed-because "The maps f and g appear as the restrictions of a smooth homotopy at the two boundary faces."}
         {:name "Stokes' theorem"
          :meaning "For a compact manifold with boundary M and a form η, ∫_{∂M} η = ∫_{M} dη."
          :needed-because "Applying it to the pullback of ω along the homotopy converts the vanishing interior integral into the equality of the two boundary integrals."}]
 :strategy [{:id :s1
             :formal-dependency "Stokes' theorem on cylinders"
             :informal-dependency "Stage 1 proof uses the trivial homotopy cylinder argument"
             :why-this-now "Pulling ω back along the homotopy H:X×I→Y and applying Stokes immediately relates the two boundary integrals."
             :lean-target "homotopy_invariance_closed_form_integral"
             :mathlib-status "Stokes' theorem and basic homotopy/pullback APIs exist in mathlib's manifold library, but wrapping them for forms is unfinished."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't94J07'
  :frame-id 'apm-v2-t94J07-1775011599250'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-2-completed
  :summary "Wrote the Stokes-on-the-homotopy-cylinder proof, mapped the pullback/exterior-derivative dependencies, and updated execute.md accordingly."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-attempt
  :summary "Attempted to set up the Lean proof but blocked because Mathlib lacks integration of top-degree forms and a Stokes theorem for compact manifolds-with-boundary; Main.lean is still a stub."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** The statement hides several layers of differential-topology machinery. Students tend to differentiate under the integral or try to compare the two pullbacks pointwise. The real issue is that the objects live on different manifolds (\(X\) versus \(X\times[0,1]\)) and the equality is global: it links integrals of top-degree forms, not pointwise functions. The main trap is forgetting that the integral of a closed form along a boundary is controlled by Stokes’ theorem applied to a *homotopy cylinder*.

**Key insight.** Package the smooth homotopy \(H:X\times[0,1]\to Y\) with the projection \(\pi_X:X\times[0,1]\to X\). The pullback \(H^{*}\omega\) is closed because \(\omega\) is closed and exterior differentiation commutes with pullbacks. Stokes’ theorem on the compact manifold with boundary \(X\times[0,1]\) then says
\[
0 = \int_{X\times[0,1]} d\big(H^{*}\omega\big) = \int_{\partial(X\times[0,1])} H^{*}\omega.
\]
By keeping careful track of orientations, the boundary integral splits into the difference of the two integrals we want.

**Complete proof.** Let \(H : X \times [0,1] \to Y\) be a smooth homotopy such that \(H(x,0)=f(x)\) and \(H(x,1)=g(x)\). Consider the \(n\)-form \(H^{*}\omega\) on \(X\times[0,1]\). Because pullback commutes with exterior differentiation, \(d\,(H^{*}\omega)=H^{*}(d\omega)=0\). The manifold \(X\times[0,1]\) is compact with boundary
\[
\partial(X\times[0,1]) = (X\times\{1\}) \cup (-X\times\{0\}),
\]
where the minus sign indicates the opposite orientation on the \(t=0\) face. By Stokes’ theorem,
\[
0 = \int_{X\times[0,1]} d(H^{*}\omega) = \int_{\partial(X\times[0,1])} H^{*}\omega
= \int_{X\times\{1\}} H^{*}\omega - \int_{X\times\{0\}} H^{*}\omega.
\]
On the boundary faces the pullback separates: \(H|_{X\times\{1\}} = g\circ\pi_X\) and \(H|_{X\times\{0\}} = f\circ\pi_X\), so the integrals reduce to the original ones on \(X\):
\[
\int_{X\times\{1\}} H^{*}\omega = \int_X g^{*}\omega, \qquad \int_{X\times\{0\}} H^{*}\omega = \int_X f^{*}\omega.
\]
Substituting into the Stokes identity yields
\(\int_X g^{*}\omega - \int_X f^{*}\omega = 0\), i.e.
\(\int_X f^{*}\omega = \int_X g^{*}\omega\), as required.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Homotopy cylinder + Stokes.** Formal: a version of Stokes’ theorem for compact manifolds with boundary (`integral_boundary_eq_integral_deriv`). Informal: used for the main equality. Why now: it’s the only bridge from interior closedness to boundary integrals.
- **Pullback commutes with d.** Formal dependency: functoriality of exterior derivative (`ExteriorDeriv.pullback`). Needed because it annihilates the interior integral.
- **Boundary orientation bookkeeping.** Formal dependency: orientation convention for `X × I` (faces appear with opposite signs). Needed to rewrite the boundary integral as \(∫_X g^{*}ω − ∫_X f^{*}ω\).

Lean search terms: `manifold Stokes`, `pullback exterior_deriv`, `orientation cylinder`, `integral_boundary_of_product`.

**Stage 3 — LEAN FORMALIZATION**

Mathlib’s manifold library currently lacks the integration theory for top-degree differential forms needed here (no `∫_X α` for a general compact oriented manifold, nor a packaged Stokes’ theorem). I opened `/home/joe/code/apm-lean/ApmCanaries/Frames/T94J07/Apm_v2_t94J07_1775011599250/Main.lean` to stub the statement, but coding stopped immediately because the relevant APIs (`IntegralOver`, smooth homotopies encoded as `SmoothMap`, and Stokes for forms) are not implemented yet. Any honest Lean proof would first require extending Mathlib with: (1) integration of differential forms over compact manifolds-with-boundary, and (2) a lemma expressing Stokes’ theorem for `X × I`. Until those features exist, the formal proof remains a tracked TODO; `lake build ...` still fails because the new theory is absent rather than because of `sorry`s.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The informal proof explicitly highlights the homotopy-cylinder/ Stokes mechanism that a formal development would need. Once Mathlib gains the missing integration/Stokes primitives, the Lean argument will literally follow Stage 1 line-for-line: pull back the closed form along the homotopy, apply Stokes on `X×I`, identify the boundary faces with \(f\) and \(g\). The write-up already emphasizes the orientation bookkeeping that the formal proof must mirror.
