# Informal Solution: t94J07

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

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
