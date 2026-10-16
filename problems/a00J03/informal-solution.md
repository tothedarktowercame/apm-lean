# Informal Solution: a00J03

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Claim.** $T_\phi : f \mapsto f \circ \phi$ is an isometric isomorphism on $Lp(X,\mu)$ for $1 \leq p < \infty$.

**Isometry.** For $f \in Lp$:

$\Vert T_\phi(f)\Vert _p^p = \int |f(\phi(x))|^p d\mu(x)$.

Change of variables $y = \phi(x)$, with $\mu(\phi^{-1}(A)) = \mu(A)$ (measure preservation):

$= \int |f(y)|^p d\mu(y) = \Vert f\Vert _p^p$.

Taking $p$-th roots: $\Vert T_\phi(f)\Vert _p = \Vert f\Vert _p$. So $T_\phi$ is an isometry.

(This is the one-step core: the change of variables formula for measure-preserving maps gives the isometry immediately. The measure-preservation hypothesis $\mu(\phi^{-1}A) = \mu(A)$ is exactly what makes the substitution work.)

**Linearity.** $T_\phi(f+g) = (f+g) \circ \phi = f\circ\phi + g\circ\phi = T_\phi(f) + T_\phi(g)$. Similarly $T_\phi(cf) = c\cdot T_\phi(f)$. Trivial.

**Surjectivity.** For $g \in Lp$, define $f = g \circ \phi^{-1}$. Then $T_\phi(f) = f \circ \phi = g \circ \phi^{-1} \circ \phi = g$.

We must check $f \in Lp$: $\Vert f\Vert _p = \Vert g \circ \phi^{-1}\Vert _p = \Vert g\Vert _p$ (by the isometry applied to $\phi^{-1}$, which is also measure-preserving since $\mu((\phi^{-1})^{-1}A) = \mu(\phi(A)) = \mu(A)$ — the last equality uses $\mu(\phi^{-1}(\phi A)) = \mu(\phi A)$ but we actually need $\mu(\phi A) = \mu(A)$; this follows from $\phi$ measure-preserving + bijectivity: $\phi(A) = (\phi^{-1})^{-1}(A)$, so $\mu(\phi(A)) = \mu((\phi^{-1})^{-1}(A)) = \mu(A)$ since $\phi^{-1}$ is also measure-preserving).

**Bijectivity.** $T_\phi$ has inverse $T_{\phi^{-1}}$: $T_{\phi^{-1}} \circ T_\phi(f) = f \circ \phi \circ \phi^{-1} = f$, and $T_\phi \circ T_{\phi^{-1}}(f) = f \circ \phi^{-1} \circ \phi = f$.

Therefore $T_\phi$ is a surjective isometry = isometric isomorphism. ∎

**Stage 2 — LEMMA DEPENDENCY GRAPH**

| # | Lemma | Lean type | Source | Critical? |
|---|-------|-----------|--------|-----------|
| 1 | **Change of variables** | `eLpNorm (g ∘ f) p μ = eLpNorm g p ν` for MeasurePreserving f | Mathlib: `eLpNorm_comp_measurePreserving` | YES |
| 2 | **Isometry on $Lp$** | `Isometry (compMeasurePreserving f hf)` | Mathlib: `isometry_compMeasurePreserving` | YES |
| 3 | **Bijectivity** | $\phi$ bijection + $\phi^{-1}$ measurable $\to$ $T_\phi$ has inverse $T_{\phi^{-1}}$ | Custom: compose `compMeasurePreserving` for $\phi$ and $\phi^{-1}$ | YES |
| 4 | **$\phi^{-1}$ is measure-preserving** | `MeasurePreserving φ⁻¹ μ μ` from bijectivity + $\mu(\phi^{-1}A) = \mu(A)$ | Custom from hypotheses | Foundation |

**Stage 3 — LEAN FORMALIZATION**

The isometry direction is a SINGLE Mathlib lemma: `isometry_compMeasurePreserving`. The isomorphism requires showing $\phi^{-1}$ is also measure-preserving and composing the two maps. See Main.lean.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The isometry direction is genuinely trivial — both on paper and in Lean. The change of variables formula for measure-preserving maps (`eLpNorm_comp_measurePreserving`) is the entire content. In Lean, the isometry is literally one line: `isometry_compMeasurePreserving hφ`.

The surjectivity/bijectivity is the slightly harder part: you need $\phi^{-1}$ to be measure-preserving too. On paper this follows from $\mu(\phi(A)) = \mu(A)$ (which uses bijectivity to write $\phi(A) = (\phi^{-1})^{-1}(A)$). In Lean, this needs `MeasurePreserving` for the inverse map, which may require composing `MeasurableEquiv` with the measure-preservation hypothesis.
