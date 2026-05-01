# Informal Solution: aunk01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**
Why it is hard.  Students usually try to treat $A+y$ as a mere image of $A$ under $x \mapsto x+y$ and forget that the image of a Borel set under a measurable map is not always Borel; you must exploit that translation is a homeomorphism and use preimages instead.  For part (b) people frequently plug the indicator of $A$ into part (c), which breaks down when $m(A)=\infty$.  Finally, one has to justify the change of variables in (c) inside the Lebesgue framework, not just heuristically.

Key insight.  Translation is a homeomorphism of $\mathbb R$ and hence preserves the Borel $\sigma$-algebra.  Lebesgue measure is the Haar measure on the additive group of $\mathbb R$, so it is translation invariant.  Measure-preserving maps leave $L^1$ integrals unchanged.  Package those three statements and every part of the problem becomes an application of a general theorem.

Complete proof.  Fix $y\in\mathbb R$ and write $\tau_y(x)=x+y$.  (a) We have $A+y=\{z : z-y\in A\}=\tau_{-y}^{-1}(A)$.  Because $\tau_{-y}$ is continuous, the preimage of a Borel set is Borel, so $A+y$ is Borel.

(b) Lebesgue measure $m$ is translation invariant: for every Borel $B$, $m(\tau_y^{-1}(B))=m(B)$.  Using $B=A+y$ and $\tau_y^{-1}(A+y)=A$ we get $m(A+y)=m(A)$ whether or not $m(A)$ is finite.

(c) Let $f\in L^1(\mathbb R)$.  Since $\tau_y$ is measure preserving, the Lebesgue change-of-variables formula gives
\[\int_{\mathbb R} f(x+y)\,dm(x)=\int_{\mathbb R} f(\tau_y x)\,dm(x)=\int_{\mathbb R} f(x)\,dm(x).\]
That is exactly the desired equality.

**Stage 2 — LEMMA DEPENDENCY GRAPH**
1. Translation is continuous and invertible ⇒ preimages of Borel sets stay Borel ⇒ (a).
2. Lebesgue measure is translation-invariant ⇒ measure preservation for $\tau_y$ ⇒ (b).
3. Measure-preserving change of variables ⇒ integral invariance ⇒ (c), depending on step 2.

**Stage 3 — LEAN FORMALIZATION**
Planned path: define the translation map once, reuse its continuity to get (a) via preimages, call the Mathlib lemma asserting `MeasurePreserving` for translations to deduce (b), and finally apply `MeasurePreserving.integral_comp` for (c).  Blocker: without working search/edit tooling I have not located the exact Mathlib names for the translation lemmas nor written `Main.lean`, so `lake build` has not yet been run.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**
When the missing lemmas are located, the Lean proof will match the prose step-for-step; no additional ideas are needed beyond those already documented in Stages 1 and 2.
