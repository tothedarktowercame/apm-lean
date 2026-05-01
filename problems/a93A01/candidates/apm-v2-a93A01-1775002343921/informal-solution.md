# Informal Solution: a93A01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

***Why it’s hard.***  Condition (b) looks strange: it does not bound the usual difference quotient uniformly; instead it says “whenever the slope gets outrageously large, the actual increment must be tiny.” The trap is to think (b) is stronger than uniform continuity—it isn’t. You need to read it contrapositive: if two function values stay ε apart, the slope cannot blow up. That viewpoint makes the equivalence transparent.

***Key insight.***  Work with the contrapositive of (b): for each ε>0 there is N such that |f(x)-f(y)| ≥ ε forces |(f(x)-f(y))/(x-y)| ≤ N. Uniform continuity on a bounded domain implies (i) there exists δ so that |x-y|<δ ⇒ |f(x)-f(y)|<ε, and (ii) f is bounded, hence |f(x)-f(y)| ≤ 2M for some M. So when |f(x)-f(y)| ≥ ε, we have |x-y| ≥ δ, and therefore the difference quotient is ≤ 2M/δ. The other direction is proved by contrapositive: if f is not uniformly continuous there exist xₙ,yₙ with |xₙ-yₙ|→0 but |f(xₙ)-f(yₙ)| ≥ ε₀, so the quotients tend to ∞ and (b) fails.

***Complete proof.***
- *(a) ⇒ (b).*  Fix ε>0. Uniform continuity gives δ>0 with |x-y|<δ ⇒ |f(x)-f(y)|<ε. Since (0,1) is bounded and f is uniformly continuous, f is bounded: pick M>0 with |f(x)|≤M for all x. For |f(x)-f(y)|≥ε we must have |x-y|≥δ (contrapositive of uniform continuity), hence
  \[\frac{|f(x)-f(y)|}{|x-y|} ≤ \frac{2M}{δ} =: N.\]
  Taking contrapositive, |(f(x)-f(y))/(x-y)|>N forces |f(x)-f(y)|<ε.
- *(b) ⇒ (a).*  Suppose (a) fails. Then there exist ε₀>0 and sequences xₙ,yₙ∈(0,1) with |xₙ-yₙ|→0 but |f(xₙ)-f(yₙ)|≥ε₀. Then
  \[\left|\frac{f(xₙ)-f(yₙ)}{xₙ-yₙ}\right| ≥ \frac{ε₀}{|xₙ-yₙ|} → ∞.\]
  For ε=ε₀, property (b) provides an N; choose n so large that the quotient exceeds N while |f(xₙ)-f(yₙ)|≥ε₀, contradicting (b). Thus f must be uniformly continuous.

***What connects.***  This repackages the usual “uniform continuity prevents arbitrarily steep slopes on bounded domains” idea. The contrapositive construction is the same one used in the Heine–Cantor theorem (compactness) and in the Riesz sequential criterion for uniform continuity.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Uniform continuity ⇒ boundedness on bounded domains.*  Needed to control |f(x)-f(y)| by a global constant 2M.
- *Contrapositive of uniform continuity.*  |f(x)-f(y)|≥ε implies |x-y|≥δ.
- *Sequential characterization of non-uniform continuity.*  Used to prove (b)⇒(a).

**Stage 3 — LEAN FORMALIZATION**

- *Target.*  `uniformContinuous_iff_largeDiffQuot_smallIncrement` (see `formal-alignment.edn`).
- *Status — blocked.*  Mathlib lacks the “sequential characterization of failure of uniform continuity” needed for the (b)⇒(a) direction. A repository search (`rg -n "not_uniformContinuous" -g"*.lean"`) returned no hits. Without a lemma supplying the sequences xₙ,yₙ promised by the analysis proof, the contrapositive argument cannot yet be formalized. Filling the gap would require adding a result of the form `¬UniformContinuous f ↔ ∃ ε>0, ∀ δ>0, ∃ x y, |x-y|<δ ∧ |f x - f y| ≥ ε`, after which the Lean proof could proceed as above.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the sequential lemma exists, the Lean development will mirror Stage 1: derive boundedness and δ from uniform continuity for (a)⇒(b), and use the sequences to contradict (b) when uniform continuity fails.
