# Informal Solution: t01A01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

*Why it is hard.*  The fundamental group of \(\mathbb{RP}^2\) is tiny, yet the problem deliberately removes all surjectivity assumptions—no covering-space lifting tricks apply directly.  The trap is failing to exploit the hint: removing one point converts \(\mathbb{RP}^2\) into a Möbius band, whose homotopy type is \(S^1\).  Without this observation you cannot control \(f_*\) or the homotopy class of \(f\).

*Key insight.*  Pick a point \(y\) not in the image of \(f\).  The inclusion \(\iota:\mathbb{RP}^2 \setminus \{y\} \hookrightarrow \mathbb{RP}^2\) admits a deformation retraction \(r\) onto the core circle of the Möbius band.  The composite \(g = r \circ f\) lands in \(S^1\), so \(f_*\) factors through
\[
  \pi_1(\mathbb{RP}^2) \cong \mathbf Z/2 \xrightarrow{g_*} \pi_1(S^1) \cong \mathbf Z \xrightarrow{\iota_*} \pi_1(\mathbb{RP}^2).
\]
Since no nontrivial homomorphism \(\mathbf Z/2 \to \mathbf Z\) exists, the whole composition is zero.

*Complete proof.*

1. **Triviality of \(f_*\).**  As above, choose \(y \notin \operatorname{im}(f)\) and write \(h:\mathbb{RP}^2\setminus\{y\}\to S^1\) for a deformation retraction.  Define \(g = h \circ f\); then \(g_* : \pi_1(\mathbb{RP}^2)\to \pi_1(S^1)\) is the zero homomorphism because \(\pi_1(\mathbb{RP}^2)=\mathbf Z/2\) and \(\pi_1(S^1)=\mathbf Z\).  The induced map \(f_* = \iota_* \circ g_*\) therefore has image \(\{1\}\).
2. **Null-homotopy of \(f\).**  The circle \(S^1\) is a \(K(\mathbf Z,1)\), so homotopy classes \([\mathbb{RP}^2,S^1]\) correspond to group homomorphisms \(\pi_1(\mathbb{RP}^2)\to \mathbf Z\).  Since \(g_*=0\), the map \(g\) is homotopic to the constant map at some point \(q\in S^1\).  Composing that homotopy with the inclusion \(S^1 \hookrightarrow \mathbb{RP}^2\setminus\{y\} \hookrightarrow \mathbb{RP}^2\) shows \(f\) is homotopic to the constant map with value \(\iota(q)\).

*Proof sanity check.*  The fragile step is the homotopy classification \( [\mathbb{RP}^2,S^1] \cong \operatorname{Hom}(\pi_1(\mathbb{RP}^2),\mathbf Z)\), which holds because \(S^1\) is a \(K(\mathbf Z,1)\).  Both subparts (trivial \(f_*\) and null-homotopy) are fully proved.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *s1 (`RP2_non_surjective_trivial_pi1`).*  One pipeline: puncture the codomain, retract onto \(S^1\), note that \(\mathbf Z/2 \to \mathbf Z\) must be zero, and use \(K(\mathbf Z,1)\) classification for the null-homotopy.

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/t01A01/apm-v2-t01A01-1775070410894/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/t01A01/apm-v2-t01A01-1775070410894/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

- Ran `rg -n "RealProjective" /home/joe/code/apm-lean` to look for an existing `RP2` topology API; the search returned no matches, so Mathlib currently lacks a model of \(\mathbb{RP}^2\), let alone the Möbius-band retract or its \(\pi_1\) computation.
- To record this obstacle inside the Lean repo, `Main.lean` now contains the placeholder declaration `theorem searched_for_realProjective_api : True := trivial`.
- Without the missing building blocks, the intended Lean theorem `RP2_non_surjective_trivial_pi1` cannot be stated, much less proved.  The formal route is therefore **blocked by missing API/theory**.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

*Mode: blocked.*  Stage 1 proves both conclusions informally, but Lean has no `RealProjectivePlane` object or punctured retract facts, so neither “\(f_* = 0\)” nor “\(f\) is null-homotopic” can be certified yet.
