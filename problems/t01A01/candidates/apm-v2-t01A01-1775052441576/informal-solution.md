# Informal Solution: t01A01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

*Why it is hard.*  Two traps recur.  First, many students try to lift everything to \(S^2\) and forget that antipodal equivalence kills all orientation arguments; that route quickly becomes complicated.  Second, even after noting that \(f\) misses a point, it is easy to overlook what \(\mathbb{RP}^2 \setminus \{pt\}\) looks like—without recognizing the Möbius-band deformation retract onto \(S^1\), you cannot compute the induced map on \(\pi_1\) or invoke classification of maps into \(S^1\).

*Key insight.*  Remove a missed point \(y\) from the codomain.  The complement deformation retracts onto a circle, so \(f\) factors (up to homotopy) through \(S^1\).  Because \(\pi_1(\mathbb{RP}^2)\cong \mathbb{Z}/2\) and \(\pi_1(S^1)\cong \mathbb{Z}\), every group homomorphism between them is trivial.  This forces both \(f_*\) and the homotopy class of \(f\) to be trivial when viewed inside the circle, and the retraction/inclusion pair carries that null-homotopy back to the original target.

*Complete proof.*

1. Since \(f\) is not surjective, choose \(y\in \mathbb{RP}^2\) not in the image.  Regard \(f\) as a map \(h : \mathbb{RP}^2 \to \mathbb{RP}^2 \setminus \{y\}\).
2. The hint recalls that \(\mathbb{RP}^2 \setminus \{y\}\) is a Möbius band that deformation retracts onto its core circle.  Let \(r : \mathbb{RP}^2 \setminus \{y\} \to S^1\) be such a retraction and \(s : S^1 \hookrightarrow \mathbb{RP}^2 \setminus \{y\}\) the inclusion of the core.  Then \(r \circ s = \mathrm{id}_{S^1}\) and \(s \circ r \simeq \mathrm{id}_{\mathbb{RP}^2 \setminus \{y\}}\).
3. Compose to get \(g = r \circ h : \mathbb{RP}^2 \to S^1\).  On fundamental groups we have
   \[
   g_* = r_* \circ h_* : \pi_1(\mathbb{RP}^2) \longrightarrow \pi_1(S^1) \cong \mathbb{Z}.
   \]
   Because \(\pi_1(\mathbb{RP}^2)\cong \mathbb{Z}/2\) is torsion and \(\mathbb{Z}\) is torsion-free, every homomorphism \(\mathbb{Z}/2 \to \mathbb{Z}\) is the zero map.  Hence \(g_* = 0\).  Since \(r_*\) is an isomorphism (deformation retracts induce isomorphisms on \(\pi_1\)), it follows that \(h_* = 0\).  The inclusion \(ι : \mathbb{RP}^2 \setminus \{y\} \hookrightarrow \mathbb{RP}^2\) satisfies \(f = ι \circ h\), so
   \[
   f_* = ι_* \circ h_* = ι_* \circ 0 = 0,
   \]
   i.e. \(f_*\) has image \(\{1\}\).  This proves the first claim.
4. Because \(S^1\) is a \(K(\mathbb{Z},1)\), homotopy classes of maps \( \mathbb{RP}^2 \to S^1\) are classified by induced maps on \(\pi_1\).  Since \(g_* = 0\), the map \(g\) is homotopic to the constant map at some point \(p \in S^1\).
5. Compose this null-homotopy with \(s\) to get a homotopy between \(h = s \circ g\) and the constant map \(s(p)\) valued in \(\mathbb{RP}^2 \setminus \{y\}\).  Finally, composing with \(ι\) shows \(f = ι \circ h\) is homotopic to the constant map with value \(ι(s(p)) \in \mathbb{RP}^2\).  That completes the second claim.

*Proof sanity check.*  The fragile step is Step 4: “\(S^1\) is a \(K(\mathbb{Z},1)\), so \(g\) is null-homotopic once \(g_* = 0\).”  This follows because \([\mathbb{RP}^2,S^1] \cong \operatorname{Hom}(\pi_1(\mathbb{RP}^2),\mathbb{Z})\); the classification is standard and can be proved via universal covers if needed.  Both subparts are fully established above.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *s1.*  **Dependency.**  Formal target `pi1_map_trivial_and_nullhomotopic_of_non_surjective_RP2` relies on (i) the deformation retract lemma `punctured_RP2_deformation_retracts_to_circle`, (ii) the algebraic fact that every hom \( \mathbb{Z}/2 \to \mathbb{Z}\) is zero, and (iii) the classification of maps into \(S^1\) by \( \pi_1\).  **Why this now.**  This chain mirrors Steps 1–5: once we know the retract, the algebraic statement immediately forces trivial \(f_*\), and the \(K(\mathbb{Z},1)\) property collapses the homotopy classification.  **Lean target/search.**  Intended Lean goal lives at `ApmCanaries.Frames.T01A01...Main`, and Mathlib search terms tried were `"RealProjective"`, `"Moebius"`, and `"Homotopic const S1"`.

**Stage 3 — LEAN FORMALIZATION**

- Ran `rg -n "RealProjective" /home/joe/code/apm-lean` to locate an existing `RealProjectivePlane` topology API.  The search returned no hits, so Mathlib currently lacks (or does not expose) a concrete type or the fundamental-group computation needed for RP².
- Because the target theorem needs (a) a Lean model of \( \mathbb{RP}^2\), (b) a formal identification of its punctured version with a Möbius band (or at least a retract to \(S^1\)), and (c) a classification lemma for maps into \(S^1\), the formal development blocks immediately.  The obstruction is **missing API/theory** rather than last-mile glue; until Mathlib supplies the projective plane type and its homotopy-type lemmas, no honest Lean proof can proceed.
- File status: `Main.lean` stays a stub (see `/home/joe/code/apm-lean/ApmCanaries/Frames/T01A01/Apm_v2_t01A01_1775052441576/Main.lean`).  No sorry-backed declarations were added; further progress requires upstream topology infrastructure.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

*Mode: blocked.*  Stage 1 already phrases the result in terms of deformation retracts and \(K(\mathbb{Z},1)\) classification.  Because Lean lacks `RealProjectivePlane` and the punctured retract lemma, none of those sentences are yet formally certified.  Once Mathlib gains (1) a RP² object, (2) a proof that removing a point retracts to \(S^1\), and (3) the derived \(π_1\)-classification, the Stage 1 proof can be tagged as “matched.”  Until then, both “\(f_*\) has image \(\{1\}\)” and “\(f\) is null-homotopic” remain informal.
