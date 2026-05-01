# Informal Solution: a96J06

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.* The conclusion feels geometric (“the polynomial must stretch every disk”), so it’s tempting to chase inequalities on coefficients. The right tool is analytic: normalize the disk to the unit disk and apply Schwarz’s lemma. Students often forget to rescale, so they can’t bring Schwarz to bear.

*Key insight.* Assume towards contradiction that some disk is mapped inside itself: 
\(|p(z)|≤r\) for all \\(|z|<r\\). After the change of variables \\(q(w)=p(r w)/r\\), we get a holomorphic self-map of the unit disk fixing 0 with derivative 1 at 0. Schwarz’s lemma then forces \\(q(w)=e^{iθ}w\\). But the polynomial has a nonzero higher-order term, contradicting the conclusion of Schwarz’s lemma. Thus every disk must contain a point expanded beyond its radius.

*Complete proof.* Suppose there is an \\(r>0\\) with \\(|p(z)|≤r\\) whenever \\(|z|≤r\\). Define
\[
q(w)=\frac{p(r w)}{r}= w + \sum_{n=2}^N c_n r^{n-1} w^n.
\]
Then \(q\) is holomorphic on the unit disk, satisfies \(q(0)=0\), and by construction \(|q(w)|≤1\) for \(|w|≤1\). Schwarz’s lemma yields \(|q(w)|≤|w|\) and \(|q'(0)|≤1\). Here \(q'(0)=1\); hence equality holds, so Schwarz’s lemma forces \(q(w)=e^{iθ}w\). Comparing coefficients shows every higher-order coefficient must vanish, contradicting the assumption \(c_N\ne 0\). Therefore our supposition is false, and for every \(r>0\) there exists \(|ζ|<r\) with \(|p(ζ)|>r\).

*What connects.* This is a baby case of the Open Mapping Theorem plus Schwarz’s lemma. It is the analytic version of “a non-linear polynomial cannot be a self-map of a disk fixing the center with derivative 1.” The same trick appears whenever we study automorphisms of the disk or prove rigidity theorems (e.g., for bounded holomorphic functions with fixed points).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Normalization lemma:* rescale the disk to unit size and rewrite \(p\) as \(q(w)=p(rw)/r\). Needed to bring Schwarz’s lemma to the party.
- *Schwarz rigidity:* if a holomorphic self-map of \(\mathbb D\) fixes 0 and has \(|q'(0)|=1\), then it is a rotation. Needed for the contradiction with the nonzero higher coefficient.
- *Contradiction conclusion:* equality of coefficients between \(q\) and the rotation forces \(c_n=0\) for \(n≥2\), contradicting \(c_N\ne0\).

**Stage 3 — LEAN FORMALIZATION**

Plan: (1) implement the normalization lemma in `Main.lean` (scaling the polynomial and the disk). (2) Invoke Mathlib’s Schwarz lemma (`Complex.Analytic.schwarz_sublemma`) to deduce rigidity of `q`. (3) Conclude coefficient vanishing using polynomial extensionality. Stage 3 remains in progress; these lemmas still need to be formalized.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the Lean proof is finished, ensure the written proof cites the precise normalization and Schwarz lemmas used, emphasizing the rigidity argument.
