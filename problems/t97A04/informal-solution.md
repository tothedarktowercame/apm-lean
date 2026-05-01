# Informal Solution: t97A04

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** A linear self-map of the torus hides three flavors of invariants (degree, homology action, and Lefschetz number). The trap is to mix up the covering map L on ℝ² with the induced map \(\bar L\) on T² or to forget that the degree is the determinant of the underlying integer matrix.

**Key insight.** Everything is encoded in the integer matrix of L. Its determinant gives the degree and the action on H₂, the matrix itself is the action on H₁, and Lefschetz’ formula \(L(f)=∑(-1)^i \operatorname{tr}(f_*|H_i)\) combines the traces.

**Complete proof.**
Let A be the matrix of L in the standard basis:
\[A = \begin{pmatrix}2 & 1\\ -1 & 1\end{pmatrix}.\]
(a) The degree of \(\bar L\) equals det A because L is a covering map of degree det A on the universal cover and respects the lattice. Thus \(\deg \bar L = \det A = 2·1 - (−1·1) = 3\).

(b) H₁(T²;ℤ) ≅ ℤ² with basis given by the loops \\[α]=(1,0) and \\[β]=(0,1). The induced map is exactly multiplication by A on this lattice: \\[α]↦2[α]-[β] and \\[β]↦[α]+[β]. Therefore
\[
(\bar L)_*|_{H₁} = \begin{pmatrix}2 & 1\\ -1 & 1\end{pmatrix}.
\]

(c) Lefschetz number:
- H₀(T²;ℤ) ≅ ℤ and \(\bar L_*\) acts as identity, so \(\operatorname{tr}(H₀)=1\).
- H₁ contribution is the trace of A, i.e. 2+1=3.
- H₂(T²;ℤ) ≅ ℤ and \(\bar L_*\) multiplies by the degree (3), so \(\operatorname{tr}(H₂)=3\).
Hence
\[
L(\bar L) = \operatorname{tr}(H₀) - \operatorname{tr}(H₁) + \operatorname{tr}(H₂) = 1 - 3 + 3 = 1.
\]

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Degree = det.** A ℤ-linear map on ℝ² inducing a torus map has degree det A.
- **Homology basis identification.** Using standard generators of π₁/H₁ turns the induced map into matrix multiplication.
- **Lefschetz formula.** Expresses the Lefschetz number as the alternating sum of traces on H₀,H₁,H₂.

**Stage 3 — LEAN FORMALIZATION**

Mathlib can handle integer matrices and their determinants, but it currently lacks a packaged Lefschetz-number API for torus self-maps. Formalizing this exercise would require (i) constructing the torus as a K(ℤ²,1) with explicit homology generators, (ii) proving that a linear map with integer matrix acts on homology via that matrix, and (iii) defining the Lefschetz number. These components are nontrivial and mostly absent. Consequently `/home/joe/code/apm-lean/ApmCanaries/Frames/T97A04/Apm_v2_t97A04_1775012771698/Main.lean` only contains a TODO comment, and `lake build …Main` succeeds trivially.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the missing APIs exist, the Lean proof would mirror Stage 1: represent \(\bar L\) by the matrix A, use its determinant for the degree/H₂ action, identify the H₁ action with A, and apply the Lefschetz trace formula to obtain 1.
