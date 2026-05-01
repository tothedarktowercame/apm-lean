# Informal Solution: t95A03

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** “Totally bounded” sounds like “bounded”, so it’s easy to underestimate how powerful the condition is. Students often try to use Heine–Borel (
\(\mathbb R^n\) only) or Arzelà–Ascoli. The real trap is forgetting that compactness in metric spaces is equivalent to sequential compactness: the job is to show every sequence has a convergent subsequence.

**Key insight.** Finite \(\varepsilon\)-nets let you iteratively trap a sequence inside smaller and smaller balls. From any sequence, first pick an \(\varepsilon_1\)–ball (say radius 1) containing infinitely many terms; then a radius \(\tfrac12\) ball within that still containing infinitely many; continue with \(\varepsilon_k=2^{-k}\). Diagonalize to obtain a subsequence whose pairwise distances go to zero, i.e. a Cauchy subsequence. Completeness turns it into a convergent subsequence, hence sequential compactness, hence compactness.

**Proof.** Let \(X\) be totally bounded and complete. To prove compactness it suffices (metric-space fact) to show every sequence \((x_n)\) has a convergent subsequence.

Fix \(\varepsilon_k = 2^{-k}\). Because \(X\) is totally bounded, finitely many \(\varepsilon_1\)-balls cover \(X\); one of them contains infinitely many terms of the sequence—call this ball \(B_1\) and restrict to those indices. Inside \(B_1\) we again use total boundedness to cover \(B_1\) by finitely many \(\varepsilon_2\)-balls; choose \(B_2\subseteq B_1\) containing infinitely many of the remaining terms. Continue inductively, producing nested balls \(B_k\) with radii \(2^{-k}\) each containing infinitely many terms of the sequence.

Choose indices \(n_1<n_2<\dots\) so that \(x_{n_k}\in B_k\). For \(i>j\), \(x_{n_i},x_{n_j}\in B_j\), whose diameter is at most \(2^{-j+1}\). Thus \((x_{n_k})\) is Cauchy. Completeness of \(X\) provides a limit \(x\in X\). Therefore every sequence in \(X\) admits a convergent subsequence; \(X\) is sequentially compact and hence compact.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Totally bounded ⇒ Cauchy subsequence.** (formal: lemma producing nested finite nets). Needed to manufacture the subsequence.
- **Completeness ⇒ Cauchy subsequence converges.** Already built into `CompleteSpace`.
- **Sequential compactness ⇔ compactness (metric).** Bridges the subsequence argument to actual compactness.

Lean hooks: `Metric.complete_of_cauchy`, `isClosedBall`, `TotallyBounded`.  Target lemma: `totallyBounded_iff_seqCompact`. Mathlib status: sequential compactness proofs exist but no single lemma packaging “complete + totally bounded ⇒ CompactSpace”, so additional API needs to be wired.

**Stage 3 — LEAN FORMALIZATION**

`Main.lean` now contains the theorem

```lean
theorem totally_bounded_complete_compact
    (X : Type*) [PseudoMetricSpace X] [CompleteSpace X]
    (h : TotallyBounded (Set.univ : Set X)) : CompactSpace X
```

The proof instantiates Mathlib’s uniform-space lemma
`isCompact_iff_totallyBounded_isComplete` with `s = Set.univ`.  The assumption
`h` supplies the totally bounded hypothesis, while completeness of `X` provides
`complete_univ`.  The resulting `IsCompact univ` is repackaged as a
`CompactSpace X`.  `lake build ApmCanaries.Frames.T95A03.Apm_v2_t95A03_1775011813898.Main`
now succeeds without warnings.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean statement exactly mirrors the informal claim: total boundedness of the
entire space plus completeness yields `CompactSpace X`.  The Stage 1 nested-ball
argument explains why the hypotheses imply sequential compactness; the Lean
proof hides those steps inside `isCompact_iff_totallyBounded_isComplete`.  No
further edits were needed in the prose beyond pointing to those standard lemmas.
