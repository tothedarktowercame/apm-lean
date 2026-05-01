# Informal Solution: a01A01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.*  If you try to shrink the support of each \(f_k\) rapidly, particular points quickly stop seeing the spikes; if you keep the supports large, the integrals refuse to go to zero.  The trap is thinking you can concentrate the mass near finitely many locations and still drive the limsup to \(+\infty\) everywhere.  The right construction must simultaneously visit *every* point infinitely often *and* keep the total mass of each spike tiny.

*Key insight.*  Work stage-by-stage.  At stage \(m\) partition \([0,1]\) into the \(2^{m}\) dyadic intervals of length \(2^{-m}\) and place a spike of height \(m+1\) on each interval.  Enumerate all those spikes level-by-level: the integral of any stage-\(m\) spike equals \((m+1)2^{-m}\to 0\), while every point belongs to exactly one dyadic interval at each stage, so it sees spikes of height \(m+1\) for arbitrarily large \(m\).  The \(\mathbb{R}^{n}\) version just replaces dyadic intervals by dyadic cubes.

*Complete proof.*  For \(m\ge0\) let \(I_{m,j}=[j/2^{m},(j+1)/2^{m})\) with \(0\le j<2^{m}\).  Define the sequence by listing the functions
\[
g_{m,j}(x) = (m+1)\mathbf{1}_{I_{m,j}}(x)
\]
in the order \( (m,j) = (0,0), (1,0),(1,1),(2,0),(2,1),(2,2),(2,3),\dots\).  
For each \(k\) the associated level \(m\) is finite, and
\[
\int_{0}^{1} g_{m,j} = (m+1)\cdot |I_{m,j}| = \frac{m+1}{2^{m}},
\]
which tends to \(0\) with \(m\).  Because only finitely many spikes occur at each level and we cycle through the levels in order, the subsequence of integrals indexed by \((m,*)\) tends to zero, so the full sequence \(\int f_k\) tends to zero as \(k\to\infty\).

Fix \(x\in[0,1]\).  For every \(m\) there is exactly one \(j\) with \(x\in I_{m,j}\) (use the binary expansion; if \(x\) is dyadic, pick the unique interval that contains it on the left).  The subsequence \(f_{k(m)} := g_{m,j}\) then satisfies
\[
f_{k(m)}(x) = m+1 \longrightarrow \infty,
\]
so \(\limsup_{k\to\infty} f_{k}(x)=\infty\).  The same tiling argument works in \(\mathbb{R}^{n}\): cover the cube \([0,1]^{n}\) by dyadic cubes of side \(2^{-m}\), put spikes of height \(m+1\) on them, and then translate/scale the construction to cover all of \(\mathbb{R}^{n}\) by disjoint dyadic cubes.  Heights \(m+1\) and volumes \(2^{-mn}\) give integrals \((m+1)2^{-mn}\to0\), while every point lies in a unique dyadic cube at each level, so its limsup is still \(+\infty\).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

*Formal dependency.*  (i) Volume of a dyadic interval/cube is its side length (Lebesgue measure of `Icc`).  (ii) Indicators integrate to “height × volume”.  (iii) Enumerating the \(2^{m}\) cubes of level \(m\) consecutively makes the stage index tend to infinity.  

*Informal dependency.*  The dyadic tiling supplies the “every point sees every level” fact; the integral computation collapses to a one-line calculation once the tiling is fixed; the enumeration ensures the sequence of integrals actually tends to zero.

*Why this order.*  First fix the geometric tiling (without it the proof cannot start), next compute the integrals (so we know the mass goes to zero), and finally argue about limsups pointwise (once you know how the indices are ordered).

*Lean targets.*  Define a recursive helper `stageData : ℕ → ℕ × ℕ` returning the level \(m\) and the position \(j\), prove that `stageData (2^m - 1 + j) = (m, j)` for all `j < 2^m`, show the integral is `(m+1)/2^m`, and show the limsup is `∞` by constructing the subsequence `2^m - 1 + j(x,m)`.  These use only basic facts about powers of two and lengths of intervals.

**Stage 3 — LEAN FORMALIZATION**

`Main.lean` currently imports Mathlib and Scratch but the actual construction is still pending.  The next coding step is to implement `stageData` (level/offset recursion), define the dyadic indicator functions, and prove the integral formula plus the limsup lemma.  No Mathlib gaps are anticipated, but the combinatorial recursion and the real-floor lemma for `j(x,m)` still need to be written.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the recursion and floor lemmas are in place, the Lean development will match the prose proof verbatim: the enumeration guarantees stage growth, the integral computation will read “`intervalIntegral` of a constant over `Icc`”, and the pointwise limsup argument becomes a direct reference to the `j(x,m)` lemma.  Until those helpers are coded, the informal proof above remains the authoritative record.
