# Informal Solution: a93J05

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

*Why it’s hard.* Periodicity in one direction never forces constancy—think of \(e^z\) with period \(2\pi i\). The trap is missing that two independent periods tile the whole plane by compact fundamental domains. Unless you explicitly use that tiling to bound \(|f|\), Liouville’s theorem cannot be applied.

*Key insight.* Reduce everything to the unit square \(P = \{x+iy : 0 \le x,y \le 1\}\). Periodicity makes every value of \(f\) a translate of its restriction to \(P\). Because \(P\) is compact and \(f\) is continuous, \(|f|\) attains a maximum on \(P\), so \(f\) is bounded on \(\mathbf{C}\). Liouville then forces \(f\) to be constant.

*Complete proof.* Let \(f : \mathbf{C} \to \mathbf{C}\) be entire and satisfy \(f(z+n+im) = f(z)\) for all integers \(n,m\). For any \(z = x+iy\) pick integers \(n = \lfloor x \rfloor\) and \(m = \lfloor y \rfloor\); then \(w = z - (n+im)\) lies in \(P\). Periodicity gives \(|f(z)| = |f(w)| \le \sup_{u \in P} |f(u)|\). The supremum is finite because \(f\) is continuous and \(P\) is compact. Hence \(f\) is bounded on all of \(\mathbf{C}\). By Liouville’s theorem any bounded entire function is constant, so \(f\) is constant.

*What connects.* This is the simplest instance of a general principle: a holomorphic map from a compact complex manifold (e.g., the torus \(\mathbf{C}/(\mathbf{Z}+\tau\mathbf{Z})\)) to \(\mathbf{C}\) is constant. The same “bound on a fundamental domain plus Liouville” trick shows that any entire function having two linearly independent periods must be constant—only meromorphic doubly periodic functions (elliptic functions) escape.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Fundamental domain reduction.* Observes that every \(z\) is congruent to some \(w\in P\). Needs floor functions and lattice translations. Lean target: `periodic_entire_bounded`.
- *Compactness implies boundedness.* Uses continuity of \(f\) on \(P\) and Heine–Borel. Search terms: `IsCompact`, `ContinuousOn.norm_le`. Same Lean target as above.
- *Liouville’s theorem.* Once boundedness is established, apply Mathlib’s Liouville lemma to deduce constancy. Lean target: `doubly_periodic_entire_constant`.

**Stage 3 — LEAN FORMALIZATION**

Implementation plan: define `fundamentalDomain = {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1}`; prove every point differs from one in the domain by an element of `ℤ + I⋅ℤ` using `Real.floor`. Show `fundamentalDomain` is compact, so `‖f z‖` is uniformly bounded there. Periodicity transports that bound everywhere. Finally invoke `Complex.bound_of_continuousPeriodic` + Liouville (`Complex.isometry_subsingleton_of_isBounded`). All Lean work remains to be written in `Main.lean`, but no additional lemmas beyond these standard facts seem missing.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

After the Lean proof is in place, mirror the exact statements of the helper lemmas (compactness of the rectangle, Liouville) in the prose and note any reliance on floor functions for the lattice reduction so the write-up matches the formal certificate.
