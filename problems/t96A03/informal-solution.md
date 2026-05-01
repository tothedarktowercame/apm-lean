# Informal Solution: t96A03

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** Two spheres glued along an equator are no longer a wedge: the intersection is one-dimensional, so you can’t just add the spheres’ homology. The usual trap is ignoring the Mayer–Vietoris boundary map from `H₂(X)` to `H₁(S¹)`—without understanding that map one guesses the wrong rank for `H₂(X)` or incorrectly thinks the equator survives in `H₁`.

**Key insight.** Cover X by the two spheres and run the Mayer–Vietoris exact sequence. Only a few homology groups of the pieces are nonzero, so the long exact sequence collapses to two short fragments. The upper fragment shows `H₁(X)` injects into `H₀(S¹)` and hence vanishes, while the lower fragment shows `H₂(X)` fits into `0→ℤ²→H₂(X)→ℤ→0`. A χ(X)=4 computation (inclusion–exclusion) forces `H₂(X)≅ℤ³`.

**Complete proof.** Let A and B be the two spheres inside X; A∩B is the equator S¹. The Mayer–Vietoris sequence gives
\[
0\to H_2(A)\oplus H_2(B) \to H_2(X) \xrightarrow{\partial} H_1(S^1) \to H_1(A)\oplus H_1(B)=0,
\]
so we obtain `0→ℤ²→H₂(X)→ℤ→0`. The next fragment is
\[
0→H_1(X)→H_0(S^1)\xrightarrow{(i_*,-j_*)} H_0(A)\oplus H_0(B)→H_0(X)→0,
\]
and the map `(i_*,-j_*)` sends the generator to `(1,-1)`, hence is injective; therefore `H₁(X)=0`. The short exact sequence above splits because ℤ is free, so `H₂(X)` is torsion-free. χ(X)=χ(A)+χ(B)−χ(S¹)=4, and since all other reduced homology groups vanish we must have rank `H₂(X)=3`. Altogether, `H₀(X)≅ℤ`, `H₁(X)=0`, `H₂(X)≅ℤ³`, and the higher groups vanish.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Mayer–Vietoris for homology.** Provides the exact sequences relating `H₂(A)⊕H₂(B)`, `H₂(X)`, and `H₁(S¹)` and determines that `H₁(X)=0`.
- **Homology of spheres/circles.** Supplies the known values that feed into Mayer–Vietoris.
- **Euler characteristic additivity.** χ(X)=4 pins down the free rank of `H₂(X)` once we know it is torsion-free.
- **Surjectivity of the “sum” boundary map.** On the cellular chain level, the equator receives four 2-cells whose boundaries sum; proving this map is surjective forces `H₁(X)=0` in the cellular complex and matches the Mayer–Vietoris picture.

**Stage 3 — LEAN FORMALIZATION**

Mathlib still lacks a Mayer–Vietoris package for singular homology, so I focused on the cellular boundary map. In `/home/joe/code/apm-lean/ApmCanaries/Frames/T96A03/Apm_v2_t96A03_1775012050983/Main.lean` I defined the linear map that sends `(a₀,a₁,a₂,a₃)∈ℤ⁴` to the sum `a₀+a₁+a₂+a₃` and proved it is surjective (`sumLinearMap_surjective`, built with `lake build`). This is exactly the algebraic statement that the four hemispherical 2-cells span the equator’s 1-chain. To finish the formalization one would (i) set up the cellular chain complex of X, (ii) identify its ∂₂ with this sum map, and (iii) connect the cellular homology to the singular homology of the glued space.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean lemma justifies the Mayer–Vietoris observation that the boundary map onto `H₁(S¹)` is onto, which is the key input for killing `H₁(X)` and building the short exact sequence for `H₂(X)`. Once the outstanding Mathlib infrastructure (cellular/singular comparison plus a formal treatment of the pushout space) is available, the existing algebraic lemma will slot into the full computation.
