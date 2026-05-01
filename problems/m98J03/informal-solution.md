# Informal Solution: m98J03

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** A projection is such a simple-looking operator that people forget it still lives inside the analytic zoo of spectra, compact sets, adjoints, and invariant subspaces. The trap is to treat each part separately: you can easily show `V_perp` is closed, or that `P` equals its adjoint, but unless you exploit the single geometric picture—“identity on `V`, zero on `V_perp`”—the spectral and compactness claims become opaque.

**Key insight.** Use the orthogonal decomposition `H = V ⊕ V_perp`. In that basis the operator is literally the block matrix `diag(I_V, 0)`. Every claim is obvious from this block form: eigenvalues are `0` or `1`, the operator is compact precisely when the nonzero block acts on a finite-dimensional summand, the orthogonal complement is the other block, commuting operators must be block-diagonal, and the adjoint equals the original block.

**Complete proof.** Let `P : H → H` be the orthogonal projection onto the closed subspace `V` and set `W := V_perp = {x ∈ H : ⟪x,v⟫ = 0 for all v ∈ V}`.

(a) Because `P^2 = P`, it satisfies the polynomial `λ(λ-1)=0`. By the spectral mapping theorem, `σ(P)` is contained in the zeros of that polynomial, i.e. `{0,1}`. If `V = {0}` then `P = 0`, so `σ(P) = {0}`. If `V = H` then `P = I`, so `σ(P) = {1}`. If neither summand is trivial, then `1` is an eigenvalue with eigenvectors `V` and `0` is an eigenvalue with eigenvectors `W`, hence `σ(P) = {0,1}`.

(b) Suppose `P` is compact. The restriction `P|_V` is the identity on `V`, so the image of the unit ball of `V` is the unit ball itself. A compact operator carries bounded sets to relatively compact sets, so the unit ball of `V` is relatively compact, and the Riesz lemma forces `V` to be finite dimensional. Conversely, if `V` is finite dimensional, the range of `P` is finite dimensional, so `P` has finite rank, hence is compact.

(c) `V_perp` is defined as `{x ∈ H : ⟪x,v⟫ = 0 for every v ∈ V}`.

(d) `V_perp` is closed because it is the intersection over `v ∈ V` of the kernels of the continuous functionals `x ↦ ⟪x,v⟫`.

(e) Suppose `A` is bounded and `AP = PA`. For `v ∈ V` we have `v = Pv`, so `P(Av) = APv = Av`, i.e. `Av ∈ V`. For `w ∈ V_perp` we have `Pw = 0`, so `P(Aw) = A(Pw) = 0`, i.e. `Aw ∈ ker P = V_perp`.

(f) Orthogonal projections are self-adjoint, so `P* = P`. Explicitly, for all `x,y`, `⟪Px,y⟫ = ⟪x,Py⟫` because the decompositions `x = v+w`, `y = v'+w'` with `v,v' ∈ V`, `w,w' ∈ V_perp` give `⟪Px,y⟫ = ⟪v,v'⟫ = ⟪x,Py⟫`.

**What connects.** Every piece of Hilbert-space operator theory uses this block decomposition idea: finite rank approximations, conditional expectations, spectral projections in quantum mechanics, and even the theory of invariant subspaces all lean on “identity on one summand, zero on the other.” Once you can see the operator as a block matrix, the algebraic/analytic properties become transparent.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- `:s1` (orthogonal decomposition facts) → used for parts (c) and (d) and for the foundational equalities `P^2 = P = P*`.
- `:s2` (spectral/compactness lemmas) → combines the polynomial relation for projections with finite-rank criteria to handle (a) and (b).
- `:s3` (commutation + adjoint) → uses the same block decomposition to show invariance (e) and the adjoint description (f).

**Stage 3 — LEAN FORMALIZATION**

Implemented in `/home/joe/code/apm-lean/ApmCanaries/Frames/M98J03/Apm_v2_m98J03_1775007499607/Main.lean`:
- `ProjectionFacts.orthogonal_isClosed` (part (d)).
- `ProjectionFacts.commute_preserves` (part (e)).
- `ProjectionFacts.adjoint_eq` (part (f)).
- Helper lemmas `starProjection_maps_onto` and `starProjection_kills_perp` encapsulate the block-view of `P`.

`spectrum`/compactness statements (parts (a) and (b)) are still pending in Lean because mathlib lacks ready-made lemmas for the spectrum of an idempotent (we would need either a spectral-mapping API for real Banach spaces or a block-diagonalization lemma). The informal argument above remains authoritative. `lake build` succeeds; existing warnings come only from unrelated files (`ApmCanaries/C2Analysis.lean`, `ApmCanaries/C4Functional.lean`).

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean development forced me to articulate two basic facts explicitly: (1) membership in `V` is equivalent to `P x = x`, and membership in `V_perp` is equivalent to `P x = 0`; (2) the commuting relation `AP = PA` rewrites to `P (A x) = A (P x)` on every vector. Those identities make the informal proof cleaner: instead of general block-matrix arguments, one can simply rewrite with these identities. The spectral and compactness parts remain informal for now because the necessary mathlib spectral tools are still missing.
