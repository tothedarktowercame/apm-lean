# Informal Solution: m96J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Why it's hard.** Two pitfalls keep appearing. First, the projection theorem is abstract: you know there is a closest point, but it is not obvious that the assignment is linear (projections onto arbitrary closed convex sets are not linear). Second, the analytic properties—norm control, adjoint, idempotence—require using the orthogonal decomposition, not just minimizing sequences. Forgetting to use the decomposition with the orthogonal complement leaves most students chasing epsilons.

**Key insight.** Once you decompose every vector uniquely as `x = v + w` with `v ∈ V` and `w ∈ V⊥`, every property becomes a one-line identity: the projection forgets the `w` component. All four parts are essentially reformulations of this decomposition: linearity follows because the decomposition is linear, the norm bound is the Pythagorean theorem, self-adjointness is just orthogonality of the dropped component, and idempotence is the observation that projecting a vector already in `V` does nothing.

**Complete proof.** Let `H` be a Hilbert space, `V ≤ H` a nonzero closed subspace, and `F : H → V` send `x` to the unique `v ∈ V` with `x - v ∈ V⊥` (Hilbert projection theorem).

*Linearity (part a).* Fix `x₁, x₂` and write `xᵢ = vᵢ + wᵢ` with `vᵢ ∈ V`, `wᵢ ∈ V⊥`. Then `x₁ + x₂ = (v₁ + v₂) + (w₁ + w₂)` with `v₁ + v₂ ∈ V`, `w₁ + w₂ ∈ V⊥`, so the closest point to `x₁ + x₂` is `v₁ + v₂ = F(x₁) + F(x₂)`. The scalar rule is similar: `(αx) = (αv) + (αw)` with `αv ∈ V` and `αw ⟂ V`, hence `F(αx) = αF(x)`.

*Norm one (part b).* From `x = F(x) + (x - F(x))` with orthogonal summands we get `‖x‖² = ‖F(x)‖² + ‖x - F(x)‖² ≥ ‖F(x)‖²`, so `‖F(x)‖ ≤ ‖x‖` and `‖F‖ ≤ 1`. Because `V ≠ {0}` there exists `v ≠ 0` in `V` and `F(v) = v`, hence `‖F‖ ≥ ‖F(v)‖ / ‖v‖ = 1`. Thus the operator norm is exactly `1`.

*Self-adjoint (part c).* For any `x, y` write `x = v₁ + w₁`, `y = v₂ + w₂` as before. Since `w₁ ⟂ V` and `w₂ ⟂ V`, `⟪w₁, v₂⟫ = ⟪v₁, w₂⟫ = 0`. Therefore `⟪F(x), y⟫ = ⟪v₁, v₂ + w₂⟫ = ⟪v₁, v₂⟫ = ⟪v₁ + w₁, v₂⟫ = ⟪x, F(y)⟫`. This symmetry is the definition of self-adjointness.

*Idempotent (part d).* If `v ∈ V` then `F(v) = v` because the closest point is itself. Consequently `F(F(x)) = F(x)` for every `x`, i.e. `F² = F`.

**What connects.** Orthogonal projections are the workhorse for everything from Fourier series to conditional expectations and to numerical linear algebra (least squares). The exact same template—orthogonal decomposition, Pythagorean theorem, adjoint symmetry—reappears whenever you project onto a finite-dimensional space, onto an eigenspace, or onto an `L²` sub-σ-algebra.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Hilbert projection theorem* → defines `F(x)` and gives the orthogonal decomposition used in every step.
- *Orthogonal decomposition linearity* (that `V` and `V⊥` are closed subspaces) → supplies the linearity calculations in part (a).
- *Pythagorean identity* → provides the norm inequality and, coupled with the existence of a nonzero vector in `V`, yields `‖F‖ = 1`.
- *Orthogonality relations* (`w ⟂ V`) → certify the inner-product symmetry needed for self-adjointness.
- *Projection fixes `V`* → immediately implies idempotence.

Lean targets mirror this order: `proj_linear` (Stage `:s2`), `proj_norm_one`, `proj_isSelfAdjoint`, and `proj_idempotent`, all assembled in `projection_properties`.

**Stage 3 — LEAN FORMALIZATION**

Main statements live in `/home/joe/code/apm-lean/ApmCanaries/Frames/M96J01/Apm_v2_m96J01_1775007086632/Main.lean`.
- Defined `proj V := (V : Submodule ℝ H).starProjection` and proved `proj_linear`, `proj_norm_one`, `proj_isSelfAdjoint`, and `proj_idempotent`.
- Bundled them in `projection_properties`, matching the informal claim.
- `lake build` succeeds (warnings only about unrelated files: unused section variables in `ApmCanaries/C2Analysis.lean` and `ApmCanaries/C4Functional.lean`).

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean proof forced an explicit choice of a `ClosedSubmodule`, which is exactly the “closed subspace” in the prose. Translating back just means forgetting the subtype bookkeeping. The norm calculation used Mathlib’s `norm_starProjection`, so in the write-up we highlighted its Pythagorean source. The self-adjoint and idempotent properties in Lean came straight from `isSelfAdjoint_starProjection` and `starProjection_eq_self_iff`; in prose we expanded these into the inner-product computation and the “project twice = project once” observation.
