# Informal Solution: m96J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Why it's hard.** Two pitfalls keep appearing. First, the projection theorem is abstract: you know there is a closest point, but it is not obvious that the assignment is linear (projections onto arbitrary closed convex sets are not linear). Second, the analytic properties—norm control, adjoint, idempotence—require using the orthogonal decomposition, not just minimizing sequences. Forgetting to use the decomposition with the orthogonal complement leaves most students chasing epsilons.

**Key insight.** Once you decompose every vector uniquely as $x = v + w$ with $v \in V$ and $w \in V^{\perp}$, every property becomes a one-line identity: the projection forgets the $w$ component. All four parts are essentially reformulations of this decomposition: linearity follows because the decomposition is linear, the norm bound is the Pythagorean theorem, self-adjointness is just orthogonality of the dropped component, and idempotence is the observation that projecting a vector already in $V$ does nothing.

**Complete proof.** Let $H$ be a Hilbert space, $V \leq H$ a nonzero closed subspace, and $F : H \to V$ send $x$ to the unique $v \in V$ with $x - v \in V^{\perp}$ (Hilbert projection theorem).

*Linearity (part a).* Fix $x_{1}, x_{2}$ and write $x_{i} = v_{i} + w_{i}$ with $v_{i} \in V$, $w_{i} \in V^{\perp}$. Then $x_{1} + x_{2} = (v_{1} + v_{2}) + (w_{1} + w_{2})$ with $v_{1} + v_{2} \in V$, $w_{1} + w_{2} \in V^{\perp}$, so the closest point to $x_{1} + x_{2}$ is $v_{1} + v_{2} = F(x_{1}) + F(x_{2})$. The scalar rule is similar: $(\alpha x) = (\alpha v) + (\alpha w)$ with $\alpha v \in V$ and $\alpha w \perp V$, hence $F(\alpha x) = \alpha F(x)$.

*Norm one (part b).* From $x = F(x) + (x - F(x))$ with orthogonal summands we get $\lVert x\rVert^{2} = \lVert F(x)\rVert^{2} + \lVert x - F(x)\rVert^{2} \geq \lVert F(x)\rVert^{2}$, so $\lVert F(x)\rVert \leq \lVert x\rVert$ and $\lVert F\rVert \leq 1$. Because $V \neq \{0\}$ there exists $v \neq 0$ in $V$ and $F(v) = v$, hence $\lVert F\rVert \geq \lVert F(v)\rVert / \lVert v\rVert = 1$. Thus the operator norm is exactly $1$.

*Self-adjoint (part c).* For any $x, y$ write $x = v_{1} + w_{1}$, $y = v_{2} + w_{2}$ as before. Since $w_{1} \perp V$ and $w_{2} \perp V$, $⟪w_{1}, v_{2}⟫ = ⟪v_{1}, w_{2}⟫ = 0$. Therefore $⟪F(x), y⟫ = ⟪v_{1}, v_{2} + w_{2}⟫ = ⟪v_{1}, v_{2}⟫ = ⟪v_{1} + w_{1}, v_{2}⟫ = ⟪x, F(y)⟫$. This symmetry is the definition of self-adjointness.

*Idempotent (part d).* If $v \in V$ then $F(v) = v$ because the closest point is itself. Consequently $F(F(x)) = F(x)$ for every $x$, i.e. $F^{2} = F$.

**What connects.** Orthogonal projections are the workhorse for everything from Fourier series to conditional expectations and to numerical linear algebra (least squares). The exact same template—orthogonal decomposition, Pythagorean theorem, adjoint symmetry—reappears whenever you project onto a finite-dimensional space, onto an eigenspace, or onto an $L^{2}$ sub-$\sigma$-algebra.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- *Hilbert projection theorem* → defines $F(x)$ and gives the orthogonal decomposition used in every step.
- *Orthogonal decomposition linearity* (that $V$ and $V^{\perp}$ are closed subspaces) → supplies the linearity calculations in part (a).
- *Pythagorean identity* → provides the norm inequality and, coupled with the existence of a nonzero vector in $V$, yields $\lVert F\rVert = 1$.
- *Orthogonality relations* ($w \perp V$) → certify the inner-product symmetry needed for self-adjointness.
- *Projection fixes $V$* → immediately implies idempotence.

Lean targets mirror this order: `proj_linear` (Stage `:s2`), `proj_norm_one`, `proj_isSelfAdjoint`, and `proj_idempotent`, all assembled in `projection_properties`.

**Stage 3 — LEAN FORMALIZATION**

Main statements live in `/home/joe/code/apm-lean/ApmCanaries/Frames/M96J01/Apm_v2_m96J01_1775007086632/Main.lean`.
- Defined `proj V := (V : Submodule ℝ H).starProjection` and proved `proj_linear`, `proj_norm_one`, `proj_isSelfAdjoint`, and `proj_idempotent`.
- Bundled them in `projection_properties`, matching the informal claim.
- `lake build` succeeds (warnings only about unrelated files: unused section variables in `ApmCanaries/C2Analysis.lean` and `ApmCanaries/C4Functional.lean`).

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean proof forced an explicit choice of a `ClosedSubmodule`, which is exactly the “closed subspace” in the prose. Translating back just means forgetting the subtype bookkeeping. The norm calculation used Mathlib’s `norm_starProjection`, so in the write-up we highlighted its Pythagorean source. The self-adjoint and idempotent properties in Lean came straight from `isSelfAdjoint_starProjection` and `starProjection_eq_self_iff`; in prose we expanded these into the inner-product computation and the “project twice = project once” observation.
