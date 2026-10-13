# t96A08 smoothness-order repair: outside grade (2026-10-13)

Repair cdf59992b: every `(⊤ : WithTop ℕ∞)` (= ω, analytic) in the statement became `((⊤ : ℕ∞) : WithTop ℕ∞)` (= ∞, smooth).
Found by lemma-4 while proving `contDiffOn_of_hasFDerivWithinAt`.

Grader (read-only Claude subagent, claude-14 2026-10-13): **faithful**.
- Manifold: IsManifold I ∞ M with a boundaryless model = smooth manifold (general complete E only generalises).
- 1-form: smoothness of v ↦ ω v.1 v.2 on the tangent bundle = smooth section of the cotangent bundle.
- Paths: continuous, C^∞ on each closed piece of a finite subdivision of [0,1] (standard); mfderiv off the cut points only, integral unaffected.
- Path independence and conclusion (f = line integral, f smooth, mfderiv f = ω) match (a) and (b); problem.md's "f : M → M" is a typo for M → ℝ.
- Minor: hreachable (M path-connected) is needed for (a) anyway; does not carry the core.
Old statement: narrower (analytic category only).
