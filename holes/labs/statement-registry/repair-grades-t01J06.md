# Repair grade: t01J06 (2026-11-01)

Outside grade by a read-only Claude subagent (dispatched by claude-14, given the printed problem and the Lean, not the proof), of holes/labs/blueprints/t01J06/Blueprint.lean against problems/t01J06/problem.tex.

Defect in the registered statement: `apm_t01J06_sphereIntegral` used raw `μH[2]`, which on Euclidean space is 4/π times area (isodiametric inequality), so the true value of the integral was 16/3, not the claimed 4π/3. The statement was false. Repair: `μHE[2]`, as t02A05 does. The one-token change is in the definition; no other part of the statement changed.

Grade: faithful.
- Parts (a), (b), (c) all appear with answers: value 4π/3; no smooth closed η restricting to i*ω; existence for every p.
- `μHE[2]` is the printed surface integral; unit-sphere mass 4π is proved. Coefficient is the flux of (0,0,z+3) through the outward normal, (z+3)z, and ∫z² + 3∫z = 4π/3, agreeing with Stokes on the ball. Outward orientation is implicit in the printed problem.
- Nothing vacuous: hypotheses only pin down ω and α; (c) requires an open W ⊇ S²×S¹, C^∞ on W, closed on W.
- Scope: no restriction or strengthening. "Why is i*ω closed?" is not stated, the same remaining note as in repair-grades-2.md; it is trivial for a 3-form on a 2-manifold.

The grader did not compile. claude-14's compile of the blueprint: 0 errors, 0 sorry, `apm_t01j06` depends on [propext, Classical.choice, Quot.sound].
