# t98A06 closure blueprint

Reviewed source: `holes/labs/blueprints/t98A06/BLUEPRINT.md` (2026-10-13).
The registered statement is true and needs no repair.  This construction does
not change the definitions or theorem type pinned by the statement registry.

## Fixed representations

Let `E n := EuclideanSpace ℝ (Fin n)`.  `SmoothVectorField v` means that the
section `x ↦ (v x : TangentBundle (𝓡 n) X)` is smooth.  `HasLocalSmoothLift
f v` records a neighborhoodwise smooth tangent section `w` satisfying
`mfderiv f x (w x) = v (f x)`; `HasSmoothLift f v` records the corresponding
global section.  The circle target fibers use the induced regular-fiber
atlases from `ManifoldTargetRegularFiberGlobalAtlas`, literally at `1` and
`minusOne`.

## Nodes

### B1 — closure definitions

Copy `E`, `SmoothVectorField`, `minusOne`, `FiberModel`,
`HasLocalSmoothLift`, and `HasSmoothLift` from the reviewed Lean blueprint.
These are representation declarations, not mathematical assumptions.

### B2 — `t98A06_local_smooth_submersion_lift` (LIBRARY)

For a smooth submersion `f : X → Y` and smooth target vector field `v`, prove
`HasLocalSmoothLift f v`.  At `x₀`, choose a complement of the kernel of
`mfderiv f x₀`.  In tangent-bundle charts, restrict the varying derivative to
that fixed complement.  It is invertible at `x₀`; after shrinking it remains
invertible, and smooth matrix inversion gives a smooth local right inverse.
Transporting this inverse back through the tangent charts and applying it to
`v (f x)` supplies the local lift.

Do not replace this with pointwise choices.  The required conclusion includes
smooth dependence on `x`.  The closest existing pointwise API is
`ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional`.

Dependencies: B1.  Expected size: 250–500 lines.

### B3 — `t98A06_global_vectorField_lift`

Assuming B2's conclusion as a hypothesis, define the affine fibers
`{u | mfderiv f x u = v (f x)}`.  Prove they are convex, feed the B2 local
sections to `exists_contMDiffSection_forall_mem_convex_of_local`, and obtain
`HasSmoothLift f v`.  This proof is already present in the reviewed Lean
blueprint and must be copied rather than re-derived.

Dependencies: B1 and the B2 interface.  Expected size: 60–120 lines.

### B4 — `t98A06_compact_circle_fibers_diffeomorphic` (LIBRARY)

Assuming the global lifting theorem, lift the unit angular vector field on
`Circle`.  Construct the complete smooth flow of the resulting vector field
on compact boundaryless `X`, including smooth dependence on time and initial
condition.  Uniqueness of integral curves must identify its projection under
`f` with circle rotation.  Restrict time `π` and time `-π` to the fibers over
`1` and `minusOne`; prove they are smooth inverses for the induced regular
fiber atlases and package them as the required `Diffeomorph`.

Do not postulate completeness or the fiber equivalence.  Mathlib has local
integral-curve existence and uniqueness, but the compact uniform-time smooth
flow package is part of this node.

Dependencies: B1 and the B3 interface.  Expected size: 1200–3000 lines plus
the 180–350 line fiber restriction adapter.

### B5 — final assembly

Copy the registered theorem and its proof from the reviewed Lean blueprint:
instantiate B3 with B2, then pair that lift theorem with B4.  The resulting
`apm_t98a06` must be placeholder-free and have exactly the registered type.

Dependencies: B2, B3, B4.

## Milestone order and gates

B1 and B3 are copied first.  B2 and B4 are independent library programs once
their stated interfaces exist.  B5 is attempted immediately after both are
banked.  Every milestone must compile without `sorry` and use only standard
axioms.  Final gates:

```text
lake env lean ConstructionTargets/t98A06Closure.lean
lake env lean problems/t98A06/lean/Main.lean
python3 scripts/statement-registry.py check
```
