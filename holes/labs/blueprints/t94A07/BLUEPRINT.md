# Blueprint for t94A07

## Triage

Verdict: **true and faithful**.  The registered Lean statement uses the
standard torus of revolution with `0 < r < R`, the actual ambient half-turn
`(x,y,z) ↦ (x,-y,-z)`, and the kernel of the derivative of the actual defining
equation as its tangent plane.  Its four displayed points, nondegenerate local
indices, cardinality, and non-homotopy conclusion agree with `problem.md`.

I first checked the dangerous degeneracies.  The hypotheses imply
`R-r > 0`, so all four axis points are distinct and none lies on the singular
axis of `sqrt (x²+y²)`.  Thus the derivative used in the tangent definition
exists at every relevant point.  The endpoint `R=r`, where two displayed
points collide at the origin and the square-root constraint ceases to be
smooth there, is correctly excluded.  Likewise `r=0` is excluded.  On the
fixed axis the equation is `(|x|-R)²=r²`, giving exactly
`x=±(R+r), ±(R-r)`.

The solve-loop had already compiled the fixed-axis equation, enumeration,
injectivity, and cardinality arguments; these are reused with proofs.  The
topology audit and `~/notes/closer/t94a07-report.md` identify exactly the two
remaining independent branches: the local derivative/kernel calculation and
the global longitude-degree obstruction.  The sorry-free module
`ConstructionTargets.EuclideanThreeHalfTurnDerivative` is imported and its
banked derivative theorem is used by the local assembly seat.

## Remaining lemmas

### `apm_t94a07_tangent_fixedPoints_eq_span`

**Statement.** At every displayed fixed point, the kernel of the derivative
of the torus constraint is the span of the two `y,z` coordinate vectors.

**Why true.** Expand membership in `fixedPoints` into four cases.  At an axis
point `(x,0,0)` with `x ≠ 0`, differentiate

`(sqrt(x²+y²)-R)² + z²-r²`.

The derivative of `sqrt(x²+y²)` is `sign(x) dx`; at each displayed point the
coefficient of `dx` in the full derivative is nonzero because `r>0`.
Consequently its kernel is exactly `dx=0`.  Show this is the span of
`single 1 1` and `single 2 1` by coordinate extensionality.  Relevant Mathlib
ingredients are `HasFDerivAt.sqrt`, `HasFDerivAt.pow`, sum/composition rules,
`HasFDerivAt.fderiv`, `LinearMap.mem_ker`, and the finite-dimensional span API.

**Expected size.** 100–150 lines.  This is the derivative and kernel worklist
nodes combined because exposing a large explicit continuous-linear-map formula
would add an unstable API boundary used nowhere else.

**Dependencies.** Definitions only.

**Truth check.** For all four points, direct calculus gives a derivative
proportional to `dx`: the proportionality factor has absolute value `2r`, so
it is nonzero.  Vectors in the claimed span have zero first coordinate, and
any vector with zero first coordinate is its `y,z` coordinate expansion.

### `apm_t94a07_local_fixed_point_packet`

**Statement.** Given the preceding tangent-plane equality as a hypothesis,
all four points are Lefschetz fixed points, the half-turn derivative sends
both tangent basis vectors to their negatives, the local matrix determinant
is `4`, and every local Lefschetz number is `1`.

**Why true.** Rewrite the tangent plane with the supplied hypothesis.  The
imported theorem
`ConstructionTargets.EuclideanThreeHalfTurnDerivative.fderiv_halfTurn_single_succ`
gives `Df(e_i)=-e_i`.  Hence the two-by-two local matrix is `2I`, whose
determinant is `4`.  Its sign definition reduces to `1`.  A fixed tangent
vector satisfies `-v=v`, hence `v=0`; fixed-point membership follows from the
already proved `apm_t94a07_fixedSet_eq` (or by the four explicit cases).

**Expected size.** 40–80 lines.

**Dependencies.** Takes the exact conclusion of
`apm_t94a07_tangent_fixedPoints_eq_span` as a hypothesis, so this seat can run
in parallel.  It also depends on the imported, sorry-free half-turn derivative
module.

**Truth check.** Hand computation gives `I-(-I)=2I`, determinant `4>0`, and
therefore local index `+1`.  Over `ℝ`, `-v=v` implies `2v=0`, hence `v=0`.

### `apm_t94a07_halfTurn_not_homotopic` — LIBRARY

**Statement.** No continuous ambient homotopy preserving this concrete torus
connects its half-turn to the identity.

**Why true.** Use the outer equator
`u ↦ ((R+r)u₁,(R+r)u₂,0)` and normalize the `xy` projection of every torus
point to the unit circle.  The projection is defined because the torus
equation and `R>r` force `sqrt(x²+y²) ≥ R-r > 0`.  Composing a hypothetical
torus-preserving homotopy with these maps produces a circle homotopy from
complex conjugation/reflection to the identity.  Their degrees are `-1` and
`1`, contradiction.  Equivalently, use the induced map on `π₁(S¹) ≅ ℤ`.

**Expected size.** 180–300 lines.  This is marked LIBRARY rather than split
into artificial small claims: the missing content is one coherent circle
degree/homotopy invariant construction.  It is exactly the global node of
`program-2026-10-11-close-t94a07`, whose intended implementation target is
`ConstructionTargets/t94A07Closure.lean`.  The current closest sorry-free
construction target is `EuclideanThreeHalfTurnDerivative`, but it only covers
the local derivative branch; no existing target packages this degree
obstruction.

**Dependencies.** Definitions only; independent of both local lemmas.

**Truth check.** On the outer equator the half-turn sends
`(cos θ,sin θ,0)` to `(cos θ,-sin θ,0)`, i.e. degree `-1`, while the identity
has degree `+1`.  At the potentially dangerous inner radius, the lower bound
on the xy norm is `R-r>0`, so normalized projection never divides by zero.

## Assembly

The main theorem has no `sorry`.  It combines the already compiled fixed-set
equality and cardinality with the local packet and the global obstruction.
Its type is copied verbatim from `problems/t94A07/lean/Main.lean`.

## Dependency layers

* **Layer 1 (parallel):**
  `apm_t94a07_tangent_fixedPoints_eq_span` and the LIBRARY lemma
  `apm_t94a07_halfTurn_not_homotopic`.
* **Layer 1 (also parallel as a conditional seat):**
  `apm_t94a07_local_fixed_point_packet`, since it receives the tangent
  equality as an explicit hypothesis rather than referring to the first
  theorem.
* **Layer 2 (already proved assembly):** `apm_t94a07` after the three lemma
  bodies are supplied.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t94A07/Blueprint.lean
```

Output of `#print axioms apm_t94a07`:

```text
'apm_t94a07' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The compiler reports exactly three `sorry` declarations, the three lemmas
listed above.  The main theorem and all reused coordinate/cardinality lemmas
are sorry-free.

## claude-14 review split (2026-10-13)

The global LIBRARY lemma `apm_t94a07_halfTurn_not_homotopic` is now a sorry-free assembly of two seat leaves,
using the sorry-free `CoefficientFirstReflection` / `SingularHomologyHomotopy` (same route as t98J01):
- `apm_t94a07_equator_reflection_homotopic` (80-140 lines): restrict the homotopy to the outer equator and
  project radially in the xy-plane; the half-turn acts there as y ↦ -y, giving reflectionMap 1 ≃ id on S¹.
- `apm_t94a07_reflectionMap_not_homotopic_id` (40-80): degree -1 on H₁(S¹;ℤ) via all_reflections_negative.
Answer check: 4 fixed points (x-axis ∩ torus, x = ±(R ± r)), tangent = yz-plane, Df = -id there,
det(I - Df) = 4 > 0, local index +1 each, L(f) = 4 ≠ 0 = L(id).
