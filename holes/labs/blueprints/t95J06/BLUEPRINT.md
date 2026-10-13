# Blueprint for t95J06

## Triage

Verdict: **true and faithful**.

The registered formula for the flow is `H(z,t) = exp(i t) • z`, exactly the
flow of the vector field `v(z)=iz`.  The first conclusion is the stated
invariance of the displayed torus.  The second conclusion says that every
actual connected component of a compact orientable invariant surface is
homeomorphic to `Circle × Circle`.  The predicate's historical name says
“Diffeomorphic”, but its value is explicitly a `Homeomorph`; this is slightly
weaker than the informal wording, not a false or incompatible claim, and the
batch registration marks the encoding faithful.

I tried the relevant degeneracies.  If `F` is empty, the component conclusion
is vacuous.  A point or zero-dimensional component cannot satisfy the frozen
`H₂ ≅ ℤ` condition.  On the unit sphere no vector is zero, so a scalar
`g : Circle` fixing a point must have `g=1`; hence the restricted circle action
has no exceptional fixed orbit.  At real times `0` and `2π`, the proved flow
lemmas give identity and periodicity.  The exhibited set `T` is nonempty
(take `θ=φ=0`) and the already compiled coordinate calculation preserves it.

The solve loop and topology loop found no counterexample.  Their reviewed STOP
is infrastructural: the intrinsic chart on `F` is not asserted compatible
with the ambient inclusion, so a smooth-action theorem cannot be applied.
The valid route is instead the continuous compact-group action theorem.

## Definitions and proved prefix

`Blueprint.lean` reproduces the frozen definitions verbatim and adds
`apm_t95j06_HasFreeContinuousCircleAction`.  This predicate contains genuine
data: a jointly continuous map `Circle × X → X`, its unit and multiplication
laws, and freeness.  It does not mention a torus or encode the desired
conclusion.

The explicit-torus invariance, `2π` periodicity, time-zero identity, and
additive action law are copied with their complete proofs from `Main.lean`.
The blueprint imports `ConstructionTargets.SurfaceClassification`, the closest
sorry-free shared foundation.  That module currently supplies finite surface
triangulation/cover infrastructure, but stops before surface classification;
its source was checked to contain no `sorry`.

## Lemma 1 — `apm_t95j06_component_free_circle_action`

**Statement in words.** For every point `x` of an invariant set `F`, the Hopf
scalar action restricts to a jointly continuous free circle action on the
connected component of `x`.

**Why true.** Define the action by complex scalar multiplication
`(g,y) ↦ g • y`.  For `g`, choose the real parameter `Complex.arg g`; the
identity `Circle.exp_arg g` and the frozen Hopf formula identify scalar
multiplication by `g` with `H(-, Complex.arg g)`, so invariance keeps the image
in `F`.  For fixed `g`, multiplication is a homeomorphism (inverse `g⁻¹`), and
therefore sends the connected component of `x` into itself; applying the
inverse gives equality.  Joint continuity follows from continuous complex
scalar multiplication and the induced subtype topology.  The group laws are
scalar multiplication laws.  If `g • y = y`, the sphere vector underlying
`y` is nonzero because its norm is one; cancellation in one nonzero coordinate
gives `g=1`.

The topology-loop diagnostic `/tmp/T95J06ActionDiagnostic.lean` previously
compiled exactly this construction and was independently reviewed.  The file
was ephemeral and is no longer present, so the blueprint preserves the clean
interface rather than claiming that proof as copied code.

**Estimated size.** 120–250 lines.

**Dependencies.** Definitions only (and Mathlib's circle/scalar APIs); it is
independent of Lemma 2's implementation.

**Truth check.** Checked at `g=1`, at `g=-1`, and on the explicit point
`(1,0,0) ∈ S⁵`.  The last point is fixed only when `g=1`.  This agrees with the
reviewed compiled action diagnostic recorded in `worklist2.edn`.

## Lemma 2 — `apm_t95j06_freeCircleAction_surface_classification` (LIBRARY)

**Statement in words.** If `F` satisfies the frozen compact orientable surface
predicate and every connected component carries a free continuous circle
action, then every component is homeomorphic to the torus.

**Why true.** A free continuous action of the compact Lie group `S¹` on a
Hausdorff topological manifold is proper and admits slices.  Thus the orbit map
of each connected component is a principal `S¹`-bundle, and its orbit space is
a compact connected 1-manifold.  The latter is a circle.  A circle bundle over
a circle has total space homeomorphic to the torus or the Klein bottle (in the
principal case the structure group is rotations, so the total space is already
the torus; the broader bundle classification gives the same final dichotomy).
The frozen isomorphism `H₂(component; ℤ) ≅ ℤ` excludes the Klein bottle, whose
integral top homology vanishes.  Hence the component is a torus.

This is the exact missing theorem named by the topology-loop STOP.  The
closest sorry-free file is `ConstructionTargets.SurfaceClassification.lean`;
it develops finite two-complex and compact-surface cover infrastructure but
does not yet prove the free-action slice theorem, orbit-space manifold result,
circle-bundle classification, or the final homology comparison.  The existing
shared polygon-surface classification/homology programs may discharge the
last stage once the orbit bundle has been converted to a polygon surface.

**Estimated size.** 1,500–4,000 lines across a ConstructionTargets program.
It is intentionally one LIBRARY lemma: splitting it into small implications
would merely postulate principal-bundle or classification conclusions, while
the slice/orbit construction and classification share their quotient data.

**Dependencies.** Its statement takes Lemma 1's conclusion as a hypothesis,
so its seat can work in parallel with Lemma 1.  It otherwise depends only on
the definitions and the surface-classification foundations.

**Truth check.** The standard examples are the translation action on the
torus (free, with `H₂ = ℤ`) and the corresponding circle fibration of the
Klein bottle (the nonorientable alternative, with `H₂ = 0`).  A sphere fails
the freeness test, while a point fails both the dimension and `H₂` tests.
These exhaust compact connected surfaces admitting a free circle action.

## Assembly and dependency layers

`apm_t95J06_bridge_1` first obtains the action data from Lemma 1 and passes it
to Lemma 2.  The registered theorem uses that bridge together with the already
proved explicit-torus calculation.  Neither assembly theorem contains a
`sorry`.

- **Layer 1 (parallel):**
  `apm_t95j06_component_free_circle_action` and
  `apm_t95j06_freeCircleAction_surface_classification` (LIBRARY, developed
  against the former's conclusion as an explicit hypothesis).
- **Layer 2 (already compiled):** `apm_t95J06_bridge_1`.
- **Layer 3 (already compiled):** `apm_t95j06`.

Lemma count: 2 unfinished top-level lemmas, one seat-sized and one LIBRARY
program.  I am convinced both statements are mathematically true.  The main
uncertainty is implementation scale of the topological slice/orbit theorem,
not its validity.

## Compilation and axioms gate

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t95J06/Blueprint.lean
```

Result: exit 0.  Exact output of `#print axioms apm_t95j06`:

```text
'apm_t95j06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` reaches the final theorem only through the two named top-level
lemmas.
