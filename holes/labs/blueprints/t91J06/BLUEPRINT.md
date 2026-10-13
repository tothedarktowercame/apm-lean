# Blueprint for t91J06

## Triage

Verdict: **true and faithful**.

The Lean theorem says exactly that a space exhausted by nested embedded closed
unit intervals, with each old stage contained in the relative interior of the
next and with the weak topology for those stages, is homeomorphic to `ℝ`.
This matches `problem.md`.  The third hypothesis is written using closed
preimages under `f n`; because each `f n` is an embedding, this is equivalent
to saying that the intersection with each embedded arc is relatively closed.

I tried the relevant degeneracies before accepting the theorem.

* `X` cannot be empty: `apm_t91J06_I` contains `0`, while every `f n` has
  codomain `X`.
* A singleton or other finite space cannot admit an embedding of the
  nontrivial interval.
* A surviving endpoint or half-line end is excluded because every complete
  stage, including both endpoints, lies in the next stage's displayed
  interior.
* A circle can be covered by arcs, but not by this nested weak exhaustion:
  compatible interval order on all stages produces two unbounded directions;
  equivalently, a compact circle cannot have the resulting weak direct-limit
  topology.
* Reversing the orientation at any stage is harmless, but it is a real case
  that must be handled.  In particular, the extension construction must split
  independently on the orientation of the transition and of the previously
  chosen coordinate.

The registered final theorem is sound.  However, the old unregistered helper
`apm_t91J06_bridge_glue_compatible_stage_coordinates` in `Main.lean` is false
as stated because it omits `hf`.  With an arbitrary topology on `X`, the same
set-theoretic exhaustion and coordinate data do not force continuity of the
inverse.  The blueprint never uses that helper; its gluing lemma retains
`hf`, as the final theorem does.

## Reused compiled work

The elementary exhaustion lemmas from `Main.lean` are copied with their
proofs: compactness, monotonicity, stage coverage, interior coverage, and
common-interior-stage coverage.

Two sorry-free construction modules are imported:

* `ConstructionTargets.NestedEmbeddingTransition` supplies the transition
  map between nested embedded intervals, its commuting equation, continuity,
  injectivity, and interior-range lemma.
* `ConstructionTargets.t91J06Closure` supplies the already proved monotone or
  antitone classification of a continuous interval injection and the
  independent orientation classification for an arbitrary interval
  homeomorphism.

I checked both files with `grep -L sorry`; neither contains `sorry`.  I also
searched all sorry-free `ConstructionTargets` files with names or contents
matching nested intervals, embeddings, transitions, interval homeomorphisms,
clamp/ramp, affine extension, and direct-limit gluing.  No module contains the
remaining bundled extension or gluing result.  The topology worklist and
`~/notes/closer/audits/t91J06.*` agree on these exact boundaries.

## Remaining lemmas

### Interval-coordinate extension: seven parallel leaves

The former 200–350 line LIBRARY boundary is now a sorry-free assembly.  It
uses `t91J06Closure.intervalEmbedding_homeomorph_four_orientations` and calls
one of four independent ramp constructors, an independent IVT lemma, and an
independent packaging lemma.  In the descriptions below put
`A = n + 2`, `u = (t 0 : ℝ)`, and `v = (t 1 : ℝ)`.

#### `apm_t91J06_extend_ramp_mono_mono` (90–140 lines, independent)

Here `t` and the real coordinate of `q` are strictly increasing.  Define `F`
on the closed pieces `[0,u]`, `[u,v]`, `[v,1]`: the outside formulas are the
unique affine maps from `(-A,q 0)` and `(q 1,A)`, while the middle formula is
`q (t⁻¹ y)`.  A convenient inverse is `Set.InjOn.invFun t univ`, or one can use
`Function.invFun`; use `Function.leftInverse_invFun` after proving injectivity.
For continuity, prove continuity on each `Icc` and paste twice with
`ContinuousOn.piecewise` (or `ContinuousOn.union` plus `IsClosed.isClosed_Icc`);
the seam equations reduce by `t`'s inverse law.  For strict monotonicity, use
`strictMonoOn_iff_forall_lt` on each piece, then split two points according to
the seams; `hqmono`, `htmono`, and positivity of the affine denominators close
the cases.  `htint` at `t 0,t 1` proves `0<u<v<1`, so neither ramp degenerates.

#### `apm_t91J06_extend_ramp_anti_anti` (90–140 lines, independent)

Both maps reverse orientation, so their composite coordinate is increasing.
Now `v<u`; use pieces `[0,v]`, `[v,u]`, `[u,1]`, joining `-A` to `q 1`, using
`q ∘ t⁻¹` in the middle, and joining `q 0` to `A`.  The useful Mathlib tools
are the same as in the mono/mono leaf, with `htanti.lt_iff_lt` and
`hqanti.lt_iff_lt` (or direct applications of `StrictAnti`) for order reversal.
The endpoint values of a decreasing homeomorphism are forced by surjectivity;
derive them by applying `q.symm` to the target endpoints if simplification
does not find them automatically.

#### `apm_t91J06_extend_ramp_mono_anti` (90–140 lines, independent)

Here `u<v`, but the required `F` is strictly decreasing.  Paste the affine
ramp from `A` to `q 0`, the middle `q ∘ t⁻¹`, and the ramp from `q 1` to `-A`.
Use `StrictAnti` throughout the cross-piece comparisons.  This is deliberately
a separate leaf: it can be proved in parallel, or cheaply obtained from the
mono/mono construction by postcomposing `q` and `F` with target negation.
For that alternative, build the subtype homeomorphism with
`Homeomorph.subtypeCongr`/`Homeomorph.setCongr` and `Homeomorph.neg`.

#### `apm_t91J06_extend_ramp_anti_mono` (90–140 lines, independent)

Here `v<u` and `F` is strictly decreasing.  The three pieces join `A` to
`q 1`, use `q ∘ t⁻¹`, and join `q 0` to `-A`.  It can alternatively be reduced
to the preceding leaf by precomposing with the unit reflection `x ↦ 1-x`.
The strict-interior hypothesis again supplies strict inequalities at both
outside pieces.  Reflections preserve the interval by `sub_nonneg.mpr` and
`sub_le_one`; `Homeomorph.subtypeCongr` is the useful bundling tool.

#### `apm_t91J06_mono_endpoint_surjective` (30–50 lines, independent)

A continuous `F : [0,1] → ℝ` with endpoint values `a,b` hits every point of
`[a,b]`.  This lemma intentionally does not assume monotonicity: apply the
intermediate value theorem, preferably `intermediate_value_Icc`, to `hF` and
the two endpoint equalities.  It remains true when `a=b` and when the interval
is empty (`a>b`, in which case the quantified subtype has no inhabitants).

#### `apm_t91J06_anti_endpoint_surjective` (30–50 lines, independent)

The reversed-endpoint version of the same IVT fact.  Apply
`intermediate_value_Icc` with endpoints exchanged, or reduce to the preceding
lemma after negation.  No order or injectivity assumption is needed.  The
degenerate and empty-target cases are harmless for the same reasons.

#### `apm_t91J06_package_interval_coordinate` (45–80 lines, independent)

Given a continuous injective `F`, an explicit proof that its values lie in the
target `Icc`, explicit surjectivity, and the middle-piece equation, bundle
`x ↦ ⟨F x,hFmem x⟩` as an `Equiv`.  Its continuity follows from
`Continuous.subtype_mk`; package it with
`Continuous.homeoOfEquivCompactToT2` (the domain subtype is compact and the
target is T2).  The extension equation follows by `Subtype.ext`/`rfl` on
values.  This statement carries no hidden interval argument: all bijectivity
facts are explicit hypotheses.

#### `apm_t91J06_extend_interval_embedding_coordinates` (assembly, proved)

Split with
`t91J06Closure.intervalEmbedding_homeomorph_four_orientations`, select the
appropriate ramp leaf, obtain surjectivity from the matching endpoint-IVT
leaf, and invoke the packaging leaf.  `StrictMono.injective` or
`StrictAnti.injective` supplies injectivity.  Thus every admitted leaf above
is mutually independent; none has another admitted declaration in its axiom
closure.

Truth checks: all four orientation combinations occur.  The range-in-interior
hypothesis rules out `t 0` or `t 1` at a boundary and injection rules out equal
seams.  The target has `A=n+2≥2`, so it is nonempty.  In particular, no leaf
merely repeats its desired conclusion, and the packaging leaf cannot conceal
the ramp argument because it receives continuity, range, injectivity,
surjectivity, and compatibility separately.

### `apm_t91J06_compatible_stage_coordinates`

**Statement in words.** Assuming the preceding interval-extension contract,
the nested embedded stages admit homeomorphisms to
`[-(n+1),n+1]` which agree exactly on every preceding stage.

**Why true.** At stage zero, use `(hf 0).toHomeomorph` from the unit interval
onto its range, identify that range with `f 0 '' univ`, and postcompose with
the standard affine homeomorphism `[0,1] ≃ₜ [-1,1]`.  At a successor, use
`ConstructionTargets.NestedEmbeddingTransition.transition`.  Its banked
lemmas give continuity, injectivity, the equation with the two stage
embeddings, and range in the displayed interior by `hnested`.  Apply the
extension hypothesis and transport the resulting coordinates from the unit
interval back to the new embedded stage.  Dependent recursion produces the
family, and the transition commuting equation proves exact compatibility.

The extension theorem is passed as an explicit hypothesis.  Thus a seat can
prove this lemma independently using the contract while the library program
constructs its implementation.

**Expected size.** 100–150 lines.

**Dependencies.** The *statement* of the extension contract; the sorry-free
transition module; `hf`; `hnested`; `apm_t91J06_stage_mono`.

**Truth check.** At `n=0`, the target is exactly `[-1,1]`.  At a successor,
the extension equation has target `[-(n+2),n+2]`, exactly the target obtained
by substituting `n+1` in the family type.  Orientation reversal changes only
which outside piece maps left or right and does not alter compatibility.

### `apm_t91J06_glue_with_embeddings`

**Statement in words.** Compatible coordinates on the compact exhaustion,
together with the embedding, cover, nesting, and weak-topology hypotheses,
glue to a homeomorphism `X ≃ₜ ℝ`.

**Why true.** Define the global coordinate of `x` by choosing a stage that
contains it and evaluating that stage's coordinate.  Compatibility iterated
to the maximum of two indices proves independence of the choice.  The same
common-stage argument proves injectivity.  Every real number lies in some
`[-(n+1),n+1]`, so stage-coordinate surjectivity proves global surjectivity.

For continuity, test the preimage of a closed real set using `hweak`; after
precomposition with `f n`, the map agrees with the continuous coordinate on
stage `n`.  For inverse continuity, every point is in the relative interior
of a later stage.  The embedding `hf n` and the homeomorphism `g n` identify
that neighborhood with an open real interval, on which the inverse has the
local continuous formula supplied by `g n.symm`.  Compatibility makes these
local formulas agree.  This last step is exactly why `hf` must remain in the
statement.

**Expected size.** 100–150 lines with local continuity; up to 180 if the
chosen-stage well-definedness bookkeeping cannot be compressed.

**Dependencies.** Only the definitions and already proved elementary
coverage/monotonicity lemmas.  It takes the compatible family and its equation
as hypotheses, so it is independent of the two coordinate-construction
proofs.

**Truth check.** For the model `X=ℝ` and stages `[-(n+1),n+1]`, the glued map
is the identity.  Any two definitions of a point's coordinate agree after
moving to the maximum stage.  Near a point that was an endpoint at an earlier
stage, interior coverage moves it to a later stage, so it still has a genuine
open inverse chart.

## Assembly and dependency layers

The final `apm_t91j06` has exactly the registered type.  It obtains the family
from `apm_t91J06_compatible_stage_coordinates` and passes it to the corrected
gluing lemma.  Its body contains no `sorry`.

* **Layer 1 (parallel):** the four `apm_t91J06_extend_ramp_*` leaves, the two
  endpoint-surjectivity leaves, `apm_t91J06_package_interval_coordinate`,
  `apm_t91J06_compatible_stage_coordinates` (proved against the extension
  contract), and `apm_t91J06_glue_with_embeddings` (proved against arbitrary
  compatible coordinates).
* **Layer 2 (already compiled, no seat):**
  `apm_t91J06_extend_interval_embedding_coordinates`, assembled from the
  seven interval leaves.
* **Layer 3 (already compiled, no seat):** the final two-line assembly after
  the coordinate and gluing bodies are supplied.

## Compilation and axioms

The missing local `.olean` files were built without updating Mathlib:

```text
lake build ConstructionTargets.t91J06Closure ConstructionTargets.NestedEmbeddingTransition
```

Then the blueprint compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t91J06/Blueprint.lean
```

The admitted declarations are exactly the seven independent interval leaves
above; the rest of this blueprint is already proved.  The requested final
output was:

```text
'apm_t91j06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` reaches the registered theorem only through the seven named
leaf bodies; the definitions, reused preliminary lemmas, interval-extension
assembly, and main assembly are sorry-free.
