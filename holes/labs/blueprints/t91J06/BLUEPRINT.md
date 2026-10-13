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

### `apm_t91J06_extend_interval_embedding_coordinates` — LIBRARY

**Statement in words.** Let `t : [0,1] → [0,1]` be a continuous injection
whose range lies in `(0,1)`.  Given arbitrary coordinates
`q : [0,1] ≃ₜ [-(n+1),n+1]`, extend them to coordinates
`Q : [0,1] ≃ₜ [-(n+2),n+2]` satisfying `Q (t x) = q x` exactly.

**Why true.** Use
`t91J06Closure.intervalEmbedding_homeomorph_four_orientations` to split on
the independent orientations of `t` and `q`.  The endpoint images of `t` are
distinct points strictly between `0` and `1`.  On the middle interval define
`q ∘ t⁻¹`; on the two complementary intervals use affine ramps to the two new
target endpoints.  Which target endpoint belongs to which side is determined
by the orientation of the composite, so all four cases paste.  Prove
continuity at the two seams, strict monotonicity or antitonicity across the
three regions, and surjectivity, then package the continuous bijection using
compact-to-Hausdorff.

This is marked **LIBRARY** because repeated topology-loop attempts stopped at
the bundled affine-pasting construction and the active shared program
`program-2026-10-11-close-t91j06` is building precisely this theorem in
`ConstructionTargets/t91J06Closure.lean`.  That file is the closest sorry-free
construction target and already contains the four-orientation front end; what
is missing is the actual affine endpoint pieces, seam proofs, and packaging.

**Expected size.** 200–350 lines.  The lower estimate is possible with a good
piecewise monotonicity API; otherwise it is program-sized rather than an
honest one-session lemma.

**Dependencies.** Definitions and the imported four-orientation theorem only.

**Truth check.** For the increasing test embedding `t(x)=1/4+x/2` and
increasing affine `q`, the construction extends the middle `[-(n+1),n+1]` by
one unit on each side.  With decreasing `q(x)` the endpoint assignment swaps,
which exposes and repairs the error in an earlier topology-loop plan that
split only on `t`.  The strict-interior hypothesis makes both outside pieces
nondegenerate.

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

* **Layer 1 (parallel):**
  `apm_t91J06_extend_interval_embedding_coordinates` (LIBRARY program),
  `apm_t91J06_compatible_stage_coordinates` (proved against the extension
  contract), and `apm_t91J06_glue_with_embeddings` (proved against arbitrary
  compatible coordinates).
* **Layer 2 (already compiled, no seat):** the final two-line assembly after
  the three Layer 1 bodies are supplied.

## Compilation and axioms

The missing local `.olean` files were built without updating Mathlib:

```text
lake build ConstructionTargets.t91J06Closure ConstructionTargets.NestedEmbeddingTransition
```

Then the blueprint compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t91J06/Blueprint.lean
```

The three warnings are exactly the three top-level admitted lemmas above.  The
requested final output was:

```text
'apm_t91j06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` reaches the registered theorem only through the three named
lemma bodies; the definitions, reused preliminary lemmas, and main assembly
are sorry-free.
