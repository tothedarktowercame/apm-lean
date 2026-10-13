# Compatible coordinates on a weak union of nested arcs

This blueprint follows `~/notes/closer/t91j06-report.md` and the t91J06 route
in `holes/labs/topology-routes/routes-1.md`.  It covers the interval-coordinate
extension, recursive stage coordinates, corrected gluing theorem, and frozen
adapter.  The shared area is `nested-interval-exhaustion`.

The construction builds on the banked
`ConstructionTargets.NestedEmbeddingTransition`, the local stage compactness,
monotonicity, and interior-coverage lemmas in `problems/t91J06/lean/Main.lean`,
and Mathlib's order theory for continuous injections on real intervals.  The
existing `apm_t91J06_bridge_glue_compatible_stage_coordinates` is false because
it omits `hf`; it must be replaced by B4 and must never be consumed as stated.

### B1. Extend prescribed coordinates across an interior interval embedding

lean: `t91J06Closure.extend_interval_embedding_coordinates` : for
`I = Set.Icc (0 : ℝ) 1`, `n : ℕ`, a continuous injective map `t : I → I`
with `Set.range t ⊆ {x | x.1 ∈ Set.Ioo 0 1}`, and a homeomorphism
`q : I ≃ₜ Set.Icc (-(n + 1 : ℝ)) (n + 1 : ℝ)`, there is a homeomorphism
`Q : I ≃ₜ Set.Icc (-(n + 2 : ℝ)) (n + 2 : ℝ)` satisfying
`∀ x, (Q (t x) : ℝ) = (q x : ℝ)`.

uses: Mathlib `Continuous.strictMono_of_inj_boundedOrder` and its antitone
counterpart, applied separately to `t` and to the underlying map of `q`;
endpoint extrema for monotone maps, affine homeomorphisms of closed intervals,
and the pasting lemma for two closed endpoint intervals

status: partial

Classify both `t` and the underlying real-valued map of `q` as strictly
monotone or strictly antitone.  The endpoint images of `t` are distinct
interior points and bound `range t`.  On that middle interval prescribe
`q ∘ t⁻¹`.  Its orientation is increasing exactly when `q` and `t` have the
same orientation, and decreasing exactly when their orientations differ.
Assign the two outer affine pieces according to this *composite* orientation:
in the increasing cases join the left endpoint to `-(n+1)` and `n+1` to the
right endpoint; in the decreasing cases join the left endpoint to `n+1` and
`-(n+1)` to the right endpoint.  Thus all four `(orientation t, orientation
q)` cases agree at both seams.  Prove continuity by closed-set pasting,
strict monotonicity or strict antitonicity piecewise and across seams, and
surjectivity by the intermediate value theorem.  Package the continuous
bijection as a homeomorphism using compactness of `I` and the Hausdorff target.

Compiled progress: `intervalEmbedding_orientation` and
`intervalHomeomorph_orientation` classify the orientations of `t` and the
real coordinate of `q` independently.  The theorem
`intervalEmbedding_homeomorph_four_orientations` packages both decisions, so
the implementation must now construct and paste the affine endpoint pieces
in those four cases.

### B2. Canonical coordinates on one embedded stage

lean: `t91J06Closure.stageHomeomorphUnitInterval` : for
`hf : Topology.IsEmbedding f`, a homeomorphism
`↥(f '' Set.univ) ≃ₜ apm_t91J06_I`.

uses: Mathlib `Topology.IsEmbedding.toHomeomorph`, `Set.image_univ`

status: planned

Use `hf.toHomeomorph : I ≃ₜ Set.range f`, identify `Set.range f` with
`f '' Set.univ`, and take the symmetric orientation.  This node performs the
only subtype-range conversion used by the recursion.

### B3. Recursively compatible stage coordinates

lean: `apm_t91J06_bridge_compatible_stage_coordinates` : exactly the current
unregistered declaration in `problems/t91J06/lean/Main.lean`.

uses: B1, B2, banked `NestedEmbeddingTransition.transition`,
`continuous_transition`, `injective_transition`,
`transition_mem_of_range_subset_image`, local `apm_t91J06_stage_mono`

status: planned

Start with B2 for stage zero followed by the affine homeomorphism from `[0,1]`
to `[-1,1]`.  At successor `n+1`, express the old stage inside the new stage
by the banked transition map.  `hnested` places its range in `(0,1)`.  Apply B1
to extend the already chosen coordinate to `[-(n+2),n+2]`.  Dependent choice
packages the recursion.  The B1 extension equation, the transition commuting
equation, and embedding injectivity give the displayed compatibility equality.

### B4. Glue compatible coordinates, retaining embedding continuity

lean: `apm_t91J06_bridge_glue_with_embeddings` : the type of the current glue
helper with the additional hypothesis
`hf : ∀ n, Topology.IsEmbedding (f n)` and conclusion `Nonempty (X ≃ₜ ℝ)`.

uses: B3, local `apm_t91J06_exists_mem_stage`,
`apm_t91J06_exists_mem_stage_interior`, `apm_t91J06_stage_mono`, `hf`,
`hcover`, `hweak`

status: planned

For `x : X`, choose a stage containing it and evaluate that stage coordinate;
compatibility proves independence of the choice by moving both indices to their
maximum.  Every real number lies in a sufficiently large symmetric interval,
so stage-coordinate surjectivity gives global surjectivity; a common later
stage gives injectivity.  To prove continuity, test inverse images of closed
sets with `hweak`; after precomposition by `f n`, compatibility identifies the
map with the continuous `g n` coordinate.  For inverse continuity, each point
of `X` lies in an interior stage, and `hf n` plus `g n` identifies a
neighbourhood with an open real interval.  These local inverse formulas agree
by compatibility.  The use of `hf` here is essential and repairs the false old
helper rather than proving it.

### B5. Frozen theorem adapter

lean: `apm_t91j06` : exactly the registered declaration in
`problems/t91J06/lean/Main.lean`.

uses: B3, B4

status: planned

Choose the compatible family from B3 and pass it, together with the frozen
`hf`, `hnested`, `hcover`, and `hweak`, to B4.  Replace the two obsolete
unregistered bridge declarations as needed, but do not change the registered
statement or any definition occurring in it.
