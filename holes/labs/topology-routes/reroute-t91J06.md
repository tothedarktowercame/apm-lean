# t91J06 reroute: clamp-and-ramp extension

## Exact stall in the old route

The two loop attempts did not enter the `Nat.rec` construction of
`apm_t91J06_bridge_compatible_stage_coordinates`.  They stopped at its proposed
`extend_interval_homeomorph`: given `0 < a < b < 1` and an oriented
homeomorphism `h : Icc a b ≃ₜ Icc (-m) m`, build a homeomorphism
`Icc 0 1 ≃ₜ Icc (-(m+1)) (m+1)` agreeing with `h` on `Icc a b`.

In Lean terms, the old proposal used three affine pieces and required explicit
`ContinuousOn` gluing at `a` and `b`, strict monotonicity/bijectivity of the
piecewise function, an antitone branch, and a subtype equality proving exact
restriction.  No theorem bundled those obligations, so both attempts merely
reconfirmed that missing bundle and made no proof-term progress.

There is also a distinct downstream defect: the current
`apm_t91J06_bridge_glue_compatible_stage_coordinates` is false because its
signature omits `hf`.  It must be replaced (the helper is not frozen) by an
embedding-aware version taking `hf : ∀ n, Topology.IsEmbedding (f n)`.  The
frozen main theorem already has this hypothesis.

## New route

The reroute keeps compatible compact-stage coordinates, but avoids piecewise
topology entirely.  After orienting `h` increasingly (compose with negation in
the antitone case), define on the ambient real line

```text
F(x) = h(projIcc a b x)
       - max 0 ((a-x)/a)
       + max 0 ((x-b)/(1-b)).
```

On `[a,b]` both ramps vanish, so `F=h` exactly.  On `[0,a]`, the clamped `h`
term is its left endpoint `-m` and the left ramp is affine from `-1` to `0`.
On `[b,1]`, the clamped term is `m` and the right ramp is affine from `0` to
`1`.  Thus `F(0)=-(m+1)` and `F(1)=m+1`.  Continuity is global by algebra of
continuous functions (`continuous_projIcc` and continuity of `max`), with no
join lemmas.

Ordered implementation steps:

1. `transition_ordered` (about 35--55 lines): use `(hf (n+1)).injective` to
   choose the unique transition `t : I → I`; prove continuity from the inverse
   homeomorphism onto the range, and use the existing interval-injection
   monotonicity theorem to split into strict-mono/strict-antitone cases.  Prove
   its endpoint image is `Icc a b` (or reversed endpoints) and derive
   `0 < a`, `b < 1` from `hnested`.

2. `clampRamp` plus continuity/restriction lemmas (compiled; about 20 lines):
   use the formula above.  This directly supplies the two facts for which the
   old route needed piecewise join bookkeeping.

3. `clampRamp_strictMonoOn` and endpoint/range lemmas (about 45--70 lines):
   prove strict increase by splitting `x<y` according to `x,y` lying left of,
   in, or right of `[a,b]`.  In a common outer region it is affine; in the
   middle use `h.strictMono`; across regions compare through `F a=-m` and
   `F b=m`.  From endpoints and continuity obtain range exactly
   `Icc (-(m+1)) (m+1)` by `intermediate_value_Icc`; strict monotonicity gives
   injectivity.  Package the resulting equivalence with
   `Continuous.homeoOfEquivCompactToT2`.  For an antitone transition, first
   reverse the inherited inner coordinate by target negation, then apply the
   same increasing lemma (no second extension construction).

4. `apm_t91J06_bridge_compatible_stage_coordinates` (about 45--65 lines):
   start from the affine unit-interval coordinate at stage zero; recurse using
   steps 1--3.  Convert between each embedded stage and `I` using
   `Topology.IsEmbedding.toHomeomorph`.  Exact inner agreement from step 2 is
   the recursive compatibility equation.

5. Replace the false glue helper by
   `apm_t91J06_bridge_glue_compatible_stage_coordinates_of_embedding` (about
   80--120 lines), explicitly taking `hf`.  Define the eventual coordinate by
   choosing a containing stage.  Prove choice-independence by iterating
   `hcompat`; injectivity in a common later stage; and surjectivity by choosing
   an interval containing the real value.  For continuity of the forward map,
   apply `hweak` and rewrite each pullback through the embedding/homeomorphism.
   For inverse continuity, locally use `(g n).symm` on an open symmetric
   interval containing the point.

6. Main assembly (2--4 lines): invoke step 4 and the corrected helper from
   step 5.  Do not invoke the current false helper.

## Compiled probe

Probe: `/tmp/reroute-t91J06/ClampRamp.lean`.

Command:

```sh
cd /home/joe/code/apm-lean && lake env lean /tmp/reroute-t91J06/ClampRamp.lean
```

Result: exit 0.  The probe compiles:

- the clamp-and-ramp definition;
- global continuity of the formula via `continuous_projIcc`;
- exact equality with the supplied homeomorphism on `Icc a b`, using
  `Set.projIcc_of_mem` and vanishing of both ramps.

The probe contains no `sorry`.  It was compiled from `/tmp`; nothing in the
shared repository was written, staged, or committed.

## Confidence

Confidence is **medium-high** that steps 2--4 are materially smaller and more
robust than the stalled route: the riskiest continuity and exact-restriction
claims compile, and join continuity has disappeared.  Confidence is **medium**
for full closure because transition-image subtype bookkeeping and the corrected
global gluing helper remain substantial.  Neither requires the missing
piecewise-extension theorem, and the gluing correction uses the embedding
hypothesis already present in the frozen statement.
