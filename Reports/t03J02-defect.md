# t03J02 defect report: the frozen attachment has no collar/cofibration producer

## Exact obstruction

Both requested invariant layers reach the same missing geometric seam.  The
frozen hypotheses provide, for each attaching map,

```lean
hj : Topology.IsEmbedding j
hnull : j.Nullhomotopic
```

with `j : C(Circle, Circle × Circle)`.  The frozen space is the `EqvGen`
quotient of the disjoint union.  Its two summand images are closed and meet
along the attached circle; they do not form an open cover.  Consequently:

* the open-cover singular Mayer--Vietoris sequence cannot be applied directly;
* an open-cover Seifert--van Kampen theorem could not be applied directly even
  if one were present;
* comparison with a homotopy pushout requires each arbitrary embedded circle
  to be a cofibration or to admit a collar/regular neighbourhood.

At commit `51de6d9`, neither pinned Mathlib nor this repository contains a
cofibration or NDR-pair API, an embedded-circle collar theorem, a surface
Jordan--Schoenflies theorem, or a theorem turning the displayed `IsEmbedding`
hypothesis into the required homotopy-pushout comparison.  Repository-wide
search also found no topological Seifert--van Kampen theorem, circle
fundamental-group computation, Kunneth theorem, torus singular-homology
computation, or closed-pushout Mayer--Vietoris theorem.  Mathlib's
`CategoryTheory.Limits.VanKampen` is about universal colimits, and its
Mayer--Vietoris results are sheaf-cohomological; neither has a type that can
produce either frozen bridge.

This is the precise missing representational seam named by the dispatch's
defect protocol.  The mathematical statement is not falsified: classically an
embedded circle in a surface is tame/collared.  The producer of that fact and
its Lean interface are absent.

## Salvaged library increment

`ConstructionTargets.SingularExcision` now contains the general chain-level
Mayer--Vietoris short exact sequence for two simplicial subcomplexes:

```text
subcomplexChainsMap_component_mono
subcomplexChainsMap_mono
subcomplexMayerVietorisShortComplex
subcomplexMayerVietorisShortComplex_shortExact
subcomplexMayerVietorisConnecting
subcomplexMayerVietoris_exact_intersection
subcomplexMayerVietoris_exact_pieces
subcomplexMayerVietoris_exact_union
```

The module builds, and the five printed headline declarations use exactly
`[propext, Classical.choice, Quot.sound]`.  They are not reachable from the
three frozen targets because the missing geometric seam prevents either bridge
from consuming them.  Their disposition is `:quarantine`: they remain in a
module the keying problem does not import and are not represented as completed
target work.

## Current target axiom output

```text
'apm_t03j02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'apm_t03J02_bridge_1' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'apm_t03J02_bridge_2' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two bridge sorries therefore remain open.  The primary theorem itself now
only packages the two bridges and introduces no third independent sorry.

## Reproduction

```text
bash scripts/t03J02-declaration-reachability.sh
```

The runner computes the union closure of `apm_t03j02`,
`apm_t03J02_bridge_1`, and `apm_t03J02_bridge_2` in one elaborated-environment
pass.
