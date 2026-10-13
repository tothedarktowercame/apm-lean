# Blueprint for tunk01

## Triage

Verdict: **true and faithful**.  The word and stipulated two vertex classes are
the same data as `t94J09`.  They give `V = 2`, `E = 7`, and `F = 1`, hence
`χ = -4`; the two positive occurrences of `a` show nonorientability, so the
closed-surface classification gives nonorientable genus `2 - χ = 6`.

The finite claims were checked by compiled kernel computation (`decide`).  As
degenerate checks, the two vertex classes are both inhabited (corners `0` and
`3`), all seven labels occur, and specializing the orientation predicate to
`a` computes a contradiction.  The hypothesis `hPresentation` rules out an
unrelated or empty `X`; composing it with the normalization gives the required
homeomorphism.  The topology-loop audit records no counterexample and confirms
that the missing construction is the literal quotient normalization.

The blueprint copies the theorem type from `Main.lean` exactly.  All finite
certificates are proved, leaving one genuine shared library obligation.

## Remaining lemma

### `apm_tunk01_polygon_normalization` — LIBRARY

**Statement in words.** The quotient of the disk by the concrete fourteen-edge
word is homeomorphic to the standard twelve-edge presentation of the
nonorientable genus-six surface.

**Why true.** This is the same polygon normalization as
`apm_t94J09_polygon_normalization`, with only the namespace changed.  Classical
polygon cut-and-paste reduces the given signed word to six twisted pairs.
Formally, the shared polygon-surface classification program must realize the
elementary edge slides/cuts as homeomorphisms of quotients and compose them.
The closest sorry-free infrastructure is `ConstructionTargets.Surfaces`,
`ConstructionTargets.SurfaceClassification`, and
`ConstructionTargets.PolygonSurfacePiOne`; none currently contains the final
normalization theorem.  The audit specifically warns that a single disk
self-homeomorphism is too restrictive for general cut-and-paste.

**Expected size.** 500–1000 lines as the shared polygon-normalization library
program (or a short adapter once that program lands).

**Dependencies.** Definitions only.  This is the exact classification lemma
shared in form with the t94J09 blueprint.

**Truth check.** Independently, `χ = -4` and the same-orientation `a` pair force
nonorientable genus six.  The target `N6Rel` is the standard six-twisted-pair
word.  It cannot be genus three, whose Euler characteristic is `-1`.

## Dependency layers

* **Layer 1:** `apm_tunk01_polygon_normalization` (LIBRARY).
* **Layer 2:** the already proved finite certificates and the sorry-free main
  theorem assembly.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/tunk01/Blueprint.lean
```

The final output of `#print axioms apm_tunk01` is:

```text
'apm_tunk01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The sole `sorry` warning is for the Layer 1 library lemma; the main theorem has
no direct `sorry`.
