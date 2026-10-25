# Blueprint for t94J04

## Finite-cover split (2026-10-24)

The registered statement is unchanged. The `k=1` top-subgroup proof remains;
the former `k>=2` LIBRARY lemma is a sorry-free shared-cover assembly.

`apm_t94J04_subgroup_standard_cover_adapter` (90–150 lines, independent)
applies `CoveringSubgroupCorrespondence.connectedCover`, supplies charted
surface local and semilocal connectivity, then transports through
`F ≃ₜ Surface true 2`. Tools: `connectedCover`, `IsCoveringMap.comp`,
`Nat.card_congr`.

`apm_t94J04_cover_group_transport_adapter` (30–60 lines, independent) takes
explicit `E ≃ₜ Surface true (k+1)` and `pi1(E) ≃ H`, transports fundamental
groups, and changes basepoint. Tools: `fundamentalGroupEquivOfHomeomorphEq`,
`FundamentalGroup.fundamentalGroupMulEquivOfPathConnected`.

C1 standard correspondence/invariance; C2 no final subgroup isomorphism is
assumed; C3 both are transport; C4/C5 maps, basepoints and equivalences are
explicit; C6 consumer hypotheses only; C7 natural index; C8 valid also at
`k=1`, assembly uses `k>=2`; C9 neither repeats the ancestor; C10 matches.
The assembly gives both subgroups the common group `pi1(Surface true (k+1))`.

## Earlier record (blueprint time)

Kept for the triage and the degeneracies checked, which still hold. Where it
calls the finite-cover lemma LIBRARY, the 2026-10-24 section above supersedes it:
that lemma is now an assembly over
`ConstructionTargets.StandardSurfaceFiniteCover`, and its open obligations are
the adapters named above.


### Triage

Verdict: **true and faithful** (as registered).

The source says that all subgroups of a genus-two surface group having a
fixed finite index `k` are isomorphic.  The Lean statement correctly assumes
`0 < k`: in Mathlib `Subgroup.index = 0` represents infinite index, and the
informal covering argument only concerns `k >= 1`.  The hypothesis
`apm_t94J04_isGenusTwoSurface F` is the direct homeomorphism-class encoding of
the source's closed orientable genus-two surface.

Degenerate checks:

* `k = 0` is excluded.  This is essential; equal infinite index does not
  determine subgroup isomorphism type.
* At `k = 1`, `Subgroup.index_eq_one` makes both subgroups `top`, yielding the
  compiled group equivalence in the first lemma.
* The surface type cannot be empty: `PathConnectedSpace F` supplies a point,
  and the theorem also explicitly receives `p : F`.
* The hand computation for a `k`-sheeted cover is
  `chi = k(2-2*2) = -2k = 2-2(k+1)`, so every connected cover has genus
  `k+1`.

I read the topology worklist's stopped covering-subgroup program before
splitting this blueprint.  Its recorded obstruction is exactly construction
of a connected cover from an arbitrary subgroup (with correct left/right
coset conventions), followed here by finite-cover Euler-characteristic
multiplicativity and surface recognition.  I also searched every sorry-free
`ConstructionTargets/*.lean` file mentioning covers, surfaces, polygons, or
fundamental groups.  `ConstructionTargets.SuppliedCoverAlgebra` handles a
cover already supplied and explicitly does not construct one from a subgroup.
`ConstructionTargets.SurfaceClassification` currently develops finite
two-complex/disk-cover infrastructure but exports no classification of finite
covers of a closed polygon surface.  `ConstructionTargets.Surfaces` supplies
the polygon model and Euler-characteristic formula.  Thus there is no short
elementary route already present.

### Lemmas

### `apm_t94J04_subgroups_equiv_of_index_one` — proved

**Statement.** Two index-one subgroups of any group are isomorphic.

**Proof.** Rewrite both index equalities with `Subgroup.index_eq_one`; both
subgroups become `top`, and `MulEquiv.refl` closes the goal.

**Expected size.** Already proved, 6 lines.

**Dependencies.** Definitions only.

**Truth check.** In any group, the only subgroup with one coset is the whole
group.  This includes the trivial group.

### `apm_t94J04_eulerChar_cover_arithmetic` — proved

**Statement.** `2 - 2(k+1) = k(2-2*2)` over the integers.

**Proof.** Ring normalization.

**Expected size.** Already proved, 2 lines.

**Dependencies.** None.

**Truth check.** At `k=1` both sides are `-2`; at `k=2` both are `-4`.

This lemma records the numerical part needed inside the library program.  It
is not used by the final assembly until that program is decomposed internally.

### `apm_t94J04_finiteIndexSurfaceSubgroupClassification` — LIBRARY

**Statement.** For a surface homeomorphic to the standard orientable
genus-two polygon surface, any two subgroups of its fundamental group with
the same index `k >= 2` are isomorphic.

**Why true.** Apply the covering-subgroup correspondence to realize each
subgroup as the fundamental group of a connected `k`-sheeted cover.  A finite
cover of a closed orientable surface is again closed and orientable.  Euler
characteristic multiplies by `k`; the proved arithmetic lemma makes both
covers genus `k+1`.  Classification of closed orientable surfaces gives a
homeomorphism between the covers.  Functoriality of fundamental groups, and
the two covering-induced identifications with `H` and `K`, gives the desired
group equivalence.

**Expected size.** 800–1600 lines as a shared library program, rather than a
lemma-seat task.  This is the worklist program
`program-2026-10-12-covering-subgroup-correspondence`, together with the
finite-cover surface recognition part of the surface-classification
foundation.  The closest sorry-free files are
`ConstructionTargets/Surfaces.lean`,
`ConstructionTargets/SurfaceClassification.lean`, and
`ConstructionTargets/CoveringDegree.lean`.

**Dependencies.** Definitions only at the blueprint boundary.  The large
program should internally consume the proved Euler arithmetic lemma.  Its
statement is deliberately the exact combined result needed by this consumer,
without encoding its conclusion in a hypothesis.

**Truth check.** For `k=2`, each cover has Euler characteristic `-4`, hence
genus `3`; for `k=3`, it has Euler characteristic `-6`, hence genus `4`.
The classical subgroup-cover theorem confirms every finite-index subgroup is
realized, including nonnormal subgroups; this is why mere equivalence of
right-coset sets would not suffice.

### Dependency layers

* **Layer 1 (parallel):** the two already proved elementary lemmas and the
  LIBRARY surface-subgroup classification program.
* **Layer 2 (already proved):** `apm_t94j04`; split on `k=1`, use the first
  lemma there, and derive `2 <= k` by `omega` for the LIBRARY lemma otherwise.

There is one open lemma, and it is intentionally marked LIBRARY because its
honest proof is the stalled shared topology foundation rather than a
30–150-line lemma-seat task.

### Compilation and axioms

`Blueprint.lean` compiles with the required single-file command.  The output
of `#print axioms apm_t94j04` is pasted below:

```text
'apm_t94j04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
