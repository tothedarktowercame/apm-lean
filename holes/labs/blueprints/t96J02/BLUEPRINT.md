# t96J02 blueprint

## Triage

Verdict: **true and faithful**. The registered theorem says that every
finite-index subgroup of the actual fundamental group of the frozen Klein
bottle is isomorphic either to that fundamental group or to
`Multiplicative (ℤ × ℤ)`, and it separately asserts that both types occur.
That is exactly the classification requested by `problem.md`.

I tried the endpoint cases first. The trivial subgroup is not finite index
because the Klein group is infinite. The top subgroup is finite index and
immediately realizes the Klein alternative, so the second existential is not
silently asking for a proper subgroup (nor does `problem.md`). The standard
even-vertical-coordinate subgroup has index two and group law reduced to
ordinary addition on two integer coordinates, so it realizes the torus
alternative. The coordinate normal form also shows there are no finite-index
finite or cyclic exceptions.

The topology worklist's earlier STOP was the missing polygon/open-cover/
van-Kampen computation. Its later rows bank the explicit affine Klein action,
its freeness and proper discontinuity, and the generic deck-quotient theorem;
they still report the final fundamental-group identification and the algebraic
finite-index classification as the residual. The audit at
`~/notes/closer/audits/t96J02.edn` agrees.

## Shared definitions and imports

`T96J02Group` and `T96J02TorusGroup` are copied verbatim from `Main.lean`.
`T96J02PresentedGroup` is only an abbreviation for the already defined
`KleinPresentedGroupCoordinateModel.PresentedKleinGroup`; it does not encode
any desired conclusion. The extra imports expose the sorry-free coordinate
normal form and deck-quotient theorem that both substantive programs need.

I searched all `ConstructionTargets/*.lean` for `Klein`, `FiniteIndex`,
`semidirect`, and `FundamentalGroup KleinBottle`, and filtered candidate files
with `grep -L sorry`. The closest sorry-free modules are
`KleinPresentedGroupCoordinateModel.lean`,
`KleinPresentedGroupCoordinateNormalForm.lean`, `KleinPlaneActionFree.lean`,
`KleinPlaneOrbitQuotientTopology.lean`,
`DeckGroupQuotientFundamentalGroup.lean`, and `t93J03Closure.lean`. None
contains the final finite-index classification. The polygon π₁ program is
tracked as `ConstructionTargets/PolygonSurfacePiOne.lean` / 
`program-2026-10-13-polygon-surface-pi1`.

## Lemmas

### `t96J02_kleinPlaneQuotient_pi1_origin`

**Statement.** At the orbit of `(0,0)`, the fundamental group of the affine
plane quotient is the acting presented Klein group.

**Proof route / Mathlib names.** Install
`KleinPlaneOrbitQuotient.kleinPlaneContinuousConstSMul` (or its banked
equivalent) and the properly-discontinuous instance from master commit
`9fd7db798`, then apply
`DeckGroupQuotientFundamentalGroup.freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv`
with `KleinPlaneAffineAction.eq_one_of_smul_eq`.  Contractibility/simply
connectedness and local path connectedness of `ℝ × ℝ` are instances.

**Estimate.** 30–60 lines of instance wiring. **Independent.**

**Truth check.** Freeness says the origin has trivial stabilizer; hence the
deck theorem returns the acting group itself, not a quotient by a stabilizer.

### `t96J02_kleinPlaneQuotient_pi1_every_basepoint`

**Statement.** Given the origin computation explicitly, the same computation
holds at every point of the orbit quotient.

**Proof route / Mathlib names.** Establish `PathConnectedSpace` for the
quotient from the quotient map and the path-connected plane, then use
`FundamentalGroup.fundamentalGroupMulEquivOfPathConnected`.  The already
banked generic proof
`ConstructionTargets.t93J03Closure.fundamentalGroupEquiv_every_basepoint`
is the exact pattern.

**Estimate.** 30–50 lines. **Independent:** it takes the preceding leaf's
whole conclusion as `h₀` and does not refer to that theorem.

**Truth check.** The quotient is nonempty (it contains the origin orbit) and
path connected as a continuous quotient of the plane, so there is no empty
or disconnected-component edge case.

### Klein quotient comparison (split into four leaves)

The previously suggested carrier-level square-to-disk homeomorphism is
**impossible** for the frozen model.  In `SurfaceRel false 2` the paired disk
arcs `(0,1)` and `(2,3)` are adjacent in cyclic order, whereas the square
action pairs opposite edges.  The sorry-free theorems
`KleinDiskClosedSquareCompatibleCarrier.no_carrier_with_required_boundary_formulas`
and
`KleinDiskClosedSquareRelationCompatibleCarrier.no_cyclic_relation_compatible_component_equiv`
formalize the obstruction.  The required map must therefore be a polygon
cut-and-paste map on quotient spaces, not a radial carrier homeomorphism.

#### `t96J02_kleinPlaneOrbitQuotient_t2`

**Statement.** The explicit plane-orbit quotient is Hausdorff.

**Proof route / Mathlib names.** Prove the orbit equivalence relation is
closed, using the local finiteness/proper discontinuity estimates already
proved above (or integer-coordinate separation), then use the quotient
Hausdorff criterion (`isClosed_orbitRel` / `Quotient.t2Space` APIs; search the
current Mathlib revision for `IsClosed` plus `T2Space (Quotient ...)`).  With
this instance,
`KleinClosedSquareOrbitInverseContinuity.closedSquareOrbitQuotientEquiv_continuous_symm_of_t2`
supplies inverse continuity.

**Estimate.** 50–100 lines. **Independent.** Degenerate boundary and corner
orbits are included because closedness is proved for the full plane relation.

#### `t96J02_kleinSquare_orbit_iff_eqvGen`

**Statement.** On the closed square, `closedSquareOrbitSetoid.r` is exactly
`EqvGen T96J02ClosedSquareRel`.

**Proof route / Mathlib names.** Unfold the two relations and combine
`KleinPlaneActionSquareOrbitClassification.sameOrbit_iff_cases` with
`KleinSquareEqvGenCasesIff.eqvGen_iff_cases`; the subtype bounds supply both
`InSquare` hypotheses.

**Estimate.** 15–30 lines. **Independent.** `EqvGen` handles corners and both
directions of the generating edge relation, avoiding an endpoint exception.

#### `t96J02_kleinClosedSquareOrbit_homeomorph_squarePolygon`

**Statement.** Given the preceding relation equality explicitly, the two
coinduced quotients of the same closed square are homeomorphic.

**Proof route / Mathlib names.** Define both directions by `Quotient.lift` of
the identity, discharge well-definedness with `hrel`, prove inverse laws by
`Quotient.inductionOn`, and prove continuity with
`Continuous.quotient_lift` and `continuous_coinduced_rng`.

**Estimate.** 35–60 lines. **Independent:** relation equality is a hypothesis.
The empty-carrier case would also work; here the square is visibly nonempty.

#### `t96J02_kleinSquarePolygonQuotient_homeomorph_diskPolygon` — LIBRARY

**Statement.** The quotient of the square by its opposite-edge Klein pairing
is homeomorphic to the frozen disk quotient `KleinBottle` (`aabb`).

**Required foundation.** This needs an explicit quotient-level polygon move:
cut the square quotient along a suitable diagonal/arc and reglue to the disk
`aabb` presentation, or invoke a proved polygon-word equivalence theorem.
No such theorem was found in the imported sorry-free modules.  A carrier
homeomorphism cannot prove it, by the obstruction above.  Useful quotient
tools after constructing the piecewise map are `Quotient.lift`,
`Continuous.quotient_lift`, the pasting lemma (`Continuous.if` or
`IsClosed.continuousOn_iff`), and compact-to-T2 inverse continuity.

**Estimate.** 200–400 lines, or 20–40 lines once a general polygon-move
library exists. **Independent.** This is the one deliberately retained
LIBRARY boundary.  Endpoint formulas must be checked in `EqvGen`, since all
four vertices collapse and raw generator relations are not symmetric.

#### `t96J02_kleinPlaneQuotient_homeomorph` (assembly, proved)

Compose the already-proved action-orbit identity adapter, the banked
closed-square fundamental-domain equivalence (using the T2 leaf), the
relation quotient adapter, and the quotient-level polygon move.  This theorem
itself is sorry-free.

### `t96J02_pi1_every_basepoint_of_homeomorph`

**Statement.** A homeomorphism transports an all-basepoint fundamental-group
calculation from its source to its target.

**Proof route / Mathlib names.** For `y`, apply `hX (e.symm y)` and compose
with the group equivalence induced by the continuous maps `e` and `e.symm`.
Use `FundamentalGroup.map`, `Homeomorph.continuous`,
`Homeomorph.continuous_symm`, and `FundamentalGroup.map_comp`; package the two
maps with `MulEquiv.ofBijective`, or use the existing induced equivalence API
if available in this Mathlib revision.

**Estimate.** 35–70 lines. **Independent:** both geometric conclusions are
explicit hypotheses.

**Truth check.** No path-connectedness is assumed or needed because the
source hypothesis covers every basepoint.  The inverse image `e.symm y`
exists even for disconnected or empty types (the universal target statement
is vacuous when `Y` is empty).

### `t96J02_kleinBottle_pi1` (assembly, proved)

Choose the quotient/Klein homeomorphism, feed the origin result to the
all-basepoint adapter, transport that family across the homeomorphism, and
specialize at `surfacePoint false 2`.  The proof contains no `sorry`.

### Finite-index subgroup classification (split into six leaves)

`t96J02_presented_coordinate m n` names the presented-group element whose
banked normal form is `(m,n)`.  It is a definition, not an axiom.

#### `t96J02_presented_finiteIndex_horizontal_step`

**Statement.** For finite-index `H`, the integers `m` for which `(m,0) ∈ H`
are exactly the multiples of a positive integer `p`.

**Proof route / Mathlib names.** Form the additive subgroup of `ℤ` cut out by
this membership condition (closure uses the coordinate multiplication law at
vertical coordinate zero). Apply `Int.subgroup_cyclic`, normalize its
generator with `Int.natAbs`, and use `Int.mem_zmultiples_iff`. To prove it is
nonzero, use finiteness of the cosets of `H`: among the finitely many cosets of
the horizontal powers, two coincide; `QuotientGroup.eq_iff_div_mem` gives a
nonzero horizontal difference in `H`. Useful finite pigeonhole tools are
`Finite.of_injective_forall_mem` / `Set.Finite.exists_ne_map_eq_of_infinite`;
alternatively use `Subgroup.finiteIndex_iff_finite_quotient` and
`Finite.exists_ne_map_eq_of_infinite`.

**Estimate.** 60–110 lines. **Independent.**

**Truth check.** Finite index rules out the zero additive subgroup. Choosing
`natAbs` makes `p > 0`; for `H = ⊤`, `p = 1`.

#### `t96J02_presented_finiteIndex_vertical_step`

**Statement.** The vertical exponents occurring in `H` are precisely `qℤ`
for a positive `q`.

**Proof route / Mathlib names.** This set is the range/image of the subgroup
under `SemidirectProduct.rightHom`; regard it as an `AddSubgroup ℤ`, then use
`Int.subgroup_cyclic`, `Int.zmultiples_natAbs`, and
`Int.mem_zmultiples_iff`. Nonzeroness again follows by applying finite-coset
pigeonhole to the vertical elements `(0,n)`. Coordinate products use
`SemidirectProduct.right_mul` (or `rfl` after changing through
`coordinateEquiv`).

**Estimate.** 55–100 lines. **Independent of the horizontal leaf.**

**Truth check.** The existential horizontal coordinate is essential: the
projection need not contain `(0,q)`. Finite index excludes `q = 0`.

#### `t96J02_presented_finiteIndex_choose_vertical_lift`

**Statement.** Given the complete projection characterization, some `(r,q)`
belongs to `H`.

**Proof route / Mathlib names.** Specialize the hypothesis at `n = q`; its
right side is `dvd_refl q`, then unpack the existential.

**Estimate.** 3–8 lines. **Independent:** the projection conclusion is an
explicit hypothesis.

**Truth check.** This remains true even at `q = 0`; positivity is deliberately
not smuggled into this leaf.

#### `t96J02_presented_finiteIndex_generated`

**Statement.** Given the exact horizontal intersection, exact vertical
projection, and a chosen `(r,q) ∈ H`, the two elements `(p,0)` and `(r,q)`
generate `H`.

**Proof route / Mathlib names.** Prove both subgroup inclusions with
`Subgroup.closure_le` and `Subgroup.le_closure`. For `x ∈ H`, write its
vertical coordinate as `k*q` using `hq`; multiply by the inverse of the
`k`th power of `(r,q)` so the vertical coordinate becomes zero; `hp` then
writes the remaining horizontal coordinate as a multiple of `p`. Use
`Subgroup.zpow_mem`, `Subgroup.mul_mem`, `Subgroup.inv_mem`,
`SemidirectProduct.ext`, and `Int.mem_zmultiples_iff`. The sign affecting the
first coordinate is irrelevant because `hp` handles the actual remainder.

**Estimate.** 80–140 lines. **Independent:** every earlier conclusion is an
explicit hypothesis.

**Truth check.** No positivity is required for the generation argument. The
statement is not vacuous: its conclusion is equality with a concrete
two-generator closure, not merely that those generators lie in `H`.

#### `t96J02_presented_finiteIndex_even_classify`

**Statement.** Positive nonzero steps and the concrete two-generator
description imply `H ≃* Multiplicative (ℤ × ℤ)` when `q` is even.

**Proof route / Mathlib names.** Define the homomorphism sending `(i,j)` to
`(p,0)^i (r,q)^j`. From `Even q`, powers of the vertical generator act
trivially on the horizontal coordinate; reuse the calculation pattern in
`t96J02_presented_torus_subgroup_aux_even_action` (`zpow_mul`, `one_zpow`).
Surjectivity follows from `hgen` and `Subgroup.closure_le`; injectivity follows
by applying `coordinateEquiv`, comparing the right coordinate to get `j=0`
from `q>0`, then the left coordinate to get `i=0` from `p>0`. Package with
`MulEquiv.ofBijective` (or `MonoidHom.ofInjective` plus its range equivalence).

**Estimate.** 100–150 lines. **Independent of all existence leaves.**

**Truth check.** The offset `r` causes no problem: even `q` makes conjugation
trivial, and the vertical coordinate still detects the second exponent.
Positivity excludes collapsed generators.

#### `t96J02_presented_finiteIndex_odd_classify`

**Statement.** Under the same concrete generation hypothesis, odd `q` gives
`H ≃* PresentedKleinGroup`.

**Proof route / Mathlib names.** Map the standard coordinate Klein group to
`H`, sending its horizontal generator to `(p,0)` and vertical generator to
`(r,q)`. Oddness gives the inversion action; prove it by writing
`q = 2*k+1` from `Odd q` and simplifying powers of `inversion` with
`zpow_add_one`, `zpow_mul`, and `inversion` squared. Use
`KleinPresentedGroupCoordinateNormalForm.coordinateEquiv` to define/check the
map. Surjectivity is `hgen`; injectivity compares the vertical coordinate
first (`q>0`) and the horizontal coordinate second (`p>0`). Package with
`MulEquiv.ofBijective`.

**Estimate.** 110–150 lines. **Independent of all existence leaves.**

**Truth check.** An arbitrary lift offset `r` still satisfies the Klein
relation: conjugation depends only on odd `q`. Normal-form coordinate
comparison prevents an extra kernel.

#### `t96J02_presented_finiteIndex_classify` (assembly, proved)

Obtain `p`, `q`, and `r`, apply the generation leaf, split with
`Int.even_or_odd q`, and invoke the matching classification leaf. The proof is
sorry-free; `#print axioms` reaches `sorryAx` only through the six leaves.

### `t96J02_presented_self_subgroup` (proved)

**Statement.** A finite-index subgroup isomorphic to the presented Klein
group exists.

**Why true.** Take `⊤`. Its quotient has one element, and
`Subgroup.topEquiv` supplies the isomorphism. The proof is included without
`sorry`.

**Estimate.** 4 lines, complete.

**Dependencies.** None.

**Truth check.** Its index is one. This also checks the theorem does not
require the witnesses to be proper.

### `t96J02_presented_torus_subgroup`

**Statement.** A finite-index subgroup of the presented Klein group is
isomorphic to `Multiplicative (ℤ × ℤ)`.

**Why true.** In semidirect coordinates take pairs whose second coordinate is
even. Closure follows because inversion preserves the first coordinate and
even plus even is even. Reduction of the action modulo parity makes its group
law componentwise; halving the second coordinate gives the desired
equivalence. The parity map to `ZMod 2` has this subgroup as kernel, so it has
index two.

**Estimate.** 100–220 lines.

**Dependencies.** None among blueprint lemmas; it can be built in parallel
with classification.

**Truth check.** The identity has even second coordinate; inverses and
products preserve evenness. The elements `(1,0)` and `(0,2)` commute and are
independent, while the parity quotient has exactly two cosets.

### `t96J02_transport_across_equiv`

**Statement.** An arbitrary group equivalence transports the classification
and both existence witnesses from one group to the other.

**Why true.** Map subgroups with `Subgroup.map e`; `MulEquiv.subgroupMap`
identifies their subtype groups. Equivalences of coset quotients preserve
`Finite`, hence finite index. For classification, map the input subgroup
forward and compose the returned subtype equivalence with the inverse ambient
equivalence in the Klein alternative. For existence, pull each supplied
subgroup back.

**Estimate.** 50–120 lines.

**Dependencies.** It accepts the complete conclusions of the other lemmas as
hypotheses, so its seat is independent.

**Truth check.** With `e = MulEquiv.refl G`, each mapped subgroup is the
original subgroup and all three conclusions reduce to the supplied
hypotheses. The top and index-two test subgroups retain indices one and two.

## Dependency layers

- Layer 1, fully parallel: the four geometric leaves; the horizontal and
  vertical step leaves; the lift, generation, even, and odd algebra leaves
  (their prerequisites are explicit hypotheses); `t96J02_presented_torus_subgroup`;
  and `t96J02_transport_across_equiv`.
- Layer 2: `t96J02_kleinBottle_pi1` and
  `t96J02_presented_finiteIndex_classify`, both sorry-free assemblies.
- Layer 3: the main theorem assembly, already complete and sorry-free.

The algebraic LIBRARY boundary is now six leaves: two finite-index step
arguments, one tiny choice leaf, one two-generator normal-form argument, and
two parity-specific equivalence constructions. No leaf assumes another leaf
as a theorem, so all six seats can work concurrently.

## Compile and axiom gate

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t96J02/Blueprint.lean
```

Output of `#print axioms apm_t96j02`:

```text
'apm_t96j02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The main theorem and both assembly theorems have no `sorry`; `sorryAx` enters
only through the ten unfinished top-level leaves (four geometric and six
algebraic).

## Cut-and-paste bridge (2026-10-14)

`t96J02_kleinSquarePolygonQuotient_homeomorph_diskPolygon` is now a sorry-free
assembly.  The design is in the Lean section `T96J02CutAndPaste`: an `I`-equivariant
radial chart from the disk to the ℓ¹ diamond, then a cut along the imaginary
axis with each half mapped affinely onto one triangle of the square.  Raw maps go
both ways (`t96J02_cut_raw`, `t96J02_paste_raw`).  The leaves are continuity
(`cut_continuous`, `paste_continuous`), compatibility with the generators
(`cut_rel`, `paste_rel`) and the two round trips (`paste_cut`, `cut_paste`), plus
the elementary facts `edge_zero_iff`, `edge_two_iff`, the chart's continuity, and
the vertex and corner classes.  Each geometric leaf receives the facts it needs as
explicit hypotheses.  Corner cases: on the disk, the vertex `I` (in the `a` case)
and `-1` (in the `b` case) map to square corners.  On the square, `t = 0` maps to
disk vertices.  In `paste_cut`, side `S3` of the diamond comes back as `-I • x`
(related by `b`).  In `cut_paste`, the top edge `v = 1` comes back as `(1-u, 0)`.
