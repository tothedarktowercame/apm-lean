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

### `t96J02_kleinBottle_pi1` — LIBRARY

**Statement.** The fundamental group at the registered basepoint of the
frozen Klein polygon is isomorphic to the standard presented Klein group.

**Why true.** This is the t96J02 specialization of
`program-2026-10-13-polygon-surface-pi1`: van Kampen gives the two-generator
presentation with Klein boundary word, and the banked coordinate normal-form
equivalence identifies that presentation with `PresentedKleinGroup`.
Alternatively, the sorry-free affine route in `t93J03Closure.lean` combines
the free properly discontinuous plane action with
`freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv`; the remaining
comparison identifies its orbit quotient with the frozen polygon.

**Estimate.** 300–600 lines as an adapter if the shared polygon program is
available; much larger if van Kampen is rebuilt locally, hence LIBRARY.

**Dependencies.** None among blueprint lemmas.

**Truth check.** The two presented generators act as a unit translation and a
glide reflection. The banked coordinate equivalence is bijective, and action
freeness rules out an accidental quotient of the presented group. At the
chosen basepoint the stabilizer is trivial.

### `t96J02_presented_finiteIndex_classify` — LIBRARY

**Statement.** Every finite-index subgroup of the presented Klein group is
isomorphic to the Klein group or to `Multiplicative (ℤ × ℤ)`.

**Why true.** Transport through the banked equivalence
`coordinateEquiv : PresentedKleinGroup ≃* ZMul ⋊[inversion] ZMul`.
For a finite-index subgroup `H`, its projection to the second `ℤ` is
`mℤ` for some positive `m`, and its intersection with the first `ℤ` is
`kℤ` for some positive `k`. Choose an element over `m`; together with the
generator of the intersection it gives a unique normal form for `H`. If `m`
is even, conjugation is trivial and the subgroup is `ℤ²`; if `m` is odd,
conjugation is inversion and rescaling the two generators gives the Klein
group. This is one coherent algebra program: splitting it further would force
several seats to reproduce the subgroup normal-form construction.

**Estimate.** 400–800 lines; LIBRARY.

**Dependencies.** None among blueprint lemmas; it uses only the shared
definitions and the banked coordinate normal form.

**Truth check.** For `H = ⊤`, the projected step is `m = 1` (odd), giving the
Klein case. For the even-coordinate subgroup, `m = 2`, giving the abelian
case. Positivity of `k,m` follows from finite index and excludes the degenerate
zero subgroups.

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

- Layer 1, fully parallel: `t96J02_kleinBottle_pi1` (LIBRARY),
  `t96J02_presented_finiteIndex_classify` (LIBRARY),
  `t96J02_presented_torus_subgroup`, and
  `t96J02_transport_across_equiv`; `t96J02_presented_self_subgroup` is already
  complete.
- Layer 2: the main theorem assembly, already complete and sorry-free.

There are **five top-level blueprint lemmas**: two LIBRARY tasks, two ordinary
seat-sized tasks, and one completed lemma. I am convinced all statements are
true. The only material uncertainty is schedule/size: the geometric π₁
adapter depends on the shared polygon-surface program, and the subgroup
normal-form classification is a genuine 400–800-line algebra program rather
than a normal lemma seat.

## Compile and axiom gate

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t96J02/Blueprint.lean
```

Output of `#print axioms apm_t96j02`:

```text
'apm_t96j02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The main theorem has no `sorry`; `sorryAx` enters only through the four
unfinished top-level lemmas.
