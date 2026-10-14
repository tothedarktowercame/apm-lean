# Blueprint for t96J06

## Triage

Verdict: **true and faithful**.  The registered Lean theorem has exactly the
source's concrete inclusion `RP¹ × RP¹ ⊂ RP² × RP²`; `RP¹` is the
projectivization of the coordinate plane `x₂ = 0`.  Its bounding predicate asks
for a compact subset carrying a three-dimensional manifold-with-boundary
structure whose intrinsic boundary has exactly the requested ambient image.

I tried the relevant degeneracies.  The proved coordinate witness shows that
the product subspace is nonempty.  The proved off-line witness shows it is not
the entire ambient product.  The representative calculation
`apm_t96j06_mk_pair_mem_ProductSubspace_iff` confirms that it is the intended
codimension-two locus, not an empty or malformed projectivization.  Empty `W`
cannot have this nonempty boundary image.  The obstruction is also insensitive
to nonorientability because it uses coefficients in `ZMod 2`.

No solve-loop refutation or revision was present.  The topology audit records
the same route: the product class has odd mod-two self-intersection, whereas an
ambient image of a compact three-manifold boundary is null-homologous.

## Reused compiled work

`Blueprint.lean` retains, with proofs, the explicit coordinate point and
off-line point, nonemptiness and properness of the product subspace, and the
representative-level membership equivalence from `Main.lean`.  These facts
rule out vacuous encodings and expose the two coordinate equations needed in a
geometric intersection construction.

## Remaining lemma

### `apm_t96J06_projectiveProduct_boundaryObstruction` — LIBRARY

**Statement in words.** For every compact subset `W` of the concrete product
of projective planes, and every three-dimensional topological
manifold-with-boundary chart structure on `W`, the ambient image of its
intrinsic boundary is not the product of the two coordinate projective lines.

**Why true.** Give the ambient product and the embedded projective torus their
mod-two fundamental classes.  If the latter were the intrinsic boundary image
of `W`, its ambient `H₂(-; ZMod 2)` class would vanish.  On the other hand, a
second projective line in each factor meets the coordinate line transversely
in one point.  The product formula gives one intersection point for the two
product cycles, so the displayed product class pairs nontrivially and cannot
vanish.  This is precisely the informal solution's self-intersection
argument.

This is deliberately one program-sized lemma rather than several fake small
lemmas.  Its hard part is not coordinate bookkeeping: it requires mod-two
fundamental classes for topological manifolds with boundary, compatibility of
the intrinsic boundary class with the ambient inclusion, a singular-chain
cross product/Künneth comparison, and the projective-line pairing.  Splitting
those into blueprint seats would produce obligations far beyond the requested
30–150 line sessions, with no existing API connecting their conclusions.

**Expected size.** 3,000–7,000 lines overall (several weeks to months), based
on the topology audit.  The final adapter after the infrastructure exists is
20–50 lines.

**Dependencies.** None inside this blueprint.  The topology program should
provide the chain `ProjectivePlaneMod2Homology.degreeOneGenerator`,
`SingularCrossProduct.eilenbergZilber`,
`ManifoldBoundaryFundamentalClass.mod2BoundaryClass`, and finally
`ProjectivePlaneProductPairing.boundaryObstruction`.  The last theorem should
be delivered in exactly the Lean statement used here.

**Truth check.** Two distinct real projective lines are represented by two
distinct two-planes in `ℝ³`; their intersection is a one-dimensional vector
space and hence one projective point.  Taking products therefore produces
exactly one intersection point mod two.  Conversely, a boundary chain has
zero homology class because its boundary is the boundary of the mod-two
fundamental chain of `W`.  This checks both sides of the contradiction.  The
tests above separately exclude empty-space and whole-space accidents in the
Lean encoding.

**Repository search.** I searched every sorry-free `ConstructionTargets/*.lean`
for projectivization, projective homology, intersection pairings, fundamental
classes, singular cross products, bordism, and boundary homology.  The
available sorry-free modules include useful singular-chain, excision, and
Mayer–Vietoris machinery, but none supplies the RP² mod-two generator,
Eilenberg–Zilber product detector, or manifold-boundary fundamental-class
bridge.  Thus no ConstructionTargets import closes or materially shortens
this exact lemma.  This agrees with the STOP audit in
`~/notes/closer/audits/t96J06.{md,edn}`.

## Assembly

The main theorem simply unpacks a proposed bounding `W` and applies the
library obstruction.  Its proof contains no `sorry`.

## Dependency layers

* **Layer 1:** `apm_t96J06_projectiveProduct_boundaryObstruction` (LIBRARY;
  topology program).
* **Layer 2:** the already compiled main-theorem adapter.

There is one admitted lemma.  I have no doubt about its mathematical truth,
but its formalization cost is genuinely large and the current repository does
not contain the necessary boundary/intersection API.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t96J06/Blueprint.lean
```

The only `declaration uses sorry` warning is the LIBRARY lemma.  The final
output of `#print axioms apm_t96j06` is:

```text
'apm_t96j06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
