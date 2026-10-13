# Blueprint for t99A02

## Triage and repair

Verdict: **unfaithful (the registered theorem is true, but it does not encode
the requested answer).**

The source asks for sketches of the universal covers of
`RP² ∨ RP²` and `S¹ ∨ RP²`.  The old Lean conclusion instead says that
three displayed relators become the identity in their own presented groups,
and that the second presented group is infinite.  In particular, the old
statement says neither that the first group is infinite nor what either group
is.  Each of its three equations is immediate from the definition of
`PresentedGroup`, because the word asserted to equal one is itself a member of
the relation set.  Thus those equations cannot distinguish these presentations
from unrelated presentations containing the same relators.

This agrees with the outside triage in
`holes/labs/statement-registry/triage-3.md`.  There was no cached solve-loop
attempt, problem-specific solve-loop record, topology-contract row, or closer
audit to reuse.

`RevisedMain.lean` makes the smallest repair recommended by that triage: it
keeps both concrete presentations and replaces the four-conjunct conclusion by
the two group identifications

* `<a,b | a²,b²> ≅ D∞`, and
* `<a,b | b²> ≅ ℤ * (ℤ/2)`.

These are the algebraic data underlying exactly the two Cayley/Bass--Serre
pictures in `informal-solution.md`: the first gives a bi-infinite alternating
line, while the second gives the Bass--Serre tree for `ℤ * (ℤ/2)`.  Lean's
current topology library does not provide a projective-plane wedge plus the
explicit tree-of-spheres covering model, so the repaired statement uses the
registry's stated minimum faithful content rather than inventing a predicate
whose definition contains the desired conclusion.

The grader's objection is removed: neither conjunct follows merely because a
relator belongs to the relation set, and the first conjunct now implies the
missing infinitude through `Infinite (DihedralGroup 0)`.

## Remaining lemmas

### `t99A02_rp2WedgeRp2_presentedGroup_equiv` (LIBRARY)

**Statement in words.** The group on two generators, each of order dividing
two, is isomorphic to the infinite dihedral group.

**Why true.** Map the two presented generators to the two standard reflections
`sr 0` and `sr 1` in `DihedralGroup 0` using `PresentedGroup.toGroup`.  In the
reverse direction, use the normal form `r n` or `sr n`, sending rotation to the
product of the two presented involutions and reflection to an involution.
Prove the two composites on generators with `PresentedGroup.ext`; the
`DihedralGroup` normal forms prove the other composite.  Relevant checked APIs
are `PresentedGroup.toGroup`, `PresentedGroup.ext`, `FreeGroup.lift`, and the
constructors/normal form of `DihedralGroup`.

**Expected size.** 300--500 lines.  This is marked LIBRARY because Mathlib has
no packaged equivalence between this presentation and `DihedralGroup 0`; the
normal-form/inverse proof is a reusable presentation theorem rather than a
small problem-specific adapter.  No sorry-free `ConstructionTargets` module
currently supplies it.

**Dependencies.** Definitions only.

**Truth check.** The standard hand normal form alternates the two involutions:
every reduced word is uniquely `(ab)^n` or `b(ab)^n`.  At the degenerate word,
the empty word maps to `r 0 = 1`.  The target is genuinely infinite because
`DihedralGroup 0` has Mathlib's `Infinite` instance, so this also catches the
content absent from the old theorem.

### `t99A02_circleWedgeRp2_presentedGroup_equiv` (LIBRARY)

**Statement in words.** The group on one unrestricted generator and one
involutory generator is the free product `ℤ * (ℤ/2)`.

**Why true.** Send generator `0` to the canonical image of `1 : ℤ` in the
left factor and generator `1` to the canonical image of `1 : ZMod 2` in the
right factor; the sole relator maps to one, so `PresentedGroup.toGroup`
descends the map.  Conversely, map the left cyclic group by integer powers of
presented generator `0`, the right cyclic group to generator `1`, and combine
them with `Monoid.Coprod.lift`.  Use `PresentedGroup.ext` and
`Monoid.Coprod.hom_ext` to show the composites are identities.  The relevant
universal-property APIs are all present in Mathlib.

**Expected size.** 250--400 lines.  This is marked LIBRARY because the missing
piece is a general presentation/free-product comparison, with coercion and
cyclic-group homomorphism work, not a short invocation of an existing theorem.
No sorry-free `ConstructionTargets` module currently supplies it.

**Dependencies.** Definitions only.

**Truth check.** With the second generator set to the nonzero element of
`ZMod 2`, its square is zero/additively (one/multiplicatively), so the relation
is satisfied.  Generator `0` has no relation and therefore supplies the
infinite cyclic factor.  Reduced free-product words give injectivity; the empty
word supplies the identity endpoint.  This also confirms that no accidental
extra relation makes the group finite.

## Assembly and dependency layers

The final theorem is a two-line pairing of the two equivalences and has no
direct `sorry`.

* **Layer 1 (parallel):**
  `t99A02_rp2WedgeRp2_presentedGroup_equiv`,
  `t99A02_circleWedgeRp2_presentedGroup_equiv`.
* **Layer 2 (already proved):** `apm_t99a02`, after both Layer 1 lemmas.

There are **two** remaining lemmas, both independent LIBRARY obligations.

## Compilation and axioms

Both files compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t99A02/RevisedMain.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t99A02/Blueprint.lean
```

The final output of `#print axioms apm_t99a02` was:

```text
'apm_t99a02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two `sorry` warnings are exactly the two Layer 1 library lemmas.  The main
theorem contains no `sorry` of its own.
