# Blueprint for a00J04

## Triage verdict: true and faithful

The current statement correctly formalizes “at most `N+1` components” as

```lean
ENat.card (ConnectedComponents ↥((lemniscate p)ᶜ)) ≤ p.natDegree + 1
```

The subtype is necessary to give the complement its subspace topology, and
`ENat.card`—unlike `Nat.card`—does not silently return zero for an infinite
component type. The hypothesis `0 < p.natDegree` exactly captures the source's
`N≥1` and excludes constant and zero polynomials.

Degenerate checks:

- for `p(z)=z`, the lemniscate is the unit circle and its complement has two
  components, attaining `natDegree p + 1 = 2`;
- for `p(z)=z^N`, there are still two components, safely below `N+1`;
- constant polynomials could have zero, one, or otherwise degenerate level-set
  behavior, but are deliberately outside the source and formal hypotheses;
- repeated roots do not inflate the bound because labels use
  `roots.toFinset`, i.e. distinct roots.

The file already contains compiled proofs of all analytic and topological
ingredients: component openness and frontier containment, sublevel/superlevel
classification, boundedness of the sublevel, the maximum/minimum modulus
arguments, root-counting, path connectedness of a strict exterior region, and
uniqueness of the superlevel component.

## Added definition

`rootLabels p := ↥(Polynomial.roots p).toFinset` is the finite type of distinct
roots. The extra `Unit` summand in the remaining lemma is the single label for
the superlevel component.

## Remaining lemma

### `exists_component_label_injection`

**Statement.** There is an injection from the connected components of the
lemniscate complement into `rootLabels p ⊕ Unit`.

**Proof sketch.** Use `ConnectedComponents.surjective_coe` to choose a point
representing each component. Apply the proved
`componentSet_subset_superlevel_or_sublevel` dichotomy.

- In the superlevel case, assign `Sum.inr ()`.
- In the sublevel case, use
  `exists_root_in_componentSet_of_subset_sublevel` and classical choice to
  assign a root lying in that component, packaged as `Sum.inl`.

For injectivity, two components carrying the right marker are equal by the
proved `component_eq_of_subset_superlevel`. Two components carrying the same
root have a common point and are equal by
`componentSet_eq_of_common_point`. Mixed labels cannot be equal by disjointness
of the sum constructors. When changing chosen representatives, use
`ConnectedComponents.coe_eq_coe` and the existing component-set equality
lemmas; alternatively define the label by quotient lifting and discharge
well-definedness with those same facts.

**Estimate.** 120--220 lines.

**Dependencies.** Only the definitions and already compiled helper lemmas in
`Blueprint.lean`.

**Truth check.** The labeling is exactly the paper counting argument. A root
cannot label two distinct components because it would belong to both disjoint
connected components. All superlevel components collapse to one by the
compiled exterior-region argument. For `p(z)=z`, the labels are its sole root
and the `Unit` marker, matching the two actual components.

## Main-theorem assembly

The main theorem is already proved from the injection:

1. `ENat.card_le_card_of_injective` bounds the component cardinality by the
   label type.
2. `ENat.card_eq_coe_fintype_card` and `Fintype.card_sum` compute its cardinal
   as `roots.toFinset.card + 1`.
3. The compiled `card_roots_le_degree` finishes the bound.

These Mathlib declarations were checked directly with `#check`.

## Dependency layers

- **Layer 1:** `exists_component_label_injection`.
- **Layer 2:** the already completed `ENat.card` calculation in the main
  theorem.

There is only one genuine remaining proof target: all sensible subpieces of
the encoding/injectivity proof are short and tightly coupled to the same
choice function, so splitting them would create more interface plumbing than
parallel work.

## Confidence and doubt

I am convinced the remaining lemma is true; every mathematical ingredient it
needs already compiles. The only uncertainty is Lean quotient engineering:
defining a label on `ConnectedComponents` may be smoother by choosing
representatives with `ConnectedComponents.surjective_coe` than by a quotient
lift. This is an implementation choice, not a statement-level doubt.

## Compile gate and axioms

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/a00J04/Blueprint.lean
```

Output of `#print axioms connectedComponents_complement_lemniscate_le`:

```text
'ApmCanaries.A00J04.connectedComponents_complement_lemniscate_le' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The main theorem has no `sorry`; `sorryAx` enters only through
`exists_component_label_injection`.
