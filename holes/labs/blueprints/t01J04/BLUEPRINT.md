# Blueprint for t01J04

## Triage and repair

Verdict: **unfaithful**, and the conventional manifold hypotheses also need one
explicit repair for the available (and standard) Sard argument.

The original problem asks for `f⁻¹(cl V)` to be a smooth manifold with boundary
*as a smooth submanifold of `X`*.  The old Lean predicate merely existentially
chooses an arbitrary atlas on the subtype.  It never relates that atlas to the
atlas of `X`.  Consequently it can certify an abstractly smoothable topological
manifold even when its inclusion is not smooth.  This is the defect identified
by `holes/labs/statement-registry/triage-1.md`; it is a faithfulness defect, not
a short logical counterexample to the old, weaker conclusion, so there is no
`Refute.lean`.

`RevisedMain.lean` makes the smallest conclusion-side repair recommended by the
registry.  Its predicate additionally says that `Subtype.val` is smooth and
that its manifold derivative is injective at every point.  Since the subtype
inclusion is already a topological embedding, this records an embedded smooth
manifold with boundary rather than an unrelated abstract atlas.

I also added `[SecondCountableTopology X]`.  The source uses the conventional
meaning of finite-dimensional manifold, which includes second countability.
Mathlib deliberately does not build that condition into `IsManifold`.  The
topology-contract STOP found that the exact Sard theorem needed here,
`T93A04ManifoldWork.null_critical`, requires this instance.  Without it an
uncountable disjoint union can invalidate the countable-union step behind Sard,
so silently omitting it would not give a justified true repair.  This is not a
hypothesis carrying the core conclusion.

Degenerate checks: when `n = 0`, `X` is discrete locally and every subtype is
again zero-dimensional; the inclusion derivative has zero-dimensional source
and is injective.  Empty preimages are harmless.  When `m = 0`, the only
neighborhood geometry is discrete and the same split remains valid.  Constant
maps cause no problem: for a small neighborhood either the closed preimage is
empty or all of `X`, both embedded manifolds with empty boundary.  The registry
defect is blocked by the repair because an arbitrary chosen atlas no longer
suffices: it must make the literal inclusion smooth with injective derivative.

## Definitions

`apm_t01J04_IsSmoothEmbeddedManifoldWithBoundary n X IX S ι` retains the old
zero/positive-dimensional model split.  In each branch it adds smoothness of
`ι` into `X` and pointwise injectivity of `mfderiv`.  No predicate is defined as
the final neighborhood-existence conclusion.

## Remaining lemmas

### `apm_t01J04_zero_dimensional_domain`

**Statement in words.** If the source dimension is zero, shrink the given
neighborhood and equip its closed-preimage subtype with the compatible
zero-dimensional embedded structure.

**Why true.** `RegularSpace Y` supplies a neighborhood `V` with
`closure V ⊆ U`.  A zero-dimensional boundaryless manifold is discrete, hence
so is the subtype.  Use singleton charts into `Fin 0 → ℝ`; all maps between the
resulting discrete zero-dimensional manifolds are smooth.  The derivative of
the inclusion has zero-dimensional domain, so it is injective.  This is exactly
the branch that the topology-contract diagnostic reports as compiled already;
its temporary fixture was not retained in the repository, so the blueprint
records the obligation rather than pretending to reuse unavailable code.

**Expected size.** 50–100 lines.

**Dependencies.** Definitions only.

**Truth check.** Empty and singleton subtypes were checked.  For every linear
map from `Fin 0 → ℝ`, injectivity is immediate because the domain is subsingleton.

### `apm_t01J04_positive_dimensional_regular_domain` — LIBRARY

**Statement in words.** For positive source dimension, choose a smaller
neighborhood whose closed preimage carries the literal compatible half-space
atlas and whose subtype inclusion is a smooth immersion.

**Why true.** Choose a target chart around `y`, shrink to a closed coordinate
ball inside `U`, and set `h(x)=‖chart(f x)-chart(y)‖²` on the relevant open
source.  Apply Sard to select a positive regular value below the radius bound.
The regular-sublevel theorem gives half-space charts on `{h ≤ a}`.  Transport
them across the equality with `f⁻¹(cl V)`.  In those charts the inclusion is the
standard half-space inclusion, so it is smooth with injective derivative.

The Sard null-critical-value component is available from the sorry-free
`ConstructionTargets.SardGenuineSmoothManifoldVector` module as
`T93A04ManifoldWork.null_critical`.  What is still missing is the large combined
regular-sublevel package: selection of a regular radius, construction and
transport of the actual `EuclideanHalfSpace n` atlas, and its compatibility
with `Subtype.val`.  This is the precise STOP reported by the topology loop
(“regular-preimage, half-space-atlas and normal-translation applicability”).
It is honestly one foundational differential-topology result, estimated above
300 lines, so it is marked LIBRARY rather than split into fake adapter lemmas.

**Expected size.** 500–1000 lines / foundational program.

**Dependencies.** Definitions and the imported sorry-free Sard module.  It is
independent of the zero-dimensional lemma.

**Truth check.** For a constant map, every positive radius is regular because
the selected level is empty, yielding either the empty subtype or all of `X`.
For `f = id : ℝ → ℝ`, choosing `V=(-r,r)` produces `[-r,r]`, whose endpoint
charts are the two orientations of the half-line.  At `r>0`, the squared-radius
derivative is nonzero on both boundary points.  These checks also catch the
forbidden endpoint `a=0`, which the lemma must not choose.

## Assembly and dependency layers

The main theorem performs `by_cases n = 0`.  It invokes the zero-dimensional
lemma in the first branch and installs `NeZero n` before invoking the LIBRARY
lemma in the second.  The main theorem contains no `sorry`.

* **Layer 1 (parallel):** `apm_t01J04_zero_dimensional_domain` and
  `apm_t01J04_positive_dimensional_regular_domain`.
* **Layer 2 (already compiled):** `apm_t01j04` assembly.

There are **2 lemma obligations**, one ordinary and one LIBRARY obligation.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t01J04/RevisedMain.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t01J04/Blueprint.lean
```

The final output of `#print axioms apm_t01j04` is:

```text
'apm_t01j04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two `sorry` warnings are exactly the two top-level lemma obligations.  The
main theorem has no direct `sorry`.
