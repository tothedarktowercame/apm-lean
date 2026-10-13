# Blueprint for t97A07

## Triage

Verdict: **true and faithful as registered**.

The raw printed problem incorrectly claims nonemptiness also for `n = 0`:
the unique map to `ℝ⁰` has surjective derivative everywhere, so its critical
value set is empty.  The registered Lean theorem explicitly exposes this
exception, asserting nonemptiness only when `0 < n` and emptiness when
`n = 0`.  The batch instruction declares that corrected registered statement
faithful, so no further repair is made.

I checked the main degeneracies.  For `n = 0`, `criticalValues_zero` proves
the set empty.  A constant map with `0 < n` has zero derivative and hence its
singleton image is the nonempty compact critical-value set; it is excluded
from the infinitude conjunct.  For `n = 1`, finite critical-value sets occur
(for example a height function on a circle), and the theorem correctly asks
for `1 < n`.  Empty `X` is excluded by `[Nonempty X]`.

The topology closure program has already proved, without `sorry`, all of the
manifold-analysis foundations in `ConstructionTargets/t97A07Closure.lean`:
openness of surjective finite-dimensional continuous linear maps, continuity
of the chart-transported manifold derivative, openness of regular points,
compactness of the critical image, the coordinate-maximum critical-point
argument, and local surjectivity/open image at a regular point.  `Blueprint.lean`
reuses those proofs and leaves only the final topological argument.

## Proved adapters

### `t97A07Blueprint.isCompact_criticalValues`

This rewrites the existential definition of `criticalValues` as the image of
the critical-point set and applies the sorry-free theorem
`t97A07Closure.isCompact_image_criticalPoints`.

### `t97A07Blueprint.criticalValues_nonempty_of_pos`

This applies the sorry-free coordinate-maximum theorem
`t97A07Closure.exists_not_surjective_mfderiv_of_pos` and takes the image of
the resulting critical point.

## Remaining lemma

### `t97A07Blueprint.criticalValues_infinite_of_one_lt_of_nonconstant`

**Statement in words.** A nonconstant smooth map from a nonempty compact
connected manifold into `ℝⁿ`, for `n > 1`, has infinitely many critical
values.

**Why true.** Let `C` be the set of critical values and assume it is finite.
Mathlib's `Set.Countable.isConnected_compl_of_one_lt_rank` makes `Cᶜ`
connected because `1 < n` (convert this to `1 < Module.rank ℝ (E n)`).
Set `A = Set.range f ∩ Cᶜ`.

If `A` is empty, then `range f ⊆ C`.  The range is connected because `X` is
connected and `f` is continuous, while it is finite because `C` is finite.
A finite connected set is a singleton, contradicting the two supplied points
with unequal images.

If `A` is nonempty, it is relatively closed in `Cᶜ`: the range of `f` is
compact, hence closed in Euclidean space.  It is relatively open as well.  If
`y = f x ∈ Cᶜ`, then `y` not being critical says that every preimage,
including `x`, has surjective `mfderiv`; the proved theorem
`t97A07Closure.range_mem_nhds_of_regular f hf x` gives
`Set.range f ∈ 𝓝 y`.  Connectedness of `Cᶜ` forces `A = Cᶜ`.
But `range f` is compact and bounded, whereas the complement of a finite set
in the nontrivial Euclidean space `E n` is unbounded.  This contradiction
proves `C` infinite.

Useful checked APIs are the imported
`Set.Countable.isConnected_compl_of_one_lt_rank`, `IsPreconnected.image`,
`IsCompact.isClosed`, `IsCompact.isBounded`, and the proved closure theorem
`t97A07Closure.range_mem_nhds_of_regular`.  The implementation may instead
express the nonempty clopen subset as a separation of `Cᶜ`; that is the same
argument.

**Expected size.** 100–150 lines.

**Dependencies.** Only the definitions and sorry-free imported foundation;
it does not depend on either proved adapter above.  In particular, compactness
of `range f` follows directly from `hf.continuous` and compactness of `X`.

**Truth check.** For a constant map the conclusion would be false (one
critical value), exactly explaining `hnotconst`.  For `n = 1`, the complement
of finitely many points need not be connected, exactly explaining `hn`.  If
there are no attained regular values, the first branch reduces the claim to
the elementary fact that a connected non-singleton finite image is impossible.
If there is an attained regular value, local surjectivity supplies a genuine
relative neighbourhood and prevents a boundary-point loophole.

## Dependency layers

* **Layer 1:**
  `t97A07Blueprint.criticalValues_infinite_of_one_lt_of_nonconstant`.
* **Layer 2 (already compiled, no seat):** the final `apm_t97a07` adapter,
  using the Layer 1 lemma plus the two proved adapters and
  `T97A07.criticalValues_zero`.

There is one remaining lemma and therefore no artificial parallel split.  Its
shared analytic dependency has already been factored into the sorry-free
`ConstructionTargets.t97A07Closure` module.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t97A07/Blueprint.lean
```

The final output of `#print axioms apm_t97a07` was:

```text
'apm_t97a07' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The single warning identifying `sorry` is exactly
`criticalValues_infinite_of_one_lt_of_nonconstant`.  The final theorem and
all adapter declarations have no direct `sorry`.
