# Blueprint for m01J04

## Triage

Verdict: **true and faithful** (for the repaired smoothness order at commit
`5e475969d`).

The theorem retains the problem's three conclusions.  As already documented in
`Main.lean`, the explicit `apm_m01J04_HasRellichProperty` hypothesis is the
faithful replacement for the bounded-domain regularity tacitly used by the
informal solution.  The reopened change from outer order `⊤` (`C^ω`) to
`((⊤ : ℕ∞) : WithTop ℕ∞)` (`C^∞`) removes the accidental collapse of
compactly supported test functions in positive dimension.

I checked the main degeneracies.  For `d = 0`, the already proved branch makes
all gradient pairings zero.  For a zero multiplier, localization is the zero
record.  For a nonzero smooth bump whose support approaches the boundary of
`Ω`, the localized product need not itself have support compactly contained in
`Ω`; this is exactly why the remaining density lemma must first cut away small
level sets before mollifying.  This does not contradict the claim: the weak
gradient of a smooth function vanishes almost everywhere on its zero set, so
the discarded collar tends to zero in the encoded `H¹` distance.

No current solve-loop obstruction/refutation file or ledger entry was present.
All declarations from the current `Main.lean` were retained.  The first reset
proof, smoothness of convolution, has been restored with Mathlib's
`HasCompactSupport.contDiff_convolution_left`; it compiles for genuine
`C^∞` and therefore is not an admitted blueprint obligation.

## Remaining lemmas

### `apm_m01J04_localization_core_approx`

Cut the global localized Sobolev pair off to a positive level core
`{ε ≤ |φ|}`, with both value and gradient supported there, and make its
`H1dist` error arbitrarily small.  Estimated proof: 90--140 lines.

Use smooth one-variable cutoffs composed with `|φ|` (or preferably `φ²`, to
avoid differentiability of `abs` at zero), the already proved weak product
rule `apm_m01J04_test_mul_weakGradient_volume`, and `MemLp` dominated
convergence.  The collar-gradient term is justified by
`apm_m01J04_contDiff_aeDerivativeZeroOnZeroSet`; it is zero a.e. on `{φ=0}`.
This lemma is independent of the mollifier lemma.

### `apm_m01J04_core_exists_smooth_global_approx`

Mollify an arbitrary global encoded `H¹` pair whose value and gradient are
supported in one positive core.  Produce one smooth compactly supported global
record, supported in `Ω`, within any prescribed `H1dist` error.  Estimated
proof: 100--150 lines.  This lemma is independent of the cutoff lemma.

Use `apm_m01J04_test_levelSet_convolution_support`,
`apm_m01J04_globalLocalizedH1_contDiff_convolution` as the model for smoothness,
`HasCompactSupport.contDiff_convolution_left`, and
`MeasureTheory.support_convolution_subset`.  The analytic inputs are the
standard approximate-identity convergence in `L²` for both fields and the
distributional identity that the weak gradient of `κ * u.val` is
`κ * u.grad`.  If Mathlib has no packaged approximate identity with the
required raw-function interface, build the usual `ContDiffBump` kernel and
package that estimate locally; do not import any `SphereCap*` or
`LinearGraphMeasure` module.

### `apm_m01J04_localization_isH1Zero_of_core_approximations`

Diagonalize the preceding two epsilon statements, use the triangle inequality
for the two `eLpNorm` summands, and finish with
`apm_m01J04_localization_isH1Zero_of_globalApprox`.  Estimated proof: 35--70
lines.  Both analytic conclusions are explicit hypotheses, so this lemma is
independent and can be proved before either construction lands.

### Assembly

`apm_m01J04_localization_isH1Zero` is now sorry-free.  Its zero-multiplier
branch uses the proved helpers copied from the partial seat result; its nonzero
branch merely supplies the two new analytic lemmas to the diagonal assembly.

**Truth check.**  Besides the zero-dimensional and zero-multiplier checks
above, I checked the model one-dimensional case `Ω = (0,1)`, with a standard
smooth bump `φ` positive on `(0,1)` and flat at the endpoints.  Its positive
level sets are compact subintervals, hence admit the required convolution
margin.  The collar indicators shrink pointwise to the zero set, while `φ'`
vanishes there; dominated convergence gives precisely the two error terms in
the sketch.  This is also the mechanism covered abstractly by the already
compiled a.e.-derivative-zero lemma.

## Truth and degeneracy checks

For `φ = 0`, the copied helper gives the constant zero approximating sequence.
For `d = 0`, all gradient coordinates are empty and the same statements reduce
to scalar `L²` approximation on the one-point Euclidean space.  Positive level
cores are compact because they are closed subsets of `tsupport φ`; for
`ε > 0` they lie in the actual support, not merely its closure.  No boundary
point is lost: `apm_m01J04_test_levelSet_exists_cthickening` gives a positive
closed-thickening margin inside `Ω`.  The core lemma is not vacuous (it must
approximate the fixed global localized pair), and the mollifier lemma is not
overloaded with cutoff convergence.

The already proved declarations before this split contain the requested product
rule, including extension by zero to the whole Euclidean space:
`apm_m01J04_test_mul_weakGradient_volume` and
`apm_m01J04_globalLocalizedH1`.  Thus this was not duplicated as a new admitted
leaf.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m01J04/Blueprint.lean
```

The final output of `#print axioms apm_m01j04` was:

```text
'apm_m01j04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The remaining `sorryAx` paths are precisely the three new leaves above; the
registered main statement and all declarations imported from `Main.lean` are
unchanged.
