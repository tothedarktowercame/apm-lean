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

### Mollification leaves

`apm_m01J04_mollify_exists_compact_core` (70--120 lines, independent): first
multiply by expanding smooth spatial cutoffs.  Use `ContDiffBump` (or the
standard Euclidean bump), the weak Leibniz calculation already used by
`apm_m01J04_test_mul_weakGradient_volume`, and `MemLp` dominated convergence.
This preliminary leaf is necessary because the registered auxiliary theorem
only assumes `support u.val ⊆ K` and `support u.grad ⊆ K`; it does **not** assume
that `K` is compact.  Keep the resulting compact set `C` inside `closure K`;
`Metric.cthickening_closure` then recovers exactly the requested support.  For
`d = 0`, take `w = u` and the singleton carrier.  Empty support gives `C = ∅`.

`apm_m01J04_mollify_exists_L2_kernel` (100--150 lines, independent,
**LIBRARY** if no packaged theorem is found): construct one normalized
`C^∞_c` approximate-identity kernel supported in `closedBall 0 delta` and apply
it simultaneously to `w.val` and `w.grad`.  Search the convolution API for an
`Lp` approximate-identity theorem.  If absent, use density via
`MemLp.exist_eLpNorm_sub_le`, uniform convergence for the continuous compactly
supported approximant, and Young's inequality (`eLpNorm_convolution_le`).
Normalize a `ContDiffBump`; positivity of `delta` avoids the zero-radius
degeneracy.  The statement is purely `L²` and does not assert a gradient
identity.

`apm_m01J04_mollify_convolution_weakGradient` (80--140 lines, independent):
show that the convolution of `w.grad` is the weak gradient of the convolution
of `w.val`.  Use `HasCompactSupport.contDiff_convolution_left`/the derivative
formula for convolution, Tonelli--Fubini, translation invariance of `volume`,
and `w.weakGradient` applied to the translated kernel/test function.  Check the
sign after the change of variables: the final identity has exactly the minus
sign in `apm_m01J04_H1.weakGradient`.  No boundary term occurs because both
kernel and test function are compactly supported.  For `d = 0`, the conclusion
is vacuous because there is no `i : Fin 0`.

`apm_m01J04_mollify_package` (50--90 lines, independent given its explicit
hypotheses): package the two convolved fields into `apm_m01J04_H1`.  Obtain
their `MemLp` facts from finite error plus `w.val_memLp`/`w.grad_memLp` (or
Young's inequality), smoothness from
`HasCompactSupport.contDiff_convolution_left`, compact support from convolution
of the two compact supports, and the carrier inclusion from
`apm_m01J04_support_convolution_subset_cthickening`.  Its error hypothesis is
literally the two summands of `H1dist`, so it contains no approximation theorem.

`apm_m01J04_mollify_error_transfer` (30--50 lines, independent): prove the
triangle inequality separately for value and gradient using
`eLpNorm_add_le`, convert finite `ENNReal` bounds with `ENNReal.toReal_add`, and
combine the two half-errors.  This is valid even when `eta ≤ 0` as an
implication (its hypotheses are then impossible); the caller supplies
`0 < eta`.

`apm_m01J04_core_exists_smooth_global_approx_aux_mollify` is now a sorry-free
assembly of these five leaves.  It uses `cthickening_subset_of_subset` to pass
from the compact carrier `C` to the closure of the original possibly
noncompact `K`, then uses `Metric.cthickening_closure`.
`apm_m01J04_core_exists_smooth_global_approx` remains the support-safe wrapper
which places that thickening inside `Ω`.

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

Review note (claude-14, 2026-10-14): `apm_m01J04_mollify_package` gained `(hC : IsCompact C)`. Without it the statement is false (C = univ: the convolution need not have compact support). The assembly passes `hCcompact` from the compact-core leaf.
