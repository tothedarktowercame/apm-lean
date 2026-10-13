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

## Remaining lemma

### `apm_m01J04_localization_isH1Zero`

**Statement in words.**  If `φ` is a smooth compactly supported test multiplier
whose nonzero set lies in `Ω`, and `f` is represented by the custom weak-`H¹`
record, then the Leibniz product record `φ f` lies in the closure, for the custom
`H1dist`, of smooth compactly supported records supported in `Ω`.

**Why true.**  This is the local Friedrichs/Meyers--Serrin argument.  Choose
smooth scalar cutoffs `θ_j` which vanish where `|φ|` is small and equal one
where `|φ|` is at least twice that threshold.  The products
`(θ_j ∘ |φ|) · (φ f)` have support in a positive level set of `|φ|`.
`apm_m01J04_test_levelSet_exists_cthickening` then gives a positive convolution
margin inside `Ω`.  Mollify each truncated value with a smooth compact kernel
of smaller radius.  The weak Leibniz identity already proved in the file shows
that the prescribed gradient is the distributional gradient; convolution
commutes with this weak derivative.  Approximate-identity convergence in `L²`
for both the value and gradient fields gives convergence of the mollified
records.  Finally send the level threshold to zero.  Dominated convergence
handles the value and `φ grad f` terms.  The only delicate collar term uses
`apm_m01J04_contDiff_aeDerivativeZeroOnZeroSet`: `Dφ = 0` almost everywhere on
`{φ = 0}`, so the collar contribution also converges to zero.  Assemble the
sequence with `apm_m01J04_localization_isH1Zero_of_globalApprox` (or equivalently
the already proved epsilon-to-sequence interface).

Useful existing interfaces in this file are
`apm_m01J04_globalLocalizedH1`,
`apm_m01J04_globalLocalizedH1_contDiff_convolution`,
`apm_m01J04_H1restrict`,
`apm_m01J04_H1dist_restrict_le`,
`apm_m01J04_localization_isH1Zero_of_globalApprox`, and
`apm_m01J04_test_levelSet_convolution_support`.  The basic Mathlib ingredients
are `HasCompactSupport.contDiff_convolution_left`, support control through
`MeasureTheory.support_convolution_subset`, and the standard `L²`
approximate-identity/mollifier estimates (a seat may need to package the latter
as a local auxiliary lemma if the API is not already in the desired raw-function
form).

**Expected size.** 180--300 lines.  Most work is choosing the coupled
value/gradient mollifier and converting its two `L²` estimates into `H1dist`.

**Dependencies.** Only the definitions and proved declarations preceding it
in `Blueprint.lean`.  In particular, it does not depend on another admitted
lemma.

**Truth check.**  Besides the zero-dimensional and zero-multiplier checks
above, I checked the model one-dimensional case `Ω = (0,1)`, with a standard
smooth bump `φ` positive on `(0,1)` and flat at the endpoints.  Its positive
level sets are compact subintervals, hence admit the required convolution
margin.  The collar indicators shrink pointwise to the zero set, while `φ'`
vanishes there; dominated convergence gives precisely the two error terms in
the sketch.  This is also the mechanism covered abstractly by the already
compiled a.e.-derivative-zero lemma.

## Assembly and dependency layers

* **Layer 1:** `apm_m01J04_localization_isH1Zero` (one seat).
* **Layer 2 (already proved):** `apm_m01J04_bridge_1`, bridge sequence and
  divergence pairing, the principal-difference and compensated-pairing
  lemmas, and the final theorem.

The restored convolution-smoothness lemma and every other declaration compile
without `sorry`.  The sole `sorry` is the Layer 1 lemma, and the main theorem
contains no direct `sorry`.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m01J04/Blueprint.lean
```

The final output of `#print axioms apm_m01j04` was:

```text
'apm_m01j04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The single warning identifying `sorry` is at
`apm_m01J04_localization_isH1Zero`.
