# Blueprint for m98J02

## Triage

Verdict: **true and faithful after the documented source repair**.

The source's PDE clause assumes only `f ∈ C²(ℝ²)` but invokes the convolution
construction from the preceding parts, which requires one factor to have
compact support.  The formal statement adds `IsCompact (tsupport f)`, exactly
the condition used by the supplied informal solution.  It otherwise uses
genuine Mathlib test functions and distributions rather than replacing them
with ordinary functions.

I checked the principal degeneracies and signs:

* The zero distribution has compact support (empty witness), and convolution
  with it is consistently zero.
* Empty or disjoint supports make the defining distribution pairing vanish.
* The adjoint changes the sign of the first-order `-∂y` term and preserves the
  second-order signs, giving `2∂x² + ∂y + 3∂x∂y` as encoded.
* The regular constant distribution is nonzero but all derivatives in the
  operator vanish, so it supplies a genuine homogeneous solution.
* For `f = 0`, the construction may choose the zero solution, and adding the
  constant distribution still proves nonuniqueness.

The canonical obstruction explicitly says no refutation was found.  The main
regularity claim is consistent with the fundamental-solution method under the
added compact-support hypothesis.

## Reused completed work

The cached attempt is retained through its compiled constructions of:

* smooth cutoffs equal to one on arbitrary compact sets;
* compactly supported regular distributions induced by continuous functions;
* the nonzero regular constant distribution;
* translated test functions;
* bundled coordinate derivatives and the bundled formal adjoint;
* support closure under linear operations; and
* addition of a homogeneous solution to an inhomogeneous one.

The main theorem's convolution-existence and PDE assembly are proved from the
four obligations below, with no direct `sorry`.

## Remaining lemmas

### `apm_m98J02_bridge_2`

**Statement in words.** If `u` vanishes off a compact set `K`, then for every
distribution `v` there is a distribution satisfying the encoded convolution
pairing.

**Why true.** Obtain the compiled cutoff `χ = 1` on `K`.  For a test function
`φ`, define

`Ψφ(x) = χ(x) · v(apm_m98J02_translateTest x φ)`.

First prove smooth dependence on `x`: locally, translated test functions lie
in one fixed compact-support stage, and their difference quotients converge
in every stage seminorm.  Applying the continuous functional `v` preserves
these derivatives.  Multiplication by `χ` gives compact support.  Next show
`φ ↦ Ψφ` is continuous on every fixed-support stage; compose it with `u` and
use `TestFunction.mkCLM` to construct `w`.  The cutoff, translation, and
pairing clauses then follow by construction.  The compiled
`apm_m98J02_bridge_1`, `apm_m98J02_translateTest`, and Mathlib's
`TestFunction.mkCLM` are the intended APIs; all occur in the compiling file.

**Expected size:** 240–340 lines.

**Dependencies:** proved definitions and lemmas only.

**Truth check:** for `u = 0`, take `w = 0`; for `v` equal to point evaluation,
the inner pairing reduces to the ordinary translated value `φ(x)` and the
formula becomes an ordinary compactly supported integral/pairing.

### `apm_m98J02_regular_convolution_is_C2`

**Statement in words.** Any distribution satisfying the encoded convolution
of the compactly supported regular distribution induced by `f ∈ C²` with
`w₀` is represented by a `C²` function.

**Why true.** For each translation parameter, use the convolution identity
and move derivatives of order at most two onto `f`.  Compact support of `f`
keeps all translated derivatives in common compact stages locally, so
continuity of `w₀` gives continuous derivatives of the scalar pairing.  Define
`g` by that pairing, prove `ContDiff ℝ 2 g`, and use Fubini plus cutoff
independence to show `w φ = ∫ gφ`.  The already bundled coordinate derivative
test functions eliminate the remaining support bookkeeping.

**Expected size:** 220–320 lines.

**Dependencies:** definitions and compiled regular-distribution/translation
infrastructure only; the lemma assumes the convolution predicate and can be
proved independently of `bridge_2`.

**Truth check:** when `w₀` is Dirac evaluation, the pairing recovers a reflected
or translated copy of `f`, visibly `C²`.  When `f = 0`, it recovers zero.

### `apm_m98J02_convolution_solves_fundamental`

**Statement in words.** Convolving the regular distribution of `f` with a
fundamental solution `w₀` produces a distributional solution of `Tw=f`.

**Why true.** Test against `φ` and use
`apm_m98J02_formalAdjointTest φ`.  Expand the convolution pairing, commute its
coordinate derivatives through translation, and apply `hw₀` to the translated
adjoint test function.  The result is evaluation at zero, hence the original
regular pairing `∫fφ`.  Cutoff independence follows because `f` is supported
inside the compact support witness.

**Expected size:** 180–280 lines.

**Dependencies:** definitions and compiled bundled-adjoint infrastructure
only; it assumes a convolution witness and is independent of the preceding
two proof obligations.

**Truth check:** formally this is the identity
`T(f*w₀) = f*(Tw₀) = f*δ₀ = f`.  For zero `f`, every pairing reduces to zero.

### `apm_m98J02_constantDistribution_homogeneous`

**Statement in words.** The nonzero regular distribution induced by the
constant function one solves the homogeneous equation.

**Why true.** Choose the compiled formal-adjoint test function.  Its integral
is zero: each coordinate derivative of a compactly supported smooth function
has zero integral, proved by Fubini and the one-dimensional fundamental
theorem; apply this once to the first-order term and iteratively to both
second-order terms.  Then use
`apm_m98J02_constantDistribution_apply`.

**Expected size:** 90–160 lines.

**Dependencies:** definitions and proved bundled-adjoint/constant-distribution
lemmas only.

**Truth check:** classically `T(1)=0`; every term contains at least one
derivative.  The compiled lemma proving the constant distribution nonzero
ensures this is not a vacuous homogeneous witness.

## Dependency layers

* **Layer 1 (parallel):** all four lemmas above.  The last three accept an
  abstract convolution witness where needed and do not depend on the proof of
  `bridge_2`.
* **Layer 2 (already proved):** instantiate the regular distribution, obtain a
  convolution from `bridge_2`, obtain its `C²` representative and PDE identity,
  then add the constant homogeneous distribution.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m98J02/Blueprint.lean
```

The final output of `#print axioms apm_m98j02` was:

```text
'apm_m98j02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The four warnings are exactly the four Layer 1 lemmas.  The main theorem has
no direct `sorry`.

## Doubt

The statements are mathematically standard and I found no counterexample.
The largest implementation risk is `apm_m98J02_bridge_2`: continuity of the
two-level translated pairing in Mathlib's LF topology may exceed one session
unless its fixed-support-stage argument is factored into local helper lemmas.
