# Blueprint for m99J06

## Triage

Verdict: **true and faithful after the documented model repairs**.

The current model stores weak derivatives in Mathlib's `L²` quotient, avoiding
the inconsistency of treating almost-everywhere equal derivative
representatives as distinct.  It also states weak convergence only for a
subsequence, which is exactly what the boundedness argument in the supplied
solution proves.

I checked the principal degeneracies:

* If `H` is trivial, the model can exist only when its realization axiom is
  compatible with a trivial `H¹₀`; the theorem's conclusions then reduce
  correctly.
* For `f = 0`, every Galerkin solution is zero by the compiled uniqueness
  argument, the norm bound is exact, and the constant zero subsequence solves
  the weak problem.
* For `V n = {0}`, finite-dimensional existence is still valid, though such a
  family cannot satisfy the density hypothesis unless `H` is trivial.
* Repeated subspaces are allowed by `V n ≤ V(n+1)` and do not affect the
  eventual-membership argument.
* Altering a derivative representative on a singleton does not alter its `Lp`
  element, so the repaired model does not distinguish null-set changes.

No solve-loop counterexample was recorded.

## Reused completed work

The cached attempt is preserved through compiled proofs that `H¹₀` pairs are
closed under zero, addition, and scalar multiplication; the model maps
preserve zero and addition; inner-product component products are integrable;
represented fields determine the Hilbert element uniquely; realizations are
unique; and Galerkin solutions are unique.

## Remaining lemmas

### `apm_m99J06_weak_iff_strong`

**Statement in words.** In the repaired one-dimensional `H¹₀` model, the weak
variational equation is equivalent to existence of an `L²` second derivative
satisfying `u-u''=f` almost everywhere.

**Why true.** For strong-to-weak, select the `L²` representatives of `u'` and
`u''`, integrate by parts using absolute continuity of both `u` and `u'`, and
use the zero endpoint trace of the test element.  Match the resulting
integrals with `M.inner_eq`.

For weak-to-strong, test first against realizations of compactly supported
smooth functions.  The weak equation identifies the distributional derivative
of the chosen representative of `u'` with `u-f ∈ L²`.  Apply the
one-dimensional fundamental theorem/absolute-continuity characterization to
obtain an absolutely continuous representative of `u'` with derivative
`u-f`; this supplies the witnesses in `apm_m99J06_strongSolution`.

**Expected size:** 230–330 lines.

**Dependencies:** definitions and proved model algebra only.

**Truth check:** for `f=0,u=0` both predicates hold.  For a smooth endpoint-zero
function, ordinary integration by parts gives exactly the signs
`∫u'v' = -∫u''v`, hence `u-u''=f`.

### `apm_m99J06_galerkin_exists_unique`

**Statement in words.** Every finite-dimensional Galerkin subspace has a
unique discrete solution.

**Why true.** First finish the cached scalar-multiplication analogue of
`apm_m99J06_model_add`, so `M.val` and `M.weakDeriv` behave linearly.  Hölder's
inequality and `M.inner_eq` show

`v ↦ ∫ f * M.val v`

is a bounded real-linear functional on `V`, with norm at most `‖f‖₂`.
Finite-dimensional subspaces are complete; apply the real Hilbert-space Riesz
representation theorem to obtain `u : V` satisfying the equation.  Uniqueness
is exactly the already proved `apm_m99J06_galerkin_unique`.

Mathlib's Hilbert duality is implemented in
`Analysis.InnerProductSpace.Dual` (`toDualMap` is surjective), and the cached
proof outline already verified this route.

**Expected size:** 150–240 lines.

**Dependencies:** definitions and proved cached lemmas only.

**Truth check:** on a one-dimensional space spanned by a unit vector `e`, the
solution is the scalar `ℓ(e)e`; on the zero subspace it is uniquely zero.

### `apm_m99J06_galerkin_norm_le`

**Statement in words.** Every discrete solution has Hilbert norm at most the
`L²` norm of `f`.

**Why true.** Test the Galerkin equation with `u` itself:

`‖u‖² = ∫ f * M.val u`.

Hölder bounds the right side by `‖f‖₂ ‖M.val u‖₂`; `M.inner_eq` and
nonnegativity of the weak-derivative energy give
`‖M.val u‖₂ ≤ ‖u‖`.  Divide when `u ≠ 0`, with a separate trivial zero case,
and convert `eLpNorm` to the norm using its finiteness from `hf`.

**Expected size:** 70–130 lines.

**Dependencies:** definitions and compiled inner-component integrability only;
independent of Galerkin existence.

**Truth check:** equality can occur when the derivative component vanishes;
for the zero solution both sides are nonnegative and the bound is immediate.

### `apm_m99J06_weak_subsequence_solves`

**Statement in words.** A uniformly bounded sequence of nested Galerkin
solutions has a weakly convergent subsequence whose limit solves the full weak
problem.

**Why true.** A bounded sequence in a Hilbert space has a weakly convergent
subsequence (Eberlein–Šmulian; for this sequence one may work in the separable
closed span and diagonalize scalar coordinates).  Express convergence via
`toWeakSpace ℝ H`.

For `v ∈ V m`, strict monotonicity of the subsequence index makes `k j ≥ m`
eventually; nestedness transports `v` into `V(k j)`.  The Galerkin equation
then gives `⟪u_{k j},v⟫ = ∫f·M.val v`.  Weak convergence passes the fixed inner
product to the limit.  Thus the equation holds on `⋃m V m`; both sides are
continuous linear functionals, so density extends it to every `v : H`.

**Expected size:** 180–280 lines.

**Dependencies:** it takes the norm bound as an explicit hypothesis, so its
statement stands alone.  In the main theorem it is used after the previous
lemma supplies that hypothesis.

**Truth check:** a constant Galerkin sequence admits the identity subsequence
and converges to its own value.  If a test vector lies in `V m`, nestedness
ensures it is available at every later discrete stage.

## Dependency layers

* **Layer 1 (parallel):** weak/strong equivalence, Galerkin existence and
  uniqueness, and the Galerkin norm bound.
* **Layer 2:** weak subsequence and limit identification, using the bound as
  an explicit input.  Its proof can be developed in parallel, but final use
  waits for the bound lemma.
* **Layer 3 (already proved):** `apm_m99j06` assembles all four results.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m99J06/Blueprint.lean
```

The final output was:

```text
'apm_m99j06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The four warnings are exactly the four stated lemmas.  The main theorem has no
direct `sorry`.

## Doubt

All statements are standard and appear true.  The main library uncertainty is
whether the pinned Mathlib exposes weak sequential compactness of Hilbert
balls in a directly usable theorem.  If not, the subsequence seat will need a
local diagonal argument in the separable closed span.  The weak/strong bridge
may similarly need local one-dimensional absolute-continuity infrastructure.
