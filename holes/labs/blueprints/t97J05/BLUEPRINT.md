# Blueprint for t97J05

## Triage and repair

Verdict: **the registered statement needs a small faithfulness repair; the
repaired statement is true**.

The source asks whether `W` is a (smooth embedded) manifold.  The original
predicate supplied a smooth one-manifold structure on the subtype and required
the subtype inclusion to be a topological embedding, but did not require that
inclusion to be an immersion.  This is too weak: a topologically embedded
curve with a corner can be given a smooth source structure using a flat
parametrization, making its inclusion smooth while its derivative at the
corner is zero.  Thus the predicate can certify images which are not embedded
smooth submanifolds in the usual sense.  This is the defect identified by the
statement-registry grader.

`RevisedMain.lean` makes the smallest recommended change: inside
`apm_t97J05_IsSmoothSubmanifold`, it adds

```lean
∀ x : s, Function.Injective (mfderiv ... Subtype.val x)
```

so the inclusion is also an immersion.  No source hypothesis or conclusion is
dropped.  The grader's corner counterexample no longer passes: its flat
parametrization has zero derivative at the corner, which is not injective on a
one-dimensional tangent space.  I did not include `Refute.lean`, since fully
formalizing the exotic charted structure on the corner is substantially
larger than the one-line defect and the repair itself.

The repair is true for this fiber.  On `W`, `xz = 1`, hence `x ≠ 0`; and
`exp x * cos y = 0`, hence `cos y = 0` and `sin y = ±1`.  The derivative rows
there are `(0, -exp x * sin y, 0)` and `(z, 0, x)`, so they have rank two.
The regular-level theorem therefore gives a genuine embedded one-manifold and
an injective derivative for its inclusion.  Degenerate checks: `W` is not
empty (`p ∈ W`); `x = 0` cannot occur because `xz = 1`; and all branches
`y = π/2 + kπ`, including negative `x`, retain rank two.  The parameter target
restricts to `0 < y < π`, selecting exactly the branch `y = π/2` near `p`.

The source's typo giving the domain of `φ` as `ℝ²` while evaluating it on
three coordinates was already correctly repaired to `ℝ³` by `Main.lean` and
is preserved.

## Reused completed work

The solve-loop file already contained a sorry-free proof that
`γ(t) = (t, π/2, 1/t)` is a bijection from `(1/2,3/2)` to the stated local
piece of the fiber.  `Blueprint.lean` retains that calculation as
`apm_t97J05_f_gamma_eq_value` and `apm_t97J05_gamma_bijOn`; it is not assigned
to a lemma seat.

## Remaining lemmas

### `apm_t97J05_derivative_and_rank`

**Statement.** The derivative at `p` has the displayed formula and is
surjective.

**Why true.** Differentiate `exp x * cos y` and `xz` using Mathlib's Fréchet
derivative rules and simplify with `sin (π/2)=1`, `cos (π/2)=0`.  For
surjectivity, send `(a,b)` to `(b,-a/exp 1,0)` (or use the first two columns).

**Expected size.** 50–100 lines.  **Dependencies:** definitions only.

**Truth check.** The matrix is `[[0,-e,0],[1,0,1]]`; its first two columns
have determinant `e ≠ 0`.

### `apm_t97J05_gamma_smooth`

**Statement.** The explicit parameterization is smooth on `(1/2,3/2)`.

**Why true.** Coordinatewise smoothness reduces to constants, the identity,
and `t ↦ t⁻¹`; the interval excludes zero.  Use the `ContDiffWithinAt` rules
for inverse and assemble the finite Euclidean vector coordinatewise.

**Expected size.** 20–40 lines.  **Dependencies:** definitions only.

**Truth check.** The only possible singularity is `t=0`, while every domain
point satisfies `t>1/2`.

### `apm_t97J05_regular_fiber_embedded` — LIBRARY

**Statement.** The complete fiber `f⁻¹ {(0,1)}` carries a smooth
one-manifold structure whose subtype inclusion is smooth, topologically
embedded, and has injective manifold derivative everywhere.

**Why true.** The row-rank calculation above holds at every fiber point:
`x ≠ 0` and `sin y = ±1`.  Apply the regular-level/preimage theorem for a
smooth map `ℝ³ → ℝ²`, and its theorem identifying the induced subtype
inclusion as an embedding and immersion.

**Expected size.** 300+ lines if the missing regular-level assembly must be
built from current Mathlib primitives; this is intentionally one LIBRARY
boundary rather than fake small wrappers.  **Dependencies:** definitions
only (the all-points rank calculation is internal, not the distinguished-point
lemma above).

**Truth check.** Checked every component `y = π/2+kπ` and both signs of
nonzero `x`; the same nonzero two-column minor works.  This is the exact
missing global regular-preimage theorem recorded by the topology loop.  No
sorry-free `ConstructionTargets` module currently supplies it.

### `apm_t97J05_local_normal_form`

**Statement.** There are smooth open partial homeomorphisms around `0`, `p`,
`(0,1)`, and `0` which put `f` into the projection `(x,y,z) ↦ (x,y)`.

**Why true.** Complete `f` to
`Φ(x,y,z)=(exp x cos y,xz,z)`.  Its derivative at `p` has determinant `e`, so
the inverse function theorem gives a local inverse.  Translate source and
target: take `φ(u,v,w)=Φ⁻¹(u,v+1,w+1)` locally and `ψ(a,b)=(a,b-1)`.
The first two coordinates then give the demanded equality.

**Expected size.** 100–180 lines.  **Dependencies:** definitions only; use
the inverse function theorem directly so this seat is parallel to the explicit
derivative lemma.

**Truth check.** `DΦ_p=[[0,-e,0],[1,0,1],[0,0,1]]`, with determinant `e`,
and direct substitution gives `ψ(f(φ(u,v,w)))=(u,v)`.

## Dependency layers

* **Layer 1 (all parallel):** the four remaining lemmas above.  Each statement
  is closed over the definitions and does not consume another seat's theorem.
* **Layer 2 (already proved assembly):** `apm_t97j05`, using the four lemmas
  and the retained bijection proof.

## Compilation and axioms

Both files compiled with the prescribed 12G command.  The final output of
`#print axioms apm_t97j05` in `Blueprint.lean` was:

```text
'apm_t97j05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The four warnings are exactly the four top-level seat lemmas.  The main theorem
has no direct `sorry`.
