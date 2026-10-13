# Blueprint for t94J08

## Triage

Verdict: **true and faithful**.

The source asks for the antipodal degree on every sphere and for the effect of
negating a vector field on its local index.  The current registered statement
faithfully separates the exceptional boundary cases from the ordinary
top-homology encoding:

- the antipodal map on `S⁰` is the transposition of two points, and its degree
  is encoded on reduced zero-homology;
- the local index of a vector field on a one-dimensional manifold is encoded
  by the two endpoint signs;
- dimensions at least two use the induced map on integral top singular
  homology of the linking sphere.

This separation is necessary.  The historical encoding incorrectly demanded
ordinary `H₀(S⁰) ≅ ℤ`, whereas ordinary `H₀(S⁰) ≅ ℤ²`.  That older
counterexample is recorded by the topology loop, but `Main.lean` already
contains the admitted repair, so no `RevisedMain.lean` is needed.

I also checked the usual degeneracies.  The reduced-`S⁰` formula is tested
on an arbitrary augmentation-zero chain, not merely on one chosen generator.
The one-dimensional formula allows either endpoint sign and any integer
`d`; the conclusion follows algebraically from `sign (-x) = -sign x`.
For the positive-dimensional branch, `n = 1` is the smallest admitted
sphere and is covered by the construction target; `n = 0` is deliberately
handled by the separate reduced-`S⁰` conjunct.  The empty and zero-dimensional
Euclidean-space pathologies therefore do not enter the ordinary-homology
claim.

## Reused topology construction

The former LIBRARY obstruction is now discharged by the sorry-free module
`ConstructionTargets.CoefficientSphereAntipodal`.  Its
`normalization` gives the integral top-homology orientation and
`scalar_equation` computes the actual induced antipodal action as
multiplication by `(-1)^(n+1)`.  The blueprint imports this module exactly as
the registered `Main.lean` does.

The existing declarations are retained with their proofs:

- `t94J08HasDegree_with_orientation`: independence from the chosen
  orientation;
- `t94J08HasDegree.comp`: degree multiplicativity;
- `t94J08NormalizedLink_neg`: pointwise identification of the negated
  normalized link with antipodal composition;
- `apm_t94J08_bridge_1`: specialization of the construction target;
- `apm_t94j08_previous_encoding`: assembly for dimensions above the endpoint.

## Completed endpoint and assembly lemmas

### `apm_t94j08_low_dimensional`

**Statement in words.** The transposition of `Fin 2` has reduced degree
`-1`, and negating a real vector field negates its endpoint-sign local
index.

**Why true.** Evaluation of `Equiv.swap 0 1` reduces the first equality to
`a 0 - a 1 = -(a 1 - a 0)`, proved by `ring`.  For the second equality,
all zero/isolation/nonvanishing fields are preserved by negation; rewriting
both endpoint signs with `Real.sign_neg` and the assumed index equality
finishes by `ring`.

**Expected size.** 15–25 lines.  This is below the requested 30–150-line seat
range, so it is proved directly in the blueprint rather than exposed as an
artificial parallel obligation.

**Dependencies.** Definitions only.

**Truth check.** The exact general statement was compiled with its full proof.
It does not use smoothness and works at all four possible pairs of nonzero
endpoint signs.  The reduced-degree calculation was checked for an arbitrary
function `Fin 2 → ℤ`.

### `apm_t94j08_positive_dimensional`

**Statement in words.** The construction target gives the antipodal degree in
every positive sphere dimension, and composition with the normalized linking
map gives the index formula in ambient dimensions at least two.

**Why true.** Use `apm_t94J08_bridge_1`, extract the continuous normalized
link from the local-index hypothesis, compose it with the antipodal map, and
apply `t94J08HasDegree.comp` plus `t94J08NormalizedLink_neg`.

**Expected size.** 25–35 lines, already proved.

**Dependencies.** The sorry-free construction target and the previously
compiled degree/link lemmas.

**Truth check.** The proof compiles for the boundary `m = 1`; the hypothesis
`1 ≤ m` excludes precisely the separately encoded one-dimensional ambient
case.

## Remaining lemmas and dependency layers

There are **zero remaining sorry lemmas**.  Both natural dependency packets
were small enough to close in the blueprint:

- **Layer 0 (already proved):** the construction-target antipodal action,
  degree composition, and normalized-link identity.
- **Layer 1 (proved here):** `apm_t94j08_low_dimensional` and
  `apm_t94j08_positive_dimensional`.
- **Layer 2 (proved here):** `apm_t94j08`, by conjunction assembly.

No lemma seats are needed.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t94J08/Blueprint.lean
```

The final output was:

```text
'apm_t94j08' depends on axioms: [propext, Classical.choice, Quot.sound]
'apm_t94J08_bridge_1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Thus `apm_t94j08` is sorry-free; in particular, `sorryAx` does not occur.

