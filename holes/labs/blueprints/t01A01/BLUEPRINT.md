# Blueprint for t01A01

## Triage

Verdict: **true and faithful**.  The registered type uses the quotient-topology
`Projectivization ℝ (Fin 3 → ℝ)` for `RP²`, assumes exactly that the continuous
self-map is not surjective, asserts pointwise triviality of every based induced
fundamental-group map, and asserts a free null-homotopy.  These are the two
conclusions in `problem.md`.

I first checked the usual degeneracies.  `RP²` is nonempty, so the empty-domain
shortcut is unavailable.  A constant map is nonsurjective and satisfies both
conclusions.  The identity map is surjective, so it is not a counterexample.
For a general nonsurjective map, choosing a missed point makes the codomain a
punctured `RP²`, which deformation retracts to `RP¹ ≃ S¹`.  A map from `RP²`
to the circle induces a homomorphism `Z/2 → Z`, hence the zero homomorphism;
lifting to `ℝ` then gives the null-homotopy.  This is also the hand proof that
establishes the registered conclusion.

The solve-loop and topology ledgers record no counterexample.  They agree that
the statement is faithful and that the stalled boundary is construction of the
punctured-projective-plane geometry in Lean, not a defect in the theorem.

## Reused, already proved declarations

`apm_t01A01_factor_through_complement` selects a missed point and packages the
map with subtype codomain.  `apm_t01A01_nullhomotopic_of_factor` composes a
null-homotopy of this factor with the subtype inclusion.  Both are copied from
the current compiled `Main.lean` and contain no `sorry`.

The blueprint imports the sorry-free modules
`ConstructionTargets.ProjectiveSpaceTopology`,
`ProjectiveQuotientDescent`, `RealProjectiveSmoothTarget`,
`SimplyConnectedOpenCover`, `CircleUniversalCover`, and
`ComponentRealLiftAssembly`.  They supply the existing quotient, sphere,
circle-cover, lifting, and component-assembly infrastructure, but do not supply
the missing punctured-`RP²` retraction.

## Remaining lemmas

### `apm_t01A01_punctured_factor_nullhomotopic` — LIBRARY

**Statement in words.** Every continuous map from `RP²` to the complement of
an arbitrary point of `RP²` is homotopic, in that complement, to a constant.

**Why true.** Normalize the missed projective point by a linear isometry.
Represent `RP²` by the antipodal quotient of `S²`; radial/orthogonal projection
away from the two representatives of the missed point gives a deformation
retraction onto the equatorial projective line.  Identify that line with
`Circle`.  For the resulting map `RP² → Circle`, pull back along the sphere
projection.  Lift the sphere map through `Circle.exp : ℝ → Circle` using sphere
simple connectedness and the banked covering machinery.  Antipodal invariance
forces the lift difference at antipodal points to be a constant integer; applying
the antipodal map twice and connectedness forces that integer to be zero.  The
lift therefore descends through the projective quotient.  Contract it linearly
in `ℝ`, use `ComponentRealLiftAssembly`, and transport the homotopy back through
the projective-line retraction.

**What the library program must add.** The closest sorry-free modules are
`ProjectiveSpaceTopology` and `ProjectiveQuotientDescent`, but the former only
has continuity/surjectivity of the quotient and the latter does not yet package
the exact restricted and interval-product descent needed here.  The program
must add the open-quotient/restriction machinery, coordinate normalization of
an arbitrary `q`, the explicit punctured-`RP²` deformation retraction, and the
projective-line/Circle identification.  The already banked circle-cover and
real-lift modules apply only after those maps exist.  This is intentionally one
honest LIBRARY boundary rather than several small lemmas that conceal the same
large construction.

**Expected size.** 500–900 lines (a multi-session library program).

**Dependencies.** Only the definitions and the imported sorry-free
ConstructionTargets modules.

**Truth check.** In disk coordinates, remove the center and retract radially to
the boundary; the retraction commutes with the antipodal boundary relation and
descends to the core circle of the Möbius band.  At the boundary it is the
identity, and no denominator vanishes because the removed point is excluded.
For constant `g`, choose its value as `p`; the stated homotopy is reflexivity.

### `apm_t01A01_piOne_trivial_of_nullhomotopic`

**Statement in words.** For arbitrary topological spaces, a continuous map
freely homotopic to a constant sends every fundamental-group element, at every
basepoint, to the identity.

**Why true.** Use
`FundamentalGroupoidFunctor.homotopicMapsNatIso` on the homotopy.  Naturality
identifies the two induced loop morphisms up to conjugation by the component of
the natural isomorphism.  The constant map sends every loop to the constant
loop, hence to `1`; conjugating `1` still gives `1`.  Quotient induction on the
fundamental-group element is an alternative direct proof.

**Expected size.** 30–60 lines.

**Dependencies.** Only Mathlib; independent of the LIBRARY lemma.

**Truth check.** For `γ = 1`, both sides reduce to `1`.  If `X` is empty the
universal quantification over `x` is vacuous.  If `f` itself is constant, the
claim follows directly because every composed loop is constant.  Free rather
than pointed homotopy only introduces conjugation, which cannot change the
identity.

## Assembly

After factorization, the LIBRARY lemma supplies a null-homotopy in the punctured
codomain.  The proved descent lemma turns this into a null-homotopy of `f` in
`RP²`.  The generic fundamental-group lemma supplies the first conjunct, and
the same homotopy supplies the second.  The main theorem contains no `sorry`.

## Dependency layers

* **Layer 1 (parallel):**
  `apm_t01A01_punctured_factor_nullhomotopic` (LIBRARY),
  `apm_t01A01_piOne_trivial_of_nullhomotopic`.
* **Layer 2 (already compiled):** factor/descent and the final theorem assembly,
  after the two Layer 1 lemmas are supplied.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t01A01/Blueprint.lean
```

The two warnings are exactly the two top-level Layer 1 lemmas.  The final output
of `#print axioms apm_t01a01` is:

```text
'apm_t01a01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

