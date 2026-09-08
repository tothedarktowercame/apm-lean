# Statement-encoding skips, 2026-09-07 sweep

Recorded so the next encoding sweep does not re-attempt these blindly.
Context: of the 43 bundles missing `problems/<id>/lean/Main.lean`, tranche 1
(8 problems, codex-2, reviewed by claude-3) encoded 4 and skipped 4; a98J05
was skipped in the original pass. Skip reasons as reported and reviewed:

- **a98J05** — the source TeX contains an assumption (analytic
  `f(z) = z + Σ cₙ zⁿ` on the disk) but **no conclusion**; the informal
  analysis confirms the statement is incomplete. Nothing to encode until the
  intended conclusion is recovered.
- **t93A05** — Mathlib lacks the smooth-homotopy and mod-2/oriented
  submanifold-intersection framework needed to state all three parts
  concretely.
- **t93A06** — the required quotient-torus differential forms, pullback
  uniqueness, exterior derivative, and integration interfaces are not
  jointly available in Mathlib.
- **t93J03** — a faithful statement needs a concrete Klein-bottle model, its
  fundamental-group presentation, covering classification, and the planar
  embedding conclusion; the combination is out of reach without substantial
  scaffolding.
- **t95A01** — the group-theoretic shadow is statable, but the question is
  about spaces (a non-orientable surface self-cover); the concrete
  Klein-bottle/self-cover classification is absent from Mathlib.

A skip here is a claim about Mathlib coverage at the time of the sweep, not
about the problem. If the relevant API lands (or someone builds the local
scaffolding), remove the entry and encode.

## Tranche 2

- **lts-derived-induction-lem3** — Mathlib has no category of genuine or
  Borel-equivariant spectra on which to state the restriction functor and its
  detection-of-equivalences assertion.
- **lts-monadic-integration** — the measure monad, bornological measurable
  spaces, “enough Pettis integrals,” and its algebra laws are not present as a
  common concrete interface.
- **t00J05** — the attached CW complex and its universal cover require CW
  attachment and cellular universal-cover constructions not available in the
  topology library.
- **t93J05** — Mathlib does not currently provide the differential-form degree,
  exterior derivative, oriented surface integration, and piecewise surface
  model needed together for this computation.
- **t95A04** — a concrete smooth-manifold model of `ℝP²` as the antipodal
  sphere quotient, with its quotient smooth structure, is missing.
- **t95A05** — the statement needs oriented manifold boundaries, integration
  of differential forms, intersection numbers, and local Lefschetz indices;
  these are not jointly formalized.
- **t96A01** — encoding the conclusion requires surface-group presentations
  and the finite-index subgroup classification (Reidemeister--Schreier plus
  surface realization), beyond the existing fundamental-group API.
- **t96A02** — Mathlib lacks a concrete wedge of two projective planes and the
  homological Lefschetz fixed-point machinery used by the assertion.
- **t96A06** — the quotient smooth structure on `ℝP³` and Lefschetz-number API
  needed for the induced polynomial map are absent.
- **t96A07** — a faithful statement requires the quotient smooth structure on
  `ℝP²` and manifold transversality to the axis and horizontal planes.
- **t96J02** — the finite-index subgroup classification of the Klein-bottle
  group requires a concrete Klein-bottle group presentation and classification
  development not in Mathlib.
- **t97A05** — oriented intersections of compact submanifolds are not available
  as a concrete invariant with the required complement-connectivity theorem.
- **t97A06** — extension and pullback of arbitrary-degree differential forms,
  volume-form integration, and closedness are not jointly supported.
- **t97A07** — Mathlib has derivative critical sets but not the full compact
  smooth-manifold regular-value framework needed to state both critical-value
  conclusions without building substantial new manifold infrastructure.
- **t98A06** — vector fields along manifold maps, global smooth lifts through
  submersions, completeness of flows, and diffeomorphism of fibers are not
  available as one concrete interface.
- **t98J01** — the spaces are concrete, but Mathlib has no Lefschetz number for
  continuous self-maps with which to state the requested computation.
- **t98J02** — the assertion needs closed-surface separation, simple closed
  curves, and lifting through finite covers, none represented together.
- **t98J04** — linking of embedded circles and disk-bounding in a solid torus
  require knot/link and embedded-disk notions absent from the library.
- **t98J05** — the genus-two surface quotient, descended differential form,
  exactness, curve integration, and homotopy class cannot be stated using the
  current differential-topology APIs.
- **t98J06** — the nonsingularity half is approachable, but the requested local
  oriented intersection number has no concrete Mathlib carrier; encoding only
  the linear-algebra consequence would omit half of the single assertion.
- **t99A01** — Mathlib does not expose the required CW cell-attachment spaces
  and their cellular homology and fundamental-group computations.
- **t99A02** — concrete wedge models exist only with substantial local quotient
  scaffolding, while the requested output is a geometric description of their
  universal covers rather than a proposition already represented in Mathlib.
- **t99A03** — the two projective-plane constructions and the fixed-point
  property require Lefschetz/cohomological machinery and concrete wedge and
  connected-sum models that are absent.
- **t99A04** — integration and pullback of closed one-forms over an embedded
  circle are not supported by a de Rham integration interface.
- **t99A05** — mod-two degree and mod-two submanifold intersection number lack
  concrete definitions in the pinned library.
- **t99A06** — Mathlib's Euler characteristic is for algebraic complexes, not
  a manifold invariant connected to nowhere-zero vector fields and
  submersions to the circle.
- **t99J01** — a faithful encoding needs a concrete wedge of three circles,
  classification of finite-sheeted covers, and computations of all resulting
  fundamental groups.
- **t99J02** — CW decomposition, cellular homology, van Kampen, and
  Mayer--Vietoris are not formalized at the level needed to state all five
  requested outputs for the genus-two surface.
- **t99J05** — complex projective space is available algebraically, but the
  topological quotient, local Lefschetz index, and Euler-characteristic
  computation for its self-map are not.
- **t99J06** — exterior differentiation and oriented integration of a two-form
  over the specified cone lack a suitable differential-form integration API.
- **tunk01** — the polygon word and exceptional vertex can be encoded
  combinatorially, but the requested surface classification needs a verified
  polygon-gluing-to-surface and classification theorem not present in Mathlib.

## Corrections and status, 2026-09-08 (claude-5)

**This list is a prior, not a verdict — measured.** Six of its 36 entries have
since been encoded and pass `scripts/check_statement_quality.py`: t99A01,
t99A02, t99A03, t99A04, t99A05, and tunk01 (`bcdab261`, 2026-09-08).

**tunk01 is the instructive one.** It was skipped here as needing "a verified
polygon-gluing-to-surface and classification theorem not present in Mathlib".
That theorem is needed to PROVE the classification; it is not needed to STATE
it. The landed encoding builds the polygon quotient and the standard
genus-six comparison surface as concrete `Quotient` / `TopologicalSpace`
objects and states a `Homeomorph` between them, with `sorry` for the proof.
Reviewed independently: the encoded word matches the printed source
symbol-for-symbol, and deriving the 14 edge identifications by hand gives
exactly two vertex classes ({P3, P9} and the rest), so chi = 2 - 7 + 1 = -4
and the surface is nonorientable — N6, as encoded. (The duplicate t94J09
answers N3 via a program its own author flagged "not necessarily to be
trusted"; N3 would require chi = -1, i.e. five vertex classes. The encoding
is right and t94J09 is wrong.)

**t99A05 shows the other technique, and its cost.** Skipped here for lacking
mod-two degree and intersection number. The landed encoding unfolds the
invariant into its definition — odd mod-two degree becomes odd cardinality of
the restricted fiber — which is honest, but it also drops smoothness and
transversality, so it states a weaker claim than the printed problem. Where
that line falls is a live question, not a settled one.

**Factual correction to the t93A06 entry.** The conclusion (blocked) stands,
but not for the recorded reason. Mathlib DOES have differential forms with an
exterior derivative and pullback, in `Mathlib/Analysis/Calculus/DifferentialForm/`
(`extDeriv`, `extDerivWithin`, `extDeriv_pullback`) — not under
`Geometry.Manifold` or `MeasureTheory`, which is where the 2026-09-08 re-check
searched before reporting them absent. What is genuinely missing is forms on
MANIFOLDS (the API is over normed vector spaces) and oriented integration of
forms / Stokes. Any future re-check should test those two things, not the
existence of `DifferentialForm`.

**Confirmed still absent (checked 2026-09-08):** no topological Lefschetz
number or index anywhere in Mathlib (only the model-theoretic Lefschetz
principle); no `intersectionNumber`; no manifold Euler characteristic
(`eulerChar` is the poset/incidence-algebra one); no `TopologicalSpace` or
`ChartedSpace` instance on `LinearAlgebra.Projectivization`, and no `RP`
notation.

## Joe's ruling on dropped hypotheses, 2026-09-08

**"If it's dropping conditions from the informal statement, we shouldn't allow
that. That doesn't make any sense."**

A constructive encoding may DEFINE what Mathlib lacks -- that route is
explicitly allowed, and is how the topology loop already works. What it may
not do is keep the shape of the problem while discarding the hypotheses that
make it that problem.

**t99A05 is withdrawn on this ruling.** Its source asks: for a SMOOTH map
between MANIFOLDS and a SUBMANIFOLD Z with dim Z = dim Y and nonzero mod-2
degree, must a compact submanifold W exist with nonzero mod-2 intersection
number? The encoding had `Continuous` in place of smooth, `TopologicalSpace`
in place of manifold, a bare `Set X` in place of the submanifold, and no
dimension condition at all -- then pinned W to be exactly the fibre rather
than asserting one exists. It passed every mechanical check, because a
statement can be well-formed, non-trivial, and still not be the problem.

The constructive route remains open for it: define mod-2 degree and mod-2
intersection number locally, then state the question with smoothness, the
manifold structures and dim Z = dim Y intact. That is more work than the
withdrawn encoding and it is the work the problem actually asks for.

**The rule is now enforced, not remembered.**
`scripts/check_statement_quality.py` fails an encoding when the source demands
smoothness, a manifold, a dimension condition or an orientation and the Lean
carries no sign of it. Scanned across all 471 encoded bundles it flags ten:

    a94J06 (orientation)   b99A04 (dimension)   m99A05 (dimension)
    t00A04 (smooth,manifold)  t01A07 (manifold)  t91A01 (smooth,orientation)
    t91A05 (smooth)        t91A07 (manifold)    t99A04 (manifold)
    t99A05 (smooth,manifold,dimension)  <- withdrawn

t99A04 is the next clearest: its source is a connected oriented compact
2-manifold with a smooth circle embedding and closed 1-forms; its encoding is
`g : ℝ → ℝ` with `∫₀¹ deriv g = 0`. The other nine are reported, not touched
-- withdrawing committed encodings is a decision per problem, not a sweep.
