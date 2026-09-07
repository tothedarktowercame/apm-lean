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
