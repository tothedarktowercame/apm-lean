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
