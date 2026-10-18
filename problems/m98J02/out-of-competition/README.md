# m98J02 — out-of-competition finding

`Main.lean` here proves part (d) of m98J02 under the narrow reading described
in `../problem.md`, "Interpretation note". It assumes:

- `f ∈ C²(ℝ²)` **with compact support**, so that `w = f * w₀` is defined by part (b);
- `w₀` is the regular distribution of a locally integrable `k`, with `T w₀ = δ₀`.

It concludes that `w = f * w₀` is a regular distribution with a `C²` density,
that `T w = f`, and that `w + 1` is a different solution. Parts (a)–(c) are as in
the competition file.

Status: elaborates with no sorries (`lake env lean`, 2026-10-18). Axioms:
`propext`, `Classical.choice`, `Quot.sound`. Theorem: `apm_m98j02_compactF`
(renamed from `apm_m98j02`, saved from 7de364a86).

It is not a closure of m98J02. The registered statement asks for every
`f ∈ C²(ℝ²)`. Until 2026-10-18 the registry graded the narrow statement
"narrower, acceptable", treating the printed problem as defective. The informal
solution now proves the printed statement, so that grade was revoked.
