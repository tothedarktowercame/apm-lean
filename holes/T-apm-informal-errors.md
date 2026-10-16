# T-apm-informal-errors — what is left wrong in the informal solutions

**Type:** T-prefix ticket. **Raised:** 2026-10-16 by Joe, after the mark8
mining run showed how badly the informal solutions converted to TeX.
**Status:** open; the items below are for anyone working on these files.

## What has been done

- **Notation.** Half the files (254 of 501) wrote their mathematics as Unicode
  prose (`f\_k = n · 1\_{[j/n, (j+1)/n]}`, `∃ε>0: ∀N>0`). Every formula in
  prose is now `$...$` LaTeX (`34c53beba`, pilot `c98033944`), with no word or
  symbol of the content changed. `scripts/check-math-markup.py <id>` proves a
  file unchanged in content against git HEAD. Run it on any future
  notation-only edit.
- **Clear notation errors fixed** (2026-10-16), each with an obvious intended
  meaning:
  - a01A04: `\pi^{n}/^{2}` → `\pi^{n/2}`
  - a95A08: `\int_{0}^{2}\pi` → `\int_{0}^{2\pi}` (15 places)
  - a96A02: `\sum_{n=n}^{2N}` → `\sum_{n=N}^{2N}`
  - a01A02: `m(E)^{1/1 - 1/2 + 1/1}` → `m(E)^{1/2}`
  - a98A06: a stray closing bar in `|f(z)||z|^{1/2}|\le C` (2 places)
  - t94J06: an extra closing brace in `\mathbb C\setminus\{0\}}`
  - a01A12: a Cyrillic `е` in `rе^{iθ}`
- **The export is checked before mining.** `scripts/qc-mining-tex.py
  <eprints-dir>` counts conversion defects over the exported papers and exits
  non-zero when a class is over its allowance.

## Open: needs a mathematician's judgement

These were seen while rewriting the notation and left as written, because
fixing them changes what the file says.

**Doubtful or wrong claims**
- a97A04: "bounded sequences in $\mathbb{R}$ are complete".
- a96A01: $\|f\|_p = (m(E^c))^{1/p}$ looks wrong.
- a95A07: the heading says "pole of order 3 (double from $1/z^{2}$ and simple
  ...)"; check the count.
- a94J02: contradicts itself about whether the construction works on all of
  $\mathbb{R}$.
- t94J09: a remark says the reduction algorithm's answer $N_3$ is wrong and its
  own $N_6$ is right. Nobody has checked this.
- m94J02: says the problem's stated inequality is false and proves a version
  with constant 5/4.
- m02J06: says the source statement is garbled at one point.
- a98J03: quotes the problem's misprinted denominator $(x-t) + y^{2}$.

**Garbled passages**
- t97A04: `\\[α]=(1,0)` and `\\[α]↦2[α]-[β]`, left outside math.
- a96J08: "= known" in the middle of a formula.
- a03J01: the notes refer to "Step 5/Step 6", which do not match the proof's
  numbering.
- a97A03: a duplicated "PROOF-PLAN.EDN" paragraph.
- m99A04: in Stage 2, `\(F` opens with `\(` and closes with a backtick.
- t92J09: a displayed formula ($\int_{S^2} i^*(\omega) = \int_{B^3} d\omega$)
  sits inside an unlabelled code fence.
- a98J03, line 44: unbalanced italic asterisks.

**Drafting left in**
- Self-correction passages ("Wait, let me redo this", abandoned attempts):
  a01A02, a01A06, a01A09, a01A10, a01A12, a01J04, a01J05, a00J06, a02J02,
  a93A01, a93J02, a94J07, a95A01, a95A05, a95A06, a95A08, a95J02, a95J06,
  a95J08, a96A06, a96J10. A solution meant for readers should state the
  argument that works, once.
- Host paths (`/home/joe/...`) in the prose: a97A03, b93J01, b93J02, t91J04.
- A stray `EOF` line at the end of a99J05. A typo "JSImportantly" in t94J01.

**Notation that reads awkwardly but is faithful**
- a02J04, a93J01: Mathlib's type `ℝ≥0∞` in prose became
  $\mathbb{R}_{\geq 0}\infty$. a95A03 and a03J01 still have it as Unicode
  outside math. It should be written as a Lean name or as $[0,\infty]$.
- a98J04: $z0$, $x0$, $y0$ without subscripts.
- Set-builder notation with words inside, such as
  `$\{x \in \mathbb{R}^{n} :$ $x$ belongs to ...`: this is correct, but it would
  read better as one formula with `\text{}`.

## Open: what the converter still gets wrong

After the rewrite, the export of all 501 papers compiles and passes
`qc-mining-tex.py`, but some defects are still counted: 64 formulae with
unbalanced brackets in 55 papers, 20 formulae ending against a letter in 9,
and 4 escaped `_`/`^` in prose. Most come from bold run-in headings, as in
`\textbf{($\Longrightarrow) f$ is AC}` and `Case 1: $|z| < 1 (z$ inside the
unit disk)`. To list them with examples:

    bash scripts/informal-proofs-to-tex.sh <ids> <tex-dir>
    python3 scripts/export-mining-tex.py <ids> <tex-dir> <eprints-dir>
    python3 scripts/qc-mining-tex.py <eprints-dir> --examples 20

The futon6 side (`scripts/pandoc-mathify.lua`) and this repository's
`scripts/asciify-tex.py` hold the conversion rules. Fix a rule, not an
instance.
