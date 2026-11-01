# Statement repairs of proved problems (2026-11-01)

Problems whose proofs were finished but whose statements the backlog-1024 grading held as narrower. Each repair adds a single `apm_<id>` theorem, repaired by a lemma seat and graded by a read-only Claude subagent dispatched by claude-14 and given only the code and problem.md.

## a92J03

Backlog grade: narrower, linearity never stated. Repair by lemma-1 adds `apm_a92j03` (49 lines, nothing removed). New grade: faithful. Transform matches the printed e^{ixξ}. Clause (c) is implied by the general Tendsto on cocompact ℝ. Linearity is stated as additivity and ℂ-homogeneity. The map into C₀ is unbundled: continuity plus decay. Every clause assumes Integrable, so none leans on a junk integral value.

## a94J05

Backlog grade: narrower, the requested statement of Cauchy's integral formula was omitted. Repair by lemma-2 adds `apm_a94j05` (19 lines, nothing removed). New grade: faithful. The formula is stated on circles for a function analytic near the closed disk, with the 2πi constant; the circle form is accepted for "state the theorem". Both Liouville clauses hold for every entire function with the problem's own bounds.

## a95A03

Backlog grade: narrower, the convolution theorem did not assert membership in L². First repair by lemma-3 added `MemLp`. New grade: narrower, because `g` is real-valued and problem.md does not restrict the scalars (the aunk01 and a98J03 standard). The exponents 3/4 < p < 3/2 and the integral 2π² were recomputed by hand and agree. Sent back for complex-valued `g`.

Second repair by lemma-3 quantifies over `g : E → ℂ` (56 lines added in all, nothing removed). New grade: faithful. Exponents, the integral and the constant ‖f‖₁ = 2π² were recomputed. The statement does not assert a.e. convergence of the convolution integral, but the grader found no content lost: the bound applied to truncations of |g| with monotone convergence recovers it.

## Printed-problem defects (reported apart from full closures)

b01J04, b96A04, a94J02: statements unchanged, backlog grade narrower; the restriction is the smallest correction of a false or inconsistent print. Counterexamples in each PRELIM-DEFECT.md, checked by claude-14.

b93J03: backlog grade narrower for `[Nontrivial V]` on the whole theorem. claude-14 moved the hypothesis to part (a) only and part (b) now covers every V. New grade (read-only subagent): narrower, justified only by the documented defect, smallest correction.
