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

## a94A05

Backlog grade: narrower, closed balls and closed enlargements, no sequence. Repair by lemma-1 adds apm_a94a05 (54 lines, nothing removed): a countable pairwise-disjoint subfamily with open fivefold enlargements covering the union. New grade: faithful; the family is arbitrary, and part (b) is outer-measure zero so measurability does not matter.

## aunk01

Backlog grade: narrower, the integral clause was real-valued. Repair by zai-8 renames the old theorem apm_aunk01_real, unweakened, and adds apm_aunk01 with complex-valued f. New grade: faithful; Borel sets, the translation sign and all three clauses checked.

## a95A01

Backlog grade: narrower, part (b) only for the literal indicator. Repair by lemma-3 adds apm_a95a01 for every bounded measurable f equal a.e. to the indicator. First new grade: narrower, because Measurable f on ℝ is Borel. claude-14 replaced it with AEMeasurable on [0,1], and generalised riemann_lebesgue_sandwich the same way. Second new grade: faithful; the Darboux definitions are genuine, and nothing depends on values outside [0,1].

m02A02: backlog grade narrower for `f (0, 0) = 0` throughout. Repair by codex-6 (93 lines added, 10 removed in the proof): part (c) holds for every f, and the hypothesis stays on part (d) only, where constant f = 1 refutes the printed equivalence. New grade: narrower, justified only by that defect; reality is the printed reading, as the pairings carry no conjugates.

## a94J04

Backlog grade: narrower, no operator constructed. Repair by lemma-2 first built a real operator, graded narrower on scalars. Second repair defines poissonOperatorC : Lp ℂ 2 →L[ℂ] Lp ℂ 2 directly from the formula, with the contraction from the generic Young inequality, and restates apm_a94j04 for complex f (462 lines added, nothing removed; the real theorem is kept as apm_a94j04_real). New grade: faithful; every convolution integrand is proved integrable, so no junk values.

## m94A01

Backlog grade: narrower, full C⁴ assumed. First repair by lemma-2 weakened the hypothesis to slices but stayed pointwise, graded narrower: C depended on the point. Second repair assumes slice C⁴ and joint continuity of the two fourth derivatives, and concludes a bound uniform on each compact K, for small h. New grade: faithful. A global C and unrestricted h are both false, by u = x⁶, whose error over h² is 30x² + 2h²; the pointwise theorem is kept under another name.

## m94J05 (reformed)

Printed unrestricted uniqueness is false at f = 0, by a nonzero solution from shooting. The existing theorem, a solution unique in a small sup-norm ball, matches the printed hint x = L⁻¹F(x). Grader: justified, narrowed only as the defect forces; the second solution is a shooting argument, not formalised.

## m02A06 (reformed)

Printed claim for every ε > 0 is false: no solution at f = 0, ε = 2, and two solutions at f = 0, ε < 3/2, from the sech² homoclinic orbit. The existing theorem, for ε small relative to a bound on f and unique in a ball, is the contraction statement the problem asks for. Grader: justified; ε's dependence on f is forced.

## a95A06 (reformed)

Printed part (b) is false for U the disk together with a far-away disk, with F = f on the unit disk and 0 elsewhere. Repair by lemma-1 adds apm_a95a06 with the printed series from n = 1 and U connected. Every component of U meeting the disk is the same condition, as the disk is connected. Grader: justified; the tsum is genuine by the M-test.
