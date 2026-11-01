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

## a98J03 (reformed)

The printed denominator (x-t)+y² has a pole inside the integration range, so the integrand is not integrable, and a principal-value reading breaks the limit. Repair by lemma-2 uses the Poisson kernel with (x-t)²+y² for complex f, a bounded complex-linear operator of norm at most 1 tied to the formula, and L² convergence. The real theorem is kept. Grader: justified; every convolution integrand is integrable.

## a98A07

Backlog grade: narrower, one common neighbourhood for all f_n. Repair by lemma-1 gives each f_n its own open neighbourhood; the common form is kept as apm_a98a07_of_common_neighborhood. New grade: stronger, since the printed open region reads as common and this weakens that hypothesis; every other clause is exact.

## m94J02 (reformed)

Printed ‖fg‖ ≤ ‖f‖‖g‖ is false at f = g = z, giving 5 > 4. The theorem uses the sharp 5/4, so (5/4)‖·‖ is a submultiplicative equivalent norm. Kimi added the Banach space structure and tied multiplication and T to the functions. Grader: justified; injectivity of eval is unstated but true, by the identity theorem.

## b98A01

Backlog grade: narrower, order 35 replaced printed order 3. Repair by lemma-2 restores the literal equivalence, proved with Burnside normal complements, and keeps the order-35 result. New grade: faithful. Caveat, hand-checked by the grader and claude-14: part (b) of the printed problem is vacuous, since every subgroup of order 5 in a group of order 210 is normal (the Sylow 7 Q is normal, G/Q of order 30 has a normal Sylow 5, so QB is normal and cyclic of order 35, and B is characteristic in it). The Lean matches the print and adds no vacuity.

## m98A05 (reformed)

Printed (b) is false: F = x² + x - 1, G = 1 - x, x₀ = 0, ε₀ = 1, with discriminant (ε-1)(ε-5) negative just above 1. Printed (c) is trivially solved by w = 0. Reform by codex-6: the IFT, (b) with DF + ε₀DG invertible (the printed case ε₀ = 0 is covered), and (c) w = 0 plus every H² Dirichlet solution with |ε||w| < 1 vanishes, by an energy argument. H² is the classical interval characterisation. Grader: over-narrow only in the IFT's global C¹, which claude-14 weakened to ContDiffAt; the grader noted nonzero solutions exist for every ε ≠ 0, so uniqueness must be local.

## a01A11

Backlog grade: hypothesis-carries-core, part (b) assumed analyticity, decay and nonzeroness. Repair by lemma-2 adds apm_a01a11 for compact K of positive measure, discharging them. The printed zf(z) is read as zg(z). New grade: faithful. The grader flagged shadowed section variables, confirmed by #check as extra binders; claude-14 omitted them, and the elaborated signature is now clean.

## lts-ultraproduct-thm1

Triage: Lean gave only a bare equivalence of carrier types and had a sorry. Repair by codex-6 fixes a finitary single-sorted signature, algebras and operation-compatible congruences, and proves the canonical quotient map an algebra isomorphism, with its formulas. New grade: faithful; the left side is a single quotient of the product, which is trivially isomorphic to the printed two-step form.

## m93J02 (reformed)

The printed denominator |x-y^α| is a misprint for |x-y|^α, and the exponent is unstated; convention 0 < α < 1, the Holder scale, since at α = 1 the answers depend on the geometry of Ω. Repair by lemma-1 covers every compact connected Ω, singletons included, where the answers change. Grader: acceptable, truth values checked by hand, one change, the sup metric on Fin n → ℝ, which claude-14 replaced by EuclideanSpace, recompiled.

## a02J07

Backlog grade: narrower, differentiability everywhere plus assumed integrability. Repair by kimi-2 adds PiecewiseSmoothSlitPath, with a finite partition and C¹ pieces only, derives integrability, and adds apm_a02j07 (462 lines, nothing removed). New grade: faithful; posSlitPlane is exactly the complement of the nonnegative reals, and the example of a half circle shows it is not vacuous.

## m93J03 (reformed)

Printed unique solvability is false for every ε: x ≡ ε and a nonconstant branch both solve it, proved in Lean by kimi-1 with no Bessel functions. Its smallness of ε does nothing, pointing to a lost ε before the integral. The theorem keeps the literal local result, proves the failure, and proves unique solvability among all continuous x of x(t) = c + ε∫ sin(t + s + x(s)) ds for every c and small ε. The constant c was added by claude-14 after the grader noted the misprint could keep the printed constant. This reading is an inference from the text.

## m95J01

Backlog grade: hypothesis-carries-core, the integral was assumed an inner product and T assumed. Repair by kimi-1 constructs the concrete space of functions e^{-x}p(x), proves the integral pairing is an inner product with genuine integrals, gives T's matrix in the printed basis, the range criterion and the orthonormal basis. The grader required a clause that T is the second derivative, now proved. The old theorem is kept as apm_m95j01_abstract.

## a00J06

Admission of singular_at_one was revoked: it used tsum's junk value past the radius. New apm_a00j06 states and proves Pringsheim's theorem honestly for complex z, by zai-7 and lemma-1 (571 lines): Taylor expansion at c < 1, Tonelli in ENNReal, summability past 1, contradicting radius 1. New grade: faithful; the tsum is used only inside the unit disk, and singular_at_one is not called.

## m97A05

Backlog grade: narrower, the Fourier formula and the action of ∂x T were omitted. Repair by zai-6 and lemma-3 adds both (581 lines), with the Fourier clause on EuclideanSpace ℝ (Fin 2) through the coordinate isometry, since ℝ × ℝ has no inner product in Mathlib; (𝓕T)ψ = ∫ ψ(t, t) under Mathlib's normalisation, disclosed. New grade: stronger, as T is tempered rather than only in D′.
