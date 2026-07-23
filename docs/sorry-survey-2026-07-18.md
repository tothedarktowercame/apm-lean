# APM Lean sorry survey — 2026-07-18

## Executive summary

The Stack HUD's `57 with sorries | 158 sorries open` is not a count of the
current proof obligations alone.  Its scanner recursively searches every Lean
file in each canonical problem bundle and uses a case-insensitive textual
match.  Consequently it includes comments, historical proofs, and unselected
candidates.

The useful operational breakdown is:

| Scope | Problems | `sorry` tokens |
|---|---:|---:|
| Obsolete HUD textual scan (comments and all versions included) | 60 | 214 |
| Executable lowercase `sorry` in all versions | 60 | 157 |
| Executable lowercase `sorry` in current `lean/` proofs | 50 | 121 |
| Non-current candidate/historical tokens (adding 10 extra problems) | 10 | 36 |

Here, "current" means a file under `problems/ID/lean/`.  Candidate-set
selection is not yet represented consistently, so the ten non-current entries
need curation rather than theorem proving.

Effort estimates below are bundle-level estimates for an experienced Lean 4 +
Mathlib contributor working from the existing skeleton:

- **S:** under half a day
- **M:** half a day to two days
- **L:** two to five days
- **XL:** more than five days, or blocked on substantial missing reusable
  infrastructure

These are triage estimates, not commitments.  A short API-spike should precede
every L/XL item.

## Repeated work — do this first

### Exact or near-exact duplicate exercises

| Problems | Current holes | Reuse opportunity | Estimate |
|---|---:|---|---|
| `a00J04`, `a01A08` | 1 + 1 | The TeX explicitly says `a01A08` is exactly `a00J04`; the Lean developments already have the same final theorem name. Finish the connected-component assembly once, then share or port it. | XL once, near-zero second copy |
| `a00J01`, `a93J04` | 2 + 1 | Both prove `‖f‖ₚ → ‖f‖∞` on `[0,1]`. Extract one finite-measure `eLpNorm` limit theorem and instantiate it twice. | L once, S second use |
| `a00J05`, `a01A11` | 4 + 2 | Both are the Cauchy transform of a compact positive-measure subset of `ℝ`. A shared differentiation-under-the-integral and large-`z` asymptotic layer should close both. | L once; saves a second L effort |

### Duplicate declarations caused by old versions

These should be curated before proving anything, because clearing an old file
does not advance the current result:

- `a00J01`: `lower_bound` and `eLpNorm_tendsto_top` occur in both current and
  historical files (five historical holes in addition to two current holes).
- `a00J02`: `abs_cont_sqrt_limit` occurs twice historically; one newer
  candidate has `lim_sqrt_zero_of_integral`.
- `a03J01`: `right_eq_lintegral` occurs in both a candidate and a historical
  file.
- `a93A03`: two candidates independently contain `radon_riesz`.
- `a96J01`: two candidates state the same uniform-convergence counterexample
  with different theorem names.

## High-leverage shared infrastructure

The following work is not literally duplicated, but one well-designed helper
layer should unblock several problems.

1. **Parametric integrals, DCT, and layer cake** — `a00J05`, `a01A02`,
   `a01A04`, `a01A06`, `a01A07`, `a01A09`, `a01A11`, `a93A02`, `a94A01`,
   `a94A03`.  Start with narrowly typed helpers for restriction to measurable
   sets, splitting improper integrals, dominated convergence, and
   differentiation under an integral.  This is the broadest payoff cluster.

2. **Fourier/convolution normalization** — `a01A03`, `a03J03`, `a92J03`,
   `a94A03`, `a94J04`.  Close `a92J03` first: it is only a `2π` convention
   bridge and will reveal the usable Mathlib Fourier API.  Then decide whether
   the missing Young/translation lemmas merit a shared module.

3. **Rouché/zero-counting infrastructure** — `a92J05`, `a94A10`, `a97A08`,
   with likely reuse in `a01J05` and `a93J07`.  Mathlib lacks the directly
   needed Rouché theorem.  Proving a reusable disk/circle form is expensive,
   but it converts several currently blocked exercises into short applications.

4. **Absolute continuity and variation** — `a93A04`, `a93J01`, and parts of
   `a01J03`.  A bridge between `eVariationOn`, disjoint interval sums, and the
   epsilon-delta AC definition would unlock both variation problems.

5. **Analytic power-series assembly** — `a00J06`, `a92J04`, `a96J10`.
   Investigate a common layer around `HasFPowerSeriesOnBall`, change of origin,
   and even/odd coefficient extraction before treating these independently.

6. **Contour substitution and residue applications** — `a01A10`, `a02J05`,
   `a92J06`, `a97A06`.  The recurring cost is not residue arithmetic but
   converting real improper integrals to parametrized complex contour
   integrals and controlling vanishing arcs.

## Current proof list (50 problems, 121 executable holes)

Items with more holes are listed first.  A count is useful for navigation, not
as a proxy for difficulty: a single missing theorem can be harder than five
local glue obligations.

| Problem | Holes | Main obligations / strategy | Effort |
|---|---:|---|---|
| `a94J04` | 6 | Poisson-kernel normalization/integrability/tail decay, `L²` contraction, approximate-identity convergence, and a.e. convergence. Young's inequality, translation continuity, and the Hardy-Littlewood maximal theorem are the major shared gaps. | XL |
| `a01A07` | 5 | Mean-value bound from disk `L¹` convergence, analyticity of the limit, then compact-uniform convergence of functions and derivatives. Build the disk estimate first; downstream statements form a chain. | XL |
| `a01J05` | 5 | Finiteness of analytic zero sets, Blaschke factorization, and derivative zero counting. The zero-count/argument-principle layer is the real blocker. | XL |
| `a94J02` | 5 | Construct a fat Cantor set, prove monotonicity and strict monotonicity of its complement-indicator integral, establish the a.e. derivative claim, then package the example. Existence of the fat Cantor set is the first reusable boundary. | XL |
| `a97A06` | 5 | Analytic auxiliary function, integrability, two vanishing-arc estimates, and the final `sin²(x)/x²` contour evaluation. Treat as a contour-infrastructure client, not five isolated holes. | XL |
| `a00J05` | 4 | Cauchy-transform differentiation, global holomorphy, large-`z` asymptotic, and non-entire conclusion. Part (b) depends on holomorphy plus the asymptotic. Share with `a01A11`. | L |
| `a01A06` | 4 | Admissibility of the exponential test function → distribution decay → layer-cake `L²` bound. This is a strict dependency chain; start with `test_function_admissible`. | L |
| `a93A02` | 4 | Uniform integrability from an `L²` bound, Fatou for the limit, finite-measure `L² → Lᵖ`, and UI under subtraction. The final Vitali application is already proved. | L |
| `a01A04` | 3 | Ball-volume slicing → DCT for slice powers → product/superexponential estimate. Each later result depends on the earlier one. | L |
| `a01A09` | 3 | Integrability of the Laplace integrand, analyticity by a parametric integral theorem, and the compact-support entire extension. Close local integrability before analytic assembly. | L |
| `a01A10` | 3 | Gaussian/Fresnel contour shift plus a `complete_square` algebra lemma. Close the algebra lemma as a quick reduction, but the contour argument remains large. | XL |
| `a01A12` | 3 | Argument doubling, the fourth-root/slit mapping, and composition of the conformal map. Prove precise image/preimage lemmas for each elementary map before composition. | L |
| `a02J01` | 3 | Pointwise Schur bound → Fubini/Tonelli interchange → `L²` operator estimate. A sequential proof; shared integral glue may reduce it. | L |
| `a02J03` | 3 | Indicator/rectangle bound → uniform bound on simple approximants → scaled-integral limit for general `L¹`. Start with compactly supported step functions and density. | L |
| `a02J06` | 3 | Second-order Schwarz bound, derivative bound, and rigidity/equality case. Search Mathlib's iterated Schwarz lemma and order-of-zero API before custom work. | M |
| `a93J07` | 3 | Hurwitz: eventual nonvanishing on a circle, persistence of zeros, then injective-or-constant/local limit conclusion. A reusable Rouché/argument-principle lemma would collapse the chain. | L |
| `a94A01` | 3 | Identify the a.e. limit of indicators, DCT for weighted set integrals, and the `Lᵖ`/symmetric-difference equivalence. The first two should be separable quick wins. | M |
| `a94A03` | 3 | Gaussian normalization, Young convolution inequality, and approximate-identity convergence via `Lᵖ` translation continuity. Young and translation continuity are missing infrastructure. | XL |
| `a94A04` | 3 | Two polynomial-linearity/integral glue holes, then density of polynomials in `L²` via Stone-Weierstrass and Cauchy-Schwarz. Close the first two cheaply; the final theorem remains L/XL. | L |
| `a97A07` | 3 | Show divided differences are polynomial, assemble the interpolation polynomial, and prove interpolation through the contour formula. Algebraic lemmas unblock the final statement. | L |
| `a97A08` | 3 | Root counts in radii `2` and `3/2`, then annulus subtraction. Both counts are Rouché applications; build one reusable theorem rather than bespoke root arguments. | XL |
| `a00J01` | 2 | Lower level-set bound and final `eLpNorm` limit. Share the general theorem with `a93J04`; ignore historical copies. | L |
| `a01A05` | 2 | Near-orthogonality control in Gram-Schmidt, then Bessel/series transfer. Part (b) depends on part (a). | L |
| `a01A11` | 2 | Cauchy-transform differentiation and large-`z` limit. Port/shared specialization of `a00J05` should close these. | S after shared lemma |
| `a01J01` | 2 | Uniform small-set estimate from the `L³` bound, then spike counterexample. The first is Hölder; likely close it before constructing the example. | M |
| `a01J02` | 2 | Borel representative of a measurable set, then Borel representative of a measurable function. The function result should be built from the set result or an existing ae-strongly-measurable theorem. | M |
| `a01J03` | 2 | Derivative of a monotone series and its a.e. form. Likely needs measure decomposition/monotone convergence for Stieltjes measures. | L |
| `a01J06` | 2 | Linear zero-count bound for exponential-type entire functions, then summability of weighted zeros. The second is elementary once the first exists. | L |
| `a02J02` | 2 | `rpow_sub_le` inequality and Radon–Riesz in `Lᵖ`. Close the scalar inequality first; use uniform convexity API if available. | M |
| `a02J07` | 2 | Endpoint FTC for a branch of log along a path, then argument bounds. Existing slit-log infrastructure is proved; remaining work is one-sided-limit integration glue. | L |
| `a03J03` | 2 | Continuity and vanishing at infinity of `Lᵖ * Lᑫ`. Both should follow from translation continuity plus Hölder; share Fourier/convolution infrastructure. | L |
| `a92J06` | 2 | Evaluate the circle contour and prove the `z=e^{iθ}` change of variables. The contour evaluation depends on residue/inside-outside root lemmas. | L |
| `a92J07` | 2 | Convert CR equations to an entire function, then derive constancy from the already-proved Liouville setup. The post-Liouville derivative step is likely the smaller first target. | L |
| `a93A04` | 2 | AC preservation under variation convergence, and Lipschitz approximation via truncated derivatives. Both need a substantial variation/AC bridge. | XL |
| `a93J06` | 2 | Radial integral identity for `f` and the resulting second-order Schwarz estimate. A focused interval-integral proof should unlock the final inequality. | M |
| `t94J01` | 2 | Ladder-chain extension/removal, then the clopen reachable-set equivalence with connectedness. The recorded blocker is `Fin` index transport, not missing mathematics. | M |
| `a00J04` | 1 | Final connected-component classification/counting assembly; all analytic helper lemmas are proved. Solve once for `a01A08` too. | XL |
| `a00J06` | 1 | Change origin for a formal power series, positivity of recentered coefficients, and Tonelli to contradict continuation at `1`. One hole hides a large proof. | XL |
| `a01A02` | 1 | Layer-cake on `|f|χ_E`, split at `sqrt(C/m(E))`, then ENNReal/Real arithmetic. A good first client for shared layer-cake helpers. | M |
| `a01A03` | 1 | Fourier convolution/derivative rule, the interval-indicator Fourier pair, and `L¹` Fourier injectivity. One hole hides a full Fourier proof. | XL |
| `a01A08` | 1 | Exact duplicate of `a00J04`; do not solve independently. | S after `a00J04` |
| `a02J05` | 1 | Dirichlet improper integral by contour integration, including indentation/principal-value control. Reuse contour substitution infrastructure. | L |
| `a03J08` | 1 | Show a piecewise reciprocal extends holomorphically across a finite pole set; existing removable-singularity ingredients are present. Mostly filter/set/`if` bookkeeping. | M |
| `a92J03` | 1 | Riemann–Lebesgue is already in Mathlib with the `2π` convention; prove the Fourier-character identity and transport along a scaling homeomorphism. Best immediate quick win. | S |
| `a92J04` | 1 | Turn pointwise power-series summability into `DifferentiableOn` on the disk; the Schwarz equality result is already proved. | M |
| `a92J05` | 1 | A single Rouché application; boundary estimates and no-boundary-root results are already proved. Blocked chiefly by the absent reusable Rouché theorem. | XL alone; S after Rouché |
| `a93J01` | 1 | Combine small variation near `0` with AC on `[a,1]`; remaining work is partition bookkeeping against the epsilon-delta definition. | L |
| `a93J04` | 1 | Upper/lower finite-measure `Lᵖ → L∞` squeeze. Share with `a00J01`. | S after shared lemma |
| `a94A10` | 1 | From a real critical point, use local factorization plus Rouché/argument principle (or an angular IVT argument) to produce a non-real point with real image. Existing factorization lemmas reduce it to the zero-counting boundary. | XL alone; S after Rouché |
| `a96J10` | 1 | Construct the analytic function from even Taylor coefficients and prove convergence on the full disk. Odd-coefficient vanishing is already proved. | L |

## Non-current-only HUD entries (10 problems, 31 executable holes)

These are listed before any further mathematical backlog because selection or
archival cleanup can remove them from the recovery metric without proving old
versions.

| Problem | Candidate holes | Historical holes | Status / recommended action |
|---|---:|---:|---|
| `a01A01` | 5 | 0 | Three-candidate set, no selected frame. Compare candidates and select or promote one current proof. |
| `a97A02` | 4 | 0 | Current status says **complete** and current `lean/` is clean. Exclude its old daily-batch candidate from HUD. |
| `a97A03` | 4 | 0 | Current status says **complete** and current `lean/` is clean. Exclude its old daily-batch candidate from HUD. |
| `a03J01` | 3 | 1 | Candidate plus historical duplicate. Select/promote the best candidate before proof work. |
| `a93A03` | 3 | 0 | Candidate set with duplicate `radon_riesz`. Choose the strongest candidate; do not clear both copies. |
| `a97A01` | 3 | 0 | Current status says **complete** and current `lean/` is clean. Exclude its old daily-batch candidate from HUD. |
| `a00J02` | 1 | 2 | Three candidates plus legacy history, no selected frame. Select the latest viable proof and archive the rest from the active metric. |
| `a96J01` | 2 | 0 | Six-candidate set; only two candidates carry holes. Selection may already yield a clean current proof. |
| `t94A04` | 2 | 0 | Two-candidate set, no selected frame. Compare statements and promote one before investing in simple-connectedness infrastructure. |
| `t97J01` | 1 | 0 | Six-candidate set; only one has a hole. A clean candidate may already exist. |

## Recommended clearing sequence

1. **Repair the metric and candidate selection first.** Restrict "current
   sorries" to the selected/current Lean artifact and count parsed lowercase
   `sorry`, not comments. This immediately removes ten false-positive problems
   and prevents work on obsolete copies.

2. **Take the low-risk quick wins:** `a92J03`, then API spikes on `a03J08`,
   `a92J04`, `a02J06`, and `t94J01`. These validate the current Mathlib surface
   and should improve the clean-problem count faster than attacking missing
   infrastructure first.

3. **Exploit exact duplicates:** make shared lemmas for the `Lᵖ → L∞` pair and
   the Cauchy-transform pair. Treat the lemniscate pair as one project.

4. **Build one analysis glue layer:** layer cake, restricted integrals, DCT,
   and parametric differentiation. Use `a01A02` as the smallest acceptance
   test, then apply it to the larger DCT cluster.

5. **Make explicit go/no-go decisions for missing infrastructure:** Rouché,
   Young convolution, variation/AC, and connected components. Each should have
   a standalone theorem statement and a small compile-tested spike before a
   multi-day proof effort.

6. **Only then attack contour-heavy and analytic-structure XL items.** They
   will benefit most from the shared layers and otherwise risk producing more
   isolated skeletons.

## Method

Canonical problem IDs came from `apm/*.tex`.  Every `problems/ID/**/*.lean`
file was scanned twice: once textually to reproduce the HUD and once with Lean
line/block comments and strings masked to identify executable lowercase
`sorry` tokens.  Current counts include only paths under `problems/ID/lean/`.
Declaration names, `status.json`, `proof-outline.md`, and the Lean source around
each hole were used for the dependency and effort notes.  No proof files were
changed during this survey.
