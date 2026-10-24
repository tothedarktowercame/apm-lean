# Backlog grading 2026-10-24: reviewer decisions on held rows (claude-14)

## Grader errors on smoothness order, overridden to faithful

The packets for batches 00–11 said "a bare ⊤ as a smoothness order is analytic".
Some graders applied that to `(⊤ : ℕ∞)`, which is C^∞. Checked against the
pinned Mathlib: `TestFunction`/`Distribution` take `n : ℕ∞`
(`Mathlib/Analysis/Distribution/TestFunction.lean:87`), and
`statement-registry.py fingerprint` reports no bare-⊤ flag for these statements.

- m99J02 (batch 07, graded vacuous): test functions are `ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ`, i.e. C_c^∞. The grader gave no other objection. Admitted faithful.
- m99J03 (batch 08, graded narrower): same test-function class; the grader says the three limits are correct. Admitted faithful.
- m03J03 (batch 04, graded narrower): `Distribution (⊤ : Opens ℝ) ℂ ⊤` is order ∞, the ordinary distributions. The grader says the four claims are represented. Admitted faithful.

## Held rows, regenerated over all 32 batches

`held-raw.txt` is now the complete list: `admit-batch.py NN` for NN = 00–31,
HELD lines only, prefixed by batch. 40 rows: 34 narrower, 4
hypothesis-carries-core, 1 vacuous (m00A04), 1 admit refused (a01A03, bare ⊤).
They stay unregistered; per the no-narrower-stand-ins rule they are open
statement repairs, not admissions.

## Batch 06 spot-checks (all grades upheld)

- m95J01 (hypothesis-carries-core): `[InnerProductSpace ℝ H]` plus `hinner`
  (Main.lean:290-297) assume the integral is a positive-definite inner product;
  part (a) asks to prove it. Upheld. `hT` correctly encodes (d/dx)² on
  e^{-x}p as p'' - 2p' + p.
- m95J02 (narrower): `hn : 2 ≤ n` (line 2101); the prose allows n = 1
  (fundamental solution |x|/2). Upheld. Test functions are C^∞ via
  `((⊤ : ℕ∞) : WithTop ℕ∞)`.
- m96J05 (hypothesis-carries-core): `hD`/`hT` (lines 193-201) posit D_ε and T
  as Fourier multipliers acting on f ξ directly; the physical-space difference
  and shift operators and the Fourier transform never appear. Upheld.
- Faithful check, m96J03: unit-ball indicator (33-34), C_c^∞ tests (77-79),
  ∫ 1_B Δφ = ∫_S Dφ(ω)ω d(volume.toSphere) (1899-1905), correct sign
  (divergence theorem) and unnormalised sphere area.

## Batch 30 (admitted 2026-10-24 during the final sweep)

Nine faithful rows admitted. Held m97A05 (narrower) checked: the theorem
(Main.lean:100-105) gives T, ∂x T = ∂y T and the wave equation but nothing for
part (b), the Fourier transform. Faithful check, m99A04: unique continuous
extension from a dense set (19-25), matches.

## Batch 05 spot-checks (all grades upheld)

Batch 05 was admitted in the earlier sweep (seven faithful rows registered);
these checks came after its late reply. Two of the three held rows narrow a
source claim that is false, so they belong on the false-problem.md list, not
the ordinary narrower list.

- m94J02 (narrower): lines 1107-1110 prove `‖fg‖ ≤ (5/4)‖f‖‖g‖`; part (c)
  asks for constant 1. The source is false: f = g = 1 + z gives ‖f‖ = 3 and
  ‖f²‖ = 1 + 2·2 + 5 = 10 > 9. The file says so (lines 8-10), and 5/4 is the
  sharp constant: max over k, m of ((k+m)²+1)/((k²+1)(m²+1)) is 5/4, at
  k = m = 1. Held; false source, repaired.
- m94J05 (narrower, correction 8cf4ec3ee): uniqueness only in a sup-norm
  ball. The file (lines 8-10) says unrestricted uniqueness is false at zero
  forcing; a negative solution of (t²x')' = x² with x(1) = x(2) = 0 exists
  beside x = 0 (superlinear Lane-Emden type). Held; false source, repaired.
- m95A04 (hypothesis-carries-core): `regular`/`hregular`, `Dtest`/`hDtest`,
  `Ddist`/`hDdist` (lines 645-654) are parameters, so parts (a) and (b), the
  embedding and the definition of the derivative, are assumed rather than
  constructed. Upheld.
- m94A04 (faithful): `IsFrechetDerivative` (lines 109-122) is a bounded
  L⁸→L² linear map with the o(‖h‖₈) remainder in L², and the theorem
  (364-372) gives a derivative at every f. Upheld.

## Batch 04 spot-checks (all grades upheld)

Batch 04 was admitted in the earlier sweep (seven rows registered: five
faithful, m03J02 stronger, m03J03 overridden to faithful above). These checks
came after its late reply. One of the three held rows narrows a false source.

- m93J03 (narrower): uniqueness only among solutions of size < η
  (Main.lean:689-698). The source is false: any solution has the form
  x = ε + A sin t + B cos t, and at ε = 0 the nonzero solution
  x = R sin(t + φ) needs R e^{2iφ} = -2π J₁(R). With φ = π/2 that is
  R = 2π J₁(R), which has a root R > 0 (2π J₁(R) ≈ πR > R near 0, and
  2π J₁(R) < R for R > 4). The file says so (lines 6-12). Held; false
  source, repaired.
- m93J02 (narrower): `hUnontrivial` and `0 < α < 1` (lines 689-693). The
  source is underspecified rather than false: for a singleton Ω, or for α = 1
  on an interval, (d) holds, while for 0 < α < 1 it fails (f(x) = x on [0,1]
  has local seminorm 0 and global 1). The file names both restrictions
  (lines 9-13). Held; not on the false-source list.
- m93J06 (narrower): part (c) adds a global Lipschitz hypothesis
  (lines 1815-1818) that the source does not need (continuity plus
  |f| ≤ C|y| gives global existence). The negated uniqueness clause for (d)
  is a fair repair, since without uniqueness the map y₀ ↦ y(t) is not
  defined, but (c) is an unforced narrowing. Held; not on the false-source
  list.
- m03J02 (stronger, admitted): uniqueness on all of ℝ (lines 20-21,
  501-504). f(u) = cos u - u is globally Lipschitz, so the backward solution
  exists, and a forward solution on t > 0 extends uniquely to ℝ. Upheld.
- m93J01 (faithful): κ = 1/12, the expansions with O(h⁶) and O(h⁴) in place
  of the false o(·) (lines 166-183), and the Numerov residual
  (1 - h²V₊/12)y₊ - (2 + 5h²V/6)y + (1 - h²V₋/12)y₋ = O(h⁶) (184-190). I
  rederived the h²(Ly) identity: the + sign on κh⁴y⁽⁴⁾ is right. Upheld.

## Batch 07 spot-checks

Batch 07 was admitted in the earlier sweep (eight rows registered: six
faithful, m96J06 stronger, m99J02 overridden to faithful above). These checks
came after its late reply. One held row is overridden; the other stays held.

- m97A04 (graded narrower, overridden to faithful): the theorem assumes
  `∀ t ∈ Set.Icc 0 1, b t < 0` (Main.lean:569). The source says "if
  b(t)<0 for all t", not "for 0<t<1", so the closed interval is within what
  problem.md states. (The open-interval version is also true, because the
  stencil only evaluates b at interior mesh points, but the problem does not
  ask for it.) The stencil identity (552-568) is the correction from 541f88367.
  Admitted faithful with this file as evidence. This leaves 39 held rows,
  33 of them narrower; `held-raw.txt` still lists m97A04 as raw output.
- m98A05 (narrower): confirmed. The only declaration is `lemma
  apm_m98a05_ift` (line 17), the generic IFT; the perturbation claim (b)
  and the H²(0,π) existence claim (c) were deleted in 93c400876. Not a false
  source: (b) is false for arbitrary ε₀, but the bank already repaired that
  with ε₀ = 0, and (c) is true. Held; not on the false-source list.
- m99J02 (graded vacuous, already overridden): rechecked against the pinned
  Mathlib: `((⊤ : ℕ∞) : WithTop ℕ∞) = ∞` is `rfl` and `≠ ω` by `decide`. The
  jump term is right: g' jumps by u₁(y)u₂'(y) − u₁'(y)u₂(y) = W(y), and
  under the ODE W is constant, so c = W(0) (lines 278-290). Upheld faithful.
- m96J06 (stronger, admitted): the extra conclusion |x| ≤ 1/12 on the ball
  |y| < 1/48 is added to the exact equation. Upheld.
- m99J01 (faithful): ODE imposed only for t ≥ 0 (lines 19-21), uniqueness on
  t ≥ 0, unique ξ = cos ξ with every solution tending to ξ (502-512). Upheld.

## Batch 08 spot-checks

Batch 08 was admitted in the earlier sweep (eight rows registered: six
faithful by the grader, a00J06 stronger, m99J03 overridden to faithful above).
These checks came after its late reply. One admission is revoked; both held
rows are now admitted.

- a00J06 (graded stronger, admission revoked): `f a := (p a).sum`, and
  `FormalMultilinearSeries.sum` is a `tsum`, which Lean sets to 0 where the
  series is not summable. So `f a x = 0` for every x > 1, and the theorem
  `¬ ∃ ρ, 0 < ρ ∧ AnalyticAt ℝ (f a) 1` (Main.lean:93-96) follows from
  "positive just left of 1, zero just right of 1". The proof's own docstring
  takes that route. Pringsheim's theorem is never used, and `ρ` is unused.
  The problem asks that no analytic g near 1 agree with f on the part of the
  disk |z| < 1 near 1; a real form that would be faithful is: no g with
  `AnalyticAt ℝ g 1` and g = f on (1 - r, 1) for some r > 0. Held as
  vacuous (junk-value statement); a repair needs a real proof.
- a00J03 (graded narrower, repaired and admitted faithful): `he_symm` was
  derivable, since μ(φA) = μ(φ⁻¹(φA)) = μ(A). I removed it from
  `composition_isometric_isomorphism` and derived it inside the proof
  from Mathlib's `MeasurePreserving.symm e he`. The file compiles
  (`lake env lean`, warnings only). Admitted with `composition_isometry` and
  `composition_isometric_isomorphism` pinned. The old canary copy under
  `ApmCanaries/Frames/A00J03/` is unchanged.
- a01A03 (graded faithful, admit refused, now admitted): the refusal was
  for the bare ⊤ in `convolution_identity_counterexample` (line 229), the
  compiled refutation of the old analytic-test version. The pin-every-theorem
  fallback in `admit-batch.py` had picked it up. The graded theorem
  `convolution_identity_implies_indicator` (98-104) uses `ContDiff ℝ ∞`;
  admitted with that declaration pinned. Restricting the hypothesis from
  C^1 to C_c^∞ weakens it (so the theorem is at least as strong), and it is
  the class where g * f' is defined for g ∈ L¹.
- m99J03 (narrower, already overridden): rechecked. Same `(⊤ : ℕ∞)`
  test class as m99J02.
- Faithful check, a00J02: f(x)/√x → 0 from the right under absolute
  continuity, f(0) = 0 and f' ∈ L² (lines 119-126). Upheld.

`admit-batch.py` now skips ids in the registry's `revoked` list and reports
them as HELD; without that, rerunning batch 08 re-admitted a00J06. Held
count after batch 08: 38 rows, 32 of them narrower, plus a00J06 revoked.
(`admit` fingerprints the committed revision. My first a00J03 admission came
before the repair was committed and pinned the old statement, so it was
revoked and redone at the repaired revision. The `revoked` list keeps that
first entry, but `admit-batch.py` checks `entries` first, so a00J03 is not
reported as held.)

## Batch 09 spot-checks (all grades upheld)

Batch 09 was admitted during the earlier sweep (rev 8fccb9498); rerunning
`admit-batch.py 09` changes nothing and prints a01A11 as HELD.

- a01A11 (hypothesis-carries-core): `cauchyTransform_not_entire`
  (Main.lean:246-251) takes `h_diff`, `h_decay` and `h_nonzero` as
  hypotheses. Upheld. Repair route: `h_diff` is part (a)
  (`cauchyTransform_differentiableAt`), `h_decay` follows from part (c)
  (z g(z) → -|K| gives g → 0), and `h_nonzero` from
  Im g(i) = ∫_K 1/(t²+1) dt > 0 because volume K > 0.
- a01A05 (faithful, refutes printed part (a)): checked against problem.md.
  Part (a) is false in either indexing: two unit vectors with inner product
  ε = 2^{-m} give ‖f_m - e_m‖² = 2 - 2√(1-ε²) > ε². The Lean structure keeps
  the problem's hypothesis with 0-based indices (Main.lean:30-35). Its
  negation is stated as `¬ ∀ H`, with the witness in ℓ² rather than L². That is
  harmless because ℓ² embeds isometrically in L². Upheld. This is a false
  source to add to the list.

## Batch 10 spot-checks (all grades upheld)

Batch 10 was admitted during the earlier sweep; rerunning `admit-batch.py 10`
changes nothing and prints a02J03 as HELD.

- a02J03 (narrower): `scaled_integral_vanishes` (Main.lean:406-411) has
  `φ f : ℝ → ℝ` and tests only `Set.Icc a b`; problem.md is on ℝⁿ with
  n-dimensional rectangles. Only n = 1 is proved. Upheld; held.
- a01J03 (stronger, admitted): `deriv_sum_of_monotone_ae` (Main.lean:151-156)
  drops problem.md's `f_n ≥ 0`. The stronger claim is still true: summability
  at 0 lets one subtract f_n(0), and the shifted summands have one sign on each
  half-line, so Fubini's differentiation theorem applies on each. Upheld.
- a01J06 (faithful): `EnumeratesZeros` (Main.lean:25-28) makes each fiber of
  ω : ℕ → ℂ finite with cardinality `analyticOrderNatAt f z`. Upheld. Caveat:
  an ℕ-indexed ω cannot enumerate finitely many zeros, so f with finitely many
  zeros satisfies no hypothesis; the problem's conclusion is a finite sum there,
  so nothing of substance is lost.

## Batch 11 spot-checks (all grades upheld)

Batch 11 was admitted during the earlier sweep; rerunning `admit-batch.py 11`
changes nothing and prints a02J07 as HELD.

- a02J07 (narrower): `SlitPath` (Main.lean:125-136) requires
  `DifferentiableAt ℝ γ t` at every t ∈ (0,1]. problem.md allows a piecewise
  smooth path, which has corners where γ is not differentiable, so paths with
  corners are excluded. The `integrable_logDeriv` field (repair 877118590) is
  harmless: γ'/γ is integrable for any piecewise smooth path avoiding 0.
  Upheld; held. Repair route: allow finitely many non-differentiable points
  (differentiable off a finite set, or a partition with C¹ pieces).
- a03J06 (stronger, admitted): `apm_a03j06` (Main.lean:70-73) takes `m : ℕ`,
  so m = 0 is included; the claim is still true there (bounded entire ⇒
  constant). Upheld.
- a03J01 (faithful): `apmMultiplicitySet` (Main.lean:22-25) uses
  `encard = j`, so points lying in infinitely many E_k belong to no F_j. Under
  A < ∞ that set is null (Borel–Cantelli), so the identity is unaffected.
  Upheld.

## Batch 12 spot-checks (all grades upheld)

Batch 12 was admitted during the earlier sweep; rerunning `admit-batch.py 12`
changes nothing and prints a92J03 as HELD.

- a92J03 (narrower): `fourier_maps_L1_to_C0` (Main.lean:109-113) states
  continuity, the bound by ‖f‖₁, and `Tendsto … (cocompact ℝ) (𝓝 0)` for every
  integrable f, which is stronger than part (c). problem.md's closing sentence
  also asks that f ↦ f̂ be a linear map L¹(ℝ) → C₀(ℝ), and no declaration states
  linearity. Upheld; held. Repair route: add the linearity conjunct
  (f̂ of a·f + b·g equals a·f̂ + b·ĝ for integrable f, g), or package the map as
  a linear map into the bounded continuous functions vanishing at infinity.
- a92J02 (stronger, admitted): `convergesInMeasure.exists_subseq_ae_tendsto`
  (Main.lean:127-131) works over any `μ : Measure α` with no measurability
  hypothesis on fₙ or f; `ConvergesInMeasure` (34-36) is the problem's ε/N
  condition verbatim. Lebesgue measure on ℝ is an instance. Upheld.
- No smoothness-order objection in this batch: a92J07 uses `ContDiff ℝ 1`,
  which is C¹ as the problem asks, not a bare ⊤.

## Batch 13 spot-checks (all grades upheld)

Batch 13 was admitted during the earlier sweep; rerunning `admit-batch.py 13`
changes nothing and holds no row.

- a93J04 (stronger, admitted): `tendsto_eLpNorm_atTop` (Main.lean:67-73)
  works over any measure with `μ univ < ⊤`, assuming AE-strong measurability
  and `eLpNorm f ⊤ μ ≠ ⊤`. A bounded Lebesgue-measurable f on [0,1] satisfies
  both, so the problem's claim is an instance. The `⊤` is the L^∞ exponent,
  not a smoothness order. Upheld.
- a93J02 (faithful): problem.md asks for the identity to be justified via
  dominated convergence; the grade treats that as a proof-method hint, and the
  statement is the series identity itself. Upheld.
- No smoothness-order objection in this batch: no `ContDiff` appears in any
  batch 13 statement.

## Batch 14 spot-checks (all grades upheld)

`admit-batch.py 14` admits eight rows and holds two. One of the two held rows
narrows a false source.

- a94A05 (narrower): `vitali_covering_lemma_5` (lines 116-121) covers a union
  of closed balls by closed 5ρ-balls. problem.md part (a) takes open
  subintervals and asks for the cover by the concentric *open* intervals five
  times as long, by a (possibly finite) sequence. Closed-5ρ containment does
  not give open-5ρ containment. Part (b) (lines 148-155) is faithful. Held; not
  on the false-source list. Repair route: state (a) for a family of `Ioo`
  intervals in a bounded interval, with a countable pairwise-disjoint
  subfamily whose open 5x enlargements cover U. The open version holds by the
  usual argument: x lies strictly inside some I_a, which meets a chosen I_j
  with r_j ≥ r_a/2, so |x - c_j| < 2r_a + r_j ≤ 5r_j.
- a94J02 (narrower): the statement restricts absolute continuity,
  integrability, nonnegativity and strict monotonicity to `Icc 0 1`. The
  source is false on ℝ: if h ≥ 0 is strictly increasing then h ≥ h(1) > 0 on
  [1, ∞), so h is not integrable (the decreasing case is symmetric on
  (-∞, -1]). Held; false source, repaired (`25d04f7c7` added the
  absolute-continuity and interval-integrability conjuncts).
- a94A04 (stronger, admitted): `zero_of_orthogonal_to_monomials`
  (lines 78-86) works for any μ with μ restricted to [0,1] finite; Lebesgue
  measure is an instance. The finite-measure instance added in `56f0b8e5c`
  stops zero moments arising from `integral_undef`. Upheld.
- No smoothness-order objection in this batch: no `ContDiff` appears in any
  batch 14 statement.

## Batch 15 spot-checks (all grades upheld)

The six faithful rows were already in `STATEMENTS.json` when
`admit-batch.py 15` ran, so it admitted nothing new and holds four. None of
the four is on the false-source list.

- a94J04 (narrower): `poissonConv_L2_contraction` (lines 200-203) bounds
  `eLpNorm (poissonConv y f) 2` by `eLpNorm f 2` for each representative, and
  `poissonConv_tendsto_L2` / `poissonConv_tendsto_ae` (503-538) cover (b) and
  (c). problem.md (a) asks that P_y extend to a bounded *linear* operator on
  L²; no declaration builds a map on `Lp ℝ 2` or states linearity or
  independence of the representative. Held.
- a94J05 (narrower): `liouville_bounded` and `liouville_re_bounded_below`
  (lines 55-74) are (a) and (b). problem.md first asks to state Cauchy's
  integral formula; nothing in the file states it. Held.
- a95A01 (narrower): `indicator_not_riemann_integrable` (line 291) is stated
  for the literal `K.indicator 1`. problem.md (b) takes any f equal to χ_K
  almost everywhere. That version is still true (f is discontinuous at every
  density point of K: near such a point f = 1 on a positive-measure part of K
  and f = 0 a.e. on the open, nonempty complement), so this is a gap, not a
  false source. Held.
- a95A03 (narrower): `f_radial_conv_L2_bound` (lines 547-550) gives the
  constant 2π², but nothing asserts `MemLp (f ∗ g) 2`; the norm bound alone
  does not give AE-strong measurability. Held.
- No smoothness-order objection in this batch: no `ContDiff` appears in any
  batch 15 statement.

## Batch 16 spot-check (all grades upheld)

The nine faithful rows were already in `STATEMENTS.json` when
`admit-batch.py 16` ran, so it admitted nothing new and holds one row. That
row narrows a false source.

- a95A06 (narrower): two departures from problem.md. (1) `lacunarySeries`
  (Main.lean:53-54) sums from n = 0, so it is the source's f plus z (0! = 1! = 1);
  the properties carry over, but the declarations are about a different
  function. That part is an unforced gap. (2) `lacunarySeries_natural_boundary`
  (lines 403-407) excludes extensions only on connected U (repair 83720e197).
  Here the source is false as written: U = Δ ∪ a disjoint open disc properly
  contains Δ and carries an analytic F agreeing with f on Δ, and the file
  proves exactly this (`lacunarySeries_has_disconnected_extension`, lines
  177-220). Held; on the false-source list for (b). The n = 0 offset still
  needs repairing to n = 1 before admission.
- No smoothness-order objection in this batch: no `ContDiff` appears in any
  batch 16 statement (the one in a95A06 Main.lean:296 is inside a proof).

## Batch 18 spot-check (all grades upheld)

All ten rows graded faithful, and all ten were already in `STATEMENTS.json`, so
`admit-batch.py 18` admitted nothing and held nothing.

- a96J08 (faithful, correction): problem.md records that the informal
  solution's boxed answer -π cot(πω) is a sign slip; its own last line gives
  +π cot(πω). The source asks only to evaluate the integral, so the corrected
  target is the true value of what is asked, not a narrowing. The old sign has
  axiom-clean refutations at ω = 1/4 and 3/4. Upheld.
- a96J05 (faithful, correction): the correction is to the registry (the first
  bank file held only auxiliary lemmas); `apm_a96j05` states vector-space
  closure, the norm axioms and completeness, as problem.md asks. Upheld.
- a96J07: the source's ill-typed `b < R` is read as `|b| < R`, and the
  coincident-pole case is split off. Both are forced. Upheld.
- No smoothness-order objection: no `ContDiff` in any batch 18 file; every `⊤`
  (a97A01, a97A02) is an `ENNReal` Lᵖ exponent.

## Batch 17 spot-check (all grades upheld)

`admit-batch.py 17` held a96A04 and admitted nothing new: the other nine rows
(three stronger, six faithful) were already in `STATEMENTS.json`.

- a96A04 (narrower): held. problem.md asks for the heat semigroup on ℝⁿ (its
  `f ∈ L²(ℝ)` is inconsistent with the `(4πt)^{-n/2}` factor and the `∫_{ℝⁿ}`,
  so the n-dimensional reading is the intended one). `heatKernel`, `heatConv`
  and all three theorems are typed on ℝ, i.e. only n = 1. Needs re-encoding
  over `EuclideanSpace ℝ (Fin n)`. Smoothness order is fine: Main.lean:93 and
  :705 use `ContDiff ℝ ∞` under `open scoped ContDiff`, which is C^∞; the
  bank's bare `⊤` (analytic) was correctly replaced.
- a96A02 (faithful, correction): the bank's constant-zero placeholder made the
  non-AC theorem false; the exact triangular-spike specification matches
  problem.md (f(1/n) = 0, peak 1/n at the midpoint of [1/(n+1), 1/n]). Upheld.
- a95J07 / a95J08 / a96J01 (stronger): dropping the nonemptiness hypothesis,
  `1 ≤ p` for `1 < p`, and continuity on all of ℝ each imply the stated
  problem. Upheld.
- No other `ContDiff` in any batch 17 statement.
