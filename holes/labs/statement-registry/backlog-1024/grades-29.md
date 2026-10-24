| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| m93J05 | faithful | The combined theorem gives the adjoint identity, kernel/range splitting, weak lower semicontinuity, existence of a minimizer, and the variational stationarity equations. | correction: the bank encoded lower semicontinuity in the reverse (false) direction and allowed non-`Lᵖ` variations; both statement changes correct those defects. |
| m94A01 | narrower | It assumes full `ContDiff ℝ 4 u`, whereas the problem only assumes continuity of the two pure fourth derivatives `u_xxxx` and `u_yyyy`. | — |
| m94A02 | faithful | For an ordered spectrum of the symmetric part it bounds every complex eigenvalue's real part by the extreme eigenvalues and proves skew-symmetric matrices have purely imaginary eigenvalues. | — |
| m94J03 | faithful | For every resolvent-set point of a compact self-adjoint operator it states exactly the inverse-distance resolvent estimate. | — |
| m94J06 | faithful | It states Fréchet differentiability of inversion on the invertible bounded operators of a Banach space (over any `RCLike` field). | — |
| m95A01 | faithful | It states both operator-norm convergences, the conditional uniform bound, and pointwise convergence to a bounded two-sided inverse under surjectivity. | — |
| m95A05 | faithful | Reflexivity and the stated coercivity hypothesis imply existence and uniqueness for every dual datum. | — |
| m95J05 | faithful | It defines fundamental solutions and C∞ compactly supported test functions, verifies the causal kernel, and solves the inhomogeneous equation by convolution. | correction: the smoothness-order repair from bare `⊤` to the explicit `ℕ∞` infinity corrected an analytic/vacuous encoding to genuine C∞ test functions. |
| m95J06 | faithful | It proves both the finite-dimensional `p→∞` norm limit and differentiability of the real Hilbert norm away from zero. | — |
| m96A01 | faithful | Using Mathlib's standard compact-operator predicate, it proves every nonzero eigenspace is finite-dimensional. | — |

### Evidence

**m93J05.** Graded `apm_m93j05`, lines 4248–4276. Its first conjunct is the adjoint relation `∫ Φ f * g = ∫ f * Φ g` (4252–4253); lines 4254–4258 characterize the kernel by vanished Fourier coefficients and split every `f` into an element fixed by `Φ` plus a kernel element, thereby describing the finite-dimensional image/cokernel decomposition. Lines 4259–4267 give weak lower semicontinuity as `( ∃ᶠ n, J(s n) ≤ r) → J f ≤ r`; 4268–4270 give a minimizer; and 4271–4276 give zero directional derivative in every `Lᵖ` direction. The original bank direction `( ∀ᶠ n, r ≤ J(s n)) → r ≤ J f` was refuted in the file by high-frequency sine functions weakly converging to zero, so the repair is a correction. No axiom, opaque definition, or sorry-typed dependency was found.

**m94A01.** Graded `apm_m94a01`, lines 83–87: `(hu : ContDiff ℝ 4 u)` implies, locally at every `(x,y)`, `|Δu-T_hu| ≤ C h²`. The conclusion faithfully expresses the requested error order and appropriately chooses local `C,δ`; however, full `C⁴` on `ℝ²` requires all partial derivatives through order four, strictly more than continuity only of `u_xxxx` and `u_yyyy`. No axiom, opaque definition, or sorry-typed dependency was found.

**m94A02.** Graded `apm_m94a02`, lines 146–155. `apm_m94a02_IsOrderedSpectrum` (lines 80–83) requires decreasing `σ` and `charpoly B = ∏_i (X-C(σ_i))`. The theorem concludes `σ(last) ≤ Re λ ∧ Re λ ≤ σ(0)` and, if `A.transpose=-A`, `Re λ=0`. Encoding positive matrix size as `Fin (n+1)` is faithful to the conventional `n≥1` setting. No axiom, opaque definition, or sorry-typed dependency was found.

**m94J03.** Graded `apm_m94j03`, lines 18–24: for complex Hilbert `H`, compact self-adjoint `A`, and `z ∈ resolventSet ℂ A`, `‖resolvent A z‖ ≤ (infDist z (spectrum ℂ A))⁻¹`. Restricting `z` to the resolvent set merely makes explicit where `(z-A)⁻¹` exists. No axiom, opaque definition, or sorry-typed dependency was found.

**m94J06.** Graded `apm_m94j06`, lines 24–28. `m94J06GL` is `{T | IsUnit T}` and `m94J06Inverse` returns the unit inverse there; the conclusion is `DifferentiableOn 𝕜 ... GL`. Generalizing from complex scalars to `RCLike` scalars is harmless strengthening, not a loss of fidelity. No axiom, opaque definition, or sorry-typed dependency was found.

**m95A01.** Graded `apm_m95a01`, lines 57–73. `m95A01Iterates` has exactly `B₀` and `Bₙ₊₁=2Bₙ-BₙABₙ`. The conclusion contains `A Bₙ→1` and `Bₙ A→1` in operator norm, a surjectivity-conditional `∃K, ∀n, ‖Bₙ‖<K`, and a bounded two-sided inverse with `Bₙx→Ainv x`. No axiom, opaque definition, or sorry-typed dependency was found.

**m95A05.** Graded `apm_m95a05`, lines 83–91: complete real normed `V`, surjectivity of the canonical map into the double dual (reflexivity), continuous linear `A : V → V'`, `c>0`, and `c‖v‖² ≤ A v v` imply `∃!u, A u=f`. This is the requested abstract coercive solvability theorem. No axiom, opaque definition, or sorry-typed dependency was found.

**m95J05.** Graded `apm_m95j05`, lines 180–188, together with definitions at lines 10–27. A fundamental solution is defined by `A T = dirac`; a test function is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ`, which means C∞ (not analytic); the causal kernel is `e^(-λt)` for `t≥0`; and the solution integral satisfies `v' + λv = φ` and is C∞. The 2026-10-13 history explicitly repairs the earlier bare-`⊤` analytic order whose compactly supported functions collapsed, so this is a correction. No axiom, opaque definition, or sorry-typed dependency was found.

**m95J06.** Graded `apm_m95j06`, lines 161–166: for every nonempty finite coordinate type, `Tendsto (fun p:ℝ => lpNorm p x) atTop (nhds linfNorm x)`, and for every real inner-product space the norm is `DifferentiableAt` every nonzero point. Both requested parts are present. No axiom, opaque definition, or sorry-typed dependency was found.

**m96A01.** Graded `apm_m96a01`, lines 21–26. It assumes `IsCompactOperator L` (Mathlib's standard formal definition of compact linear transformation) and proves `FiniteDimensional ℂ (ker (L-λ id))` for every `λ≠0`, exactly the stated eigenspace. No axiom, opaque definition, or sorry-typed dependency was found.
