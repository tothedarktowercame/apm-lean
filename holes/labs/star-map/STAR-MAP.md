# Prelim star map: skills

112 skills over 484 problems. `both` means the informal solution names the skill
and the Lean proof reaches a matching Mathlib constant. `named` means the informal side alone
names it emphatically. Tags are for study planning and carry the error rates in README.md.
Built by build.py; edit concepts.tsv, not this file.

## Complex

### Cauchy integral theorem and formula (9 both, 9 named)

both: `a92J06` `a94A09` `a94J06` `a95J03` `a95J04` `a96A05` `a96A06` `a96J07` `a98A07`
named: `a00J05` `a01A07` `a01A09` `a01J04` `a03J06` `a94J05` `a97A06` `aunk04` `aunk05`

Lean: `circleIntegral.integral_sub_inv_of_mem_ball`, `circleIntegral.integral_congr`, `circleIntegral.integral_const_mul`, `circleIntegral.integral_sub`, `circleIntegral.eq_1`

- a94J06: Evaluate integral for Case 1 (warrant: Cauchy integral formula). Lean: `apm_a94J06_inside`.

- a96A06: the Taylor coefficients of g decay superexponentially (warrant: Cauchy estimates). Lean: `cauchy_estimate_taylor`.

### Residues and contour integrals (7 both, 17 named)

both: `a01J05` `a92J06` `a94A09` `a94J06` `a96A05` `a96A06` `a97J08`
named: `a01A10` `a01J04` `a02J05` `a03J05` `a94A06` `a94J05` `a95A07` `a96J07` `a96J08` `a97A06` `a97J05` `a97J06` `a98A05` `aunk03` `b00J02` `b01J02` `b99A02`

Lean: `circleIntegral.integral_sub_inv_of_mem_ball`, `circleIntegral.integral_sub_center_inv`

- a94J06: Evaluate integral for Case 1' (warrant: residue theorem). Lean: `apm_a94J06_at_zero`.

- a95A07: At z = n != 0, the residue of g(z) is 1/(2*pi*i*n^2) (warrant: At z = n != 0, the residue of g(z) is 1/(2*pi*i*n^2)).

### Argument principle and Rouché (0 both, 11 named)

named: `a01J05` `a92J05` `a93J07` `a94A09` `a94J07` `a95J03` `a96A07` `a97A08` `a97J08` `aunk04` `t94J06`

- a94A09: Rouché comparison with big part h and small part -f (warrant: Rouché comparison). Lean: `apm_a94a09_exists_zero_of_zeroCount_ne_zero`.

- a97J08: f_n and g have the same number of zeros inside Gamma (warrant: Rouché's theorem). Lean: `apm_a97j08_curveImage_compact`.

### Maximum modulus (4 both, 7 named)

both: `a00J04` `a01A08` `a01J05` `a97J07`
named: `a02J06` `a03J07` `a94A08` `a95A05` `a99J07` `b99A01` `m02A06`

Lean: `Complex.norm_le_of_forall_mem_frontier_norm_le`, `Complex.eqOn_closure_of_isPreconnected_of_isMaxOn_norm`

- a95A05: g ≡ 0 on Δ by the maximum modulus principle (warrant: maximum modulus principle). Lean: `eq_zero_on_closure_of_frontier_zero`.

- a97J07: g attains its maximum on the boundary (warrant: The maximum modulus principle applies to g.).

### Schwarz lemma and automorphisms of the disc (7 both, 1 named)

both: `a01A12` `a02J06` `a92J04` `a94A08` `a95A08` `a95J01` `a96J06`
named: `a01J05`

Lean: `dslope`, `Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div`, `dslope_same`, `Complex.norm_dslope_le_div_of_mapsTo_ball`

- a95J01: The composition $h = g^{-1} \circ f$ satisfies $|h^{\prime}(0)| \leq 1$. (warrant: Schwarz lemma). Lean: `schwarz_deriv_bound`.

- a96J06: Schwarz's lemma yields |q(w)|≤|w| and |q′(0)|≤1 (warrant: Schwarz's lemma).

### Liouville and entire functions (8 both, 8 named)

both: `a01A11` `a92J07` `a93J05` `a94A07` `a94A10` `a94J05` `a94J08` `a95J02`
named: `a00J05` `a01A09` `a01J04` `a01J06` `a03J06` `a03J08` `a96J07` `aunk04`

Lean: `Differentiable.apply_eq_apply_of_bounded`, `Differentiable.exists_const_forall_eq_of_bounded`

- a94A10: Since $f$ is entire and nonconstant, $f$ has a zero of order $n \geq 2$ at $x_{0}$ for $g(z) := f(z) {-} f(x_{0})$ (warrant: definition of an entire function). Lean: `nonconstant_of_realIffReal`.

- a01J06: Let $f(z)$ be an entire function (warrant: Definition of entire function). Lean: `apm_a01J06_logCounting_top_eq_zero`.

### Morera and uniform limits of analytic functions (5 both, 4 named)

both: `a01A07` `a93J07` `a97J08` `a98A07` `aunk05`
named: `a00J05` `a01A09` `a01A11` `a99J09`

Lean: `TendstoLocallyUniformlyOn.differentiableOn`

- a01A09: G(z) is analytic (warrant: Morera's theorem).

- a01A11: g is analytic on \mathbb{C} \setminus K (warrant: Morera + Fubini).

### Identity theorem and zeros (5 both, 4 named)

both: `a93J07` `a94A10` `a95A05` `a95J02` `aunk02`
named: `a92J04` `t03J04` `t91A01` `t96A06`

Lean: `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, `analyticOrderAt`, `analyticOrderAt_eq_top`, `AnalyticAt.analyticOrderAt_ne_zero`, `analyticOrderAt_ne_zero`

- a92J04: By the identity theorem for power series, a_n equals 0 for all n greater than or equal to 2 (warrant: identity theorem for power series).

- a94A10: The local mapping behaviour near $x_{0}$ (warrant: definition of a zero of order n).

### Conformal maps and Möbius transforms (0 both, 5 named)

named: `a01A12` `a97A05` `t01A01` `t03J03` `t97A01`

- a01A12: The final composition of the conformal map is a one-to-one map. (warrant: The full composition of the conformal map is a one-to-one map.).

### Harmonic functions (0 both, 7 named)

named: `a00J05` `a01A07` `a01A11` `a94J04` `a95A04` `a95A08` `a98J03`

- a94J04: Py extends to a bounded linear operator Py:L2(R)→L2(R) with operator norm less than or equal to one. (warrant: The Poisson kernel is a probability measure and a convolution kernel). Lean: `poissonConv_L2_contraction`.

### Series, Laurent and singularities (5 both, 2 named)

both: `a03J08` `a94A07` `a95J03` `a97J05` `a98A06`
named: `a02J06` `a96A06`

Lean: `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`, `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt`, `Function.FactorizedRational.meromorphicOrderAt_eq`, `meromorphicOrderAt`, `meromorphicOrderAt_eq_int_iff`

- a98A06: Riemann's theorem extends g across the origin (warrant: Riemann's removable singularity theorem).

- a03J08: g extends to an entire function (warrant: Riemann removable singularity theorem).

### Branches of log and logarithmic derivative (4 both, 0 named)

both: `a01J05` `a02J07` `a92J07` `a99J06`

Lean: `Complex.log_im`, `Complex.exp_log`, `logDeriv`, `logDeriv_mul`, `logDeriv_fun_pow`

- a99J06: g is a holomorphic logarithm of f (warrant: g is a holomorphic logarithm of f). Lean: `apm_a99j06_exists_log_of_logDeriv_exact`.

- a02J07: Let γ be a piecewise smooth differentiable path (warrant: definition of the principal logarithm).

### Normal families (0 both, 0 named)


### Infinite products and partial fractions (0 both, 5 named)

named: `a94J06` `a96A08` `a96J07` `a96J08` `t93J01`

- a94J06: Use partial fractions (warrant: partial fraction decomposition). Lean: `partial_fractions`.

- a96A08: The integral of sin(πx) / (x^2-x) is -2π. (warrant: Informal proof (partial fractions)).

## Measure

### Dominated convergence (13 both, 7 named)

both: `a00J05` `a01A04` `a01A09` `a01A11` `a02J02` `a93A04` `a94A01` `a98A02` `a98A07` `a99J03` `a99J09` `m96J05` `m99J03`
named: `a92J03` `a93J02` `a96A01` `a96A03` `a96A04` `a96J03` `a98J03`

Lean: `MeasureTheory.tendsto_integral_of_dominated_convergence`, `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `MeasureTheory.tendsto_lintegral_of_dominated_convergence'`

- a98A07: The sequence f_n(z) converges uniformly to f(z) on every compact subset of D. (warrant: Dominated Convergence Theorem). Lean: `apm_a98A07_tendstoUniformlyOn_closedBall`.

- m96J05: Convergence of exp(D_epsilon) to T in L^2 (warrant: dominated convergence theorem). Lean: `apm_m96J05_bridge_1`.

### Monotone convergence and Fatou (4 both, 5 named)

both: `a03J01` `a97J01` `a98A04` `m02J05`
named: `a01J03` `a02J02` `a93A02` `a96A03` `a99J10`

Lean: `MeasureTheory.lintegral_tsum`, `MeasureTheory.lintegral_iSup_ae`, `MeasureTheory.lintegral_liminf_le'`

- a96A03: The limit function f belongs to B (warrant: Fatou's lemma). Lean: `memLp_limit_of_ae_tendsto_bounded`.

- a97J01: the integral of f^+ over R is less than or equal to c (warrant: Monotone Convergence Theorem).

### Fubini and Tonelli (8 both, 8 named)

both: `a01A02` `a02J01` `a02J04` `a03J04` `a95A03` `a95J08` `a99J03` `m02J06`
named: `a00J05` `a01A04` `a01A06` `a01A09` `a01A11` `a03J01` `a94A02` `a96J02`

Lean: `MeasureTheory.Integrable.integral_prod_left`, `MeasureTheory.lintegral_eq_lintegral_meas_lt`, `MeasureTheory.Integrable.integral_prod_right`, `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`, `MeasureTheory.Integrable.prod_right_ae`

- a96J02: f is somewhere positive (warrant: Tonelli's theorem). Lean: `exists_pos_measure_bounded_subset`.

- a01A11: g is analytic on \mathbb{C} \setminus K (warrant: Morera + Fubini).

### Hölder and Minkowski inequalities (12 both, 19 named)

both: `a00J02` `a01A09` `a01J01` `a02J01` `a93A02` `a93J04` `a94J04` `a96A03` `a96A04` `a97A02` `a99J09` `m93J05`
named: `a03J03` `a92J01` `a94A04` `a95A08` `a95J08` `a96A01` `a96A02` `a97A01` `a97J03` `a99J02` `b93J01` `b98A04` `bpm-1-1-2` `m02J05` `m02J06` `m93J02` `m93J06` `m94A04` `m95A02`

Lean: `MeasureTheory.MemLp.integrable_mul`, `MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ`, `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`, `ENNReal.lintegral_mul_le_Lp_mul_Lq`, `MeasureTheory.eLpNorm_add_le`

- m93J06: f is Holder-alpha in y (warrant: f is Holder-alpha in y). Lean: `apm_m93j06_not_holder_unique`.

- a95A08: \ell(C)^2 = (\int |f'(e^{i\theta})^2 d\theta)^2 \leq 2\pi \cdot \int |f'(e^{i\theta})|^2 d\theta (warrant: Cauchy-Schwarz inequality).

### Jensen inequality and convexity (4 both, 7 named)

both: `a96A01` `bpm-1-8-1` `m02J05` `t00A05`
named: `a02J02` `a95A08` `a99J01` `m03J05` `m93J05` `m98J04` `m99A01`

Lean: `ConvexOn`, `ConvexOn.map_integral_le`, `ConcaveOn.inf`, `ConcaveOn.add`, `ConcaveOn.smul`

- a95A08: \ell(C) \geq 2\pi \cdot \exp((1/2\pi)\int_{0}^{2}\pi \log|f'(e^{i\theta})| d\theta) (warrant: Jensen's inequality).

- a99J01: ∫E log|f| dμ ≤ log a. (warrant: Jensen's inequality).

### Chebyshev, Markov and Borel-Cantelli (0 both, 4 named)

named: `a01A01` `a03J01` `a92J02` `a99J05`

- a92J02: m(lim sup E_k) = 0 (warrant: Borel-Cantelli lemma).

- a93J03: For all sufficiently large n, x ∉ A_n. (warrant: Borel-Cantelli lemma).

### Egorov, Lusin and convergence in measure (2 both, 7 named)

both: `a92J02` `a95J05`
named: `a03J02` `a93A02` `a94A01` `a95A02` `a95J06` `a96J05` `a98J01`

Lean: `MeasureTheory.TendstoInMeasure`, `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`, `MeasureTheory.tendstoInMeasure_iff_dist`, `MeasureTheory.tendstoInMeasure_iff_norm`, `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm`

- a95J05: convergence in measure $\Longrightarrow \int|\operatorname{arctan} f_{n}| \to 0$ (warrant: convergence in measure is equivalent to convergence in the metric d(f,). Lean: `tendstoInMeasure_iff_integral_arctan`.

- a92J02: For each k, there exists N_k such that n > N_k implies m({|f_n - f| > 1/k}) < 2^(-k) (warrant: definition of convergence in measure). Lean: `convergesInMeasure.exists_subseq_ae_tendsto`.

### L^p spaces (21 both, 2 named)

both: `a00J03` `a01A09` `a02J01` `a02J02` `a03J03` `a92J01` `a93A02` `a93J04` `a94A01` `a94A03` `a95A03` `a95J08` `a96A03` `a96J05` `a97A02` `a97J03` `a99J09` `m93J05` `m93J07` `m94A04` `m95A04`
named: `a01A02` `a99J10`

Lean: `MeasureTheory.MemLp`, `MeasureTheory.eLpNorm`, `MeasureTheory.Lp`, `MeasureTheory.MemLp.coeFn_toLp`, `MeasureTheory.eLpNorm_one_eq_lintegral_enorm`

- a95J08: norm of h in Lp is less than or equal to norm of f in L1 times norm of g in Lp (warrant: definition of Lp norm).

- a93J04: ||f||p ≤ ||f||∞ (warrant: definition of Lp norm).

### Lebesgue differentiation and absolute continuity (11 both, 14 named)

both: `a00J02` `a93A04` `a93J01` `a94A02` `a94J02` `a95A02` `a95J06` `a97A03` `a97J04` `a98J02` `m99J06`
named: `a01J01` `a01J03` `a02J04` `a93A02` `a94A05` `a94J01` `a95A04` `a95J07` `a96A02` `a96J04` `a97A01` `a98A03` `a99J04` `m95A02`

Lean: `AbsolutelyContinuousOnInterval`, `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`, `AbsolutelyContinuousOnInterval.mono`, `AbsolutelyContinuousOnInterval.disjWithin`, `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv`

- a94A05: Show that f(C) has Lebesgue measure zero. (warrant: Vitali covering lemma). Lean: `measure_image_critical_set_eq_zero`.

- a93A04: If $f_n$ is Lipschitz and $V(f_n-f)\to 0$, then $f$ is absolutely continuous. (warrant: definition of absolute continuity). Lean: `lipschitz_implies_ac`.

### Radon-Nikodym and singular measures (3 both, 0 named)

both: `a01J03` `a02J04` `a99J04`

Lean: `MeasureTheory.Measure.MutuallySingular`, `MeasureTheory.Measure.rnDeriv`, `MeasureTheory.Measure.rnDeriv_lt_top`, `MeasureTheory.Measure.eq_rnDeriv`, `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`

- a99J04: For each pair i≠j write the Lebesgue decomposition of μi with respect to μj (warrant: For each pair i≠j write the Lebesgue decomposition of μi with respect).

### Measurable sets and outer measure (4 both, 16 named)

both: `a95A02` `a95J06` `a98A03` `t91J01`
named: `a01A02` `a01J02` `a02J04` `a03J01` `a03J02` `a94A01` `a94J02` `a95A01` `a96J04` `a97A04` `a97J01` `a98A04` `a98J01` `a99J05` `aunk01` `t94A03`

Lean: `cantorSet_subset_unitInterval`, `cantorSet`, `MeasureTheory.OuterMeasure`, `cantorSet_eq_union_halves`, `preCantorSet`

- a03J02: f(E) is null (warrant: countable union of null sets). Lean: `differentiable_image_null_of_null`.

- a95A01: Establish that $f$ is not Riemann integrable (warrant: A compact set with positive measure and empty interior (fat Cantor set). Lean: `inf_indicator_eq_zero`.

### Convolution and approximate identities (8 both, 13 named)

both: `a01A03` `a03J03` `a96J02` `a97J03` `a99J02` `m02J01` `m95J02` `m98J02`
named: `a02J01` `a94A03` `a94J04` `a95A03` `a95J08` `a96A04` `a98J03` `m02J05` `m02J06` `m95J05` `m98A04` `m98J05` `m99A06`

Lean: `MeasureTheory.convolution`, `MeasureTheory.convolution_eq_swap`, `ContDiffBump`, `ContDiffBump.nonneg_normed`, `ContDiffBump.integral_normed`

- a94J04: Py extends to a bounded linear operator Py:L2(R)→L2(R) with operator norm less than or equal to one. (warrant: The Poisson kernel is a probability measure and a convolution kernel). Lean: `poissonConv_L2_contraction`.

- a95A03: ||f*g||_2 <= ||f||_1 * ||g||_2 (warrant: Young's convolution inequality). Lean: `young_inequality_L1_L2`.

### Fourier transform (6 both, 7 named)

both: `a01A10` `a03J05` `a92J03` `m96J05` `m97A05` `m98J05`
named: `a01A03` `a01A09` `a02J03` `a02J05` `a03J03` `a96A04` `a98J03`

Lean: `Real.fourierChar`, `fourierIntegral_gaussian`, `Real.fourier_eq'`, `Real.fourierInv_eq'`, `Real.fourierChar_apply`

- a98J03: The Fourier transform of P_y(x) is e^(-2πy|ξ|). (warrant: The Fourier transform of P_y(x) is e^(-2πy|ξ|) by definition of P_y(x)).

- m98J05: Fourier transform of f' (warrant: Fourier transform definition).

### Fourier series (2 both, 7 named)

both: `a92J03` `a98A02`
named: `a95A08` `bpm-1-7-1` `m93A01` `m93J05` `m94J03` `m95A02` `m96A03`

Lean: `Real.fourierChar`, `Real.fourierChar_apply`, `Orthonormal.inner_products_summable`

- bpm-1-7-1: The Fourier series of f is ∑[n=1 to ∞] ((-1)^(n+1) * 2 * sin(nx)) / n. (warrant: Fourier series definition). Lean: `bpm_1_7_1`.

- m96A03: ∑|∫u_n(s)ds|^2 = t-a (warrant: Parseval's identity).

### Gaussian and Gamma integrals (6 both, 1 named)

both: `a01A04` `a01A10` `a94A03` `a96A04` `m02A04` `m98J05`
named: `a02J05`

Lean: `integral_gaussian`, `Real.Gamma_pos_of_pos`, `Real.Gamma_one_half_eq`, `Real.Gamma_add_one`, `Real.Gamma`

- m02A04: Evaluate the Gaussian integral (warrant: Evaluating the Gaussian integral).

### Differentiation under the integral sign (8 both, 1 named)

both: `a00J05` `a01A09` `a01A11` `a99J03` `a99J09` `m98J02` `m98J04` `m98J05`
named: `a96A04`

Lean: `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`

## Functional

### Baire category (4 both, 1 named)

both: `m95J07` `t91A06` `t92J03` `t94A03`
named: `m01J01`

Lean: `BaireSpace.of_completelyPseudoMetrizable`, `dense_iInter_of_isOpen_nat`, `nonempty_interior_of_iUnion_of_closed`

- m95J07: The set of functions in C[-1,1] that are not differentiable at 0 is second category (warrant: Baire property).

- t94A03: The real line is not a countable union of nowhere-dense sets (warrant: Baire Category Theorem).

### Uniform boundedness (3 both, 1 named)

both: `m01J04` `m02J03` `m99A05`
named: `m95A01`

Lean: `banach_steinhaus`

- m02J03: x_n is bounded (warrant: Uniform Boundedness Principle).

- m95A01: The B_n are pointwise bounded, so by the uniform boundedness principle (Banach-Steinhaus), sup_n ||B_n|| < infinity (warrant: uniform boundedness principle (Banach-Steinhaus)).

### Open mapping and closed graph (5 both, 7 named)

both: `m01J01` `m95J07` `m96A04` `m98A01` `m98J01`
named: `a94J03` `m00A01` `m03J01` `m03J04` `m94J06` `m95A01` `m98A05`

Lean: `LinearMap.continuous_of_isClosed_graph`, `LinearMap.continuous_of_seq_closed_graph`

- m95J07: The graph of T is closed (warrant: definition of closed graph).

- a94J03: f cannot be constant on any nontrivial interval (warrant: open mapping theorem).

### Hahn-Banach and dual spaces (8 both, 1 named)

both: `m02A01` `m93J07` `m94A03` `m95A02` `m96A06` `m99A05` `m99J05` `m99J06`
named: `a02J03`

Lean: `StrongDual`, `exists_dual_vector`

- m96A06: F'(u) is a bounded linear functional on H (warrant: F'(u) is a bounded linear functional on H).

- m93J07: If $Y \ne X$, then there exists $f\in X^{\ast{}}$ with $\|f\|=1$ and $f|_Y = 0$. (warrant: definition of Hahn-Banach theorem).

### Riesz representation and orthogonal projection (10 both, 3 named)

both: `a01A05` `m00A01` `m00A03` `m01J02` `m01J03` `m03J01` `m96A03` `m96J01` `m98J03` `t95A04`
named: `a02J02` `m00A04` `m96A01`

Lean: `Submodule.starProjection`, `Submodule.orthogonal`, `Submodule.starProjection_eq_self_iff`, `Submodule.range_starProjection`, `Submodule.HasOrthogonalProjection`

- m98J03: orthogonal complement V_perp (warrant: Let $P : H \to H$ be the orthogonal projection onto the closed subspac). Lean: `apm_m98J03_commute_preserves`.

- m96A01: Riesz's theorem forces finite dimension (warrant: Riesz's theorem).

### Orthonormal bases in Hilbert space (8 both, 4 named)

both: `a01A05` `a98A02` `m02J02` `m95A02` `m95J01` `m96A03` `m96J04` `m99J04`
named: `m01J03` `m93A03` `m94J03` `m99A03`

Lean: `HilbertBasis`, `InnerProductSpace.gramSchmidt`, `InnerProductSpace.gramSchmidtNormed`, `Orthonormal`, `HilbertBasis.repr`

- m95A02: e_n are complete (warrant: Definition of complete orthonormal basis). Lean: `m95A02_sq_norm_basisFunction_sub`.

- m95J01: The orthonormal basis phi_m (warrant: The orthonormal basis phi_m is defined as the Gram-Schmidt process app). Lean: `apm_m95J01_finrank_of_equiv`.

### Compact and self-adjoint operators (10 both, 3 named)

both: `m00A03` `m01J03` `m93A01` `m94J03` `m96A01` `m96J04` `m97A01` `m98J03` `m99A03` `m99J04`
named: `m02J02` `m03J05` `m93A04`

Lean: `IsCompactOperator`, `IsCompactOperator.clm_comp`, `IsCompactOperator.comp_clm`, `IsCompactOperator.image_closedBall_subset_compact`, `IsSelfAdjoint`

- m02J02: The eigenfunctions e_n are a complete orthogonal system in L^2(0,1) (warrant: eigenfunctions of a self-adjoint operator with compact resolvent). Lean: `apm_m02j02_sine_orthogonal`.

- m97A01: A^{\ast{}}A has a unique positive square root (warrant: spectral theorem).

### Weak convergence (2 both, 8 named)

both: `m02A01` `m99J06`
named: `a02J02` `a93A03` `a96A03` `m01J04` `m02J03` `m93A03` `m95A02` `m99A05`

Lean: `toWeakSpaceCLM`

- m95A02: Weak convergence implies uniform convergence (warrant: Definition of weak convergence). Lean: `m95A02_bounded_of_weak_convergence`.

- a96A03: lim_n→∞ ∫f_n(x)g(x)dx = ∫f(x)g(x)dx for all g in L^2(R) (warrant: Weak convergence).

### Arzelà-Ascoli (2 both, 3 named)

both: `m02J06` `m96J04`
named: `bpm-1-6-2` `m93A04` `m95A02`

Lean: `Equicontinuous`, `BoundedContinuousFunction.arzela_ascoli`, `EquicontinuousAt`, `LipschitzOnWith.uniformEquicontinuousOn`, `UniformEquicontinuousOn.equicontinuousOn`

- m02J06: K is compact in L^1(R) (warrant: Arzel\`{a}--Ascoli theorem). Lean: `apm_m02J06_bridge_2`.

- m96J04: V is compact (warrant: Arzel\`{a}--Ascoli theorem). Lean: `apm_m96j04_volterra_compact`.

### Stone-Weierstrass and density (1 both, 4 named)

both: `a94A04`
named: `a92J03` `a96A05` `m02J02` `m93J07`

Lean: `exists_polynomial_near_continuousMap`

- a97J03: lim epsilon to 0 delta(epsilon) = 0 (warrant: C_c(R) is dense in L^p and L^q).

- t91A06: G is dense in X (warrant: G is dense in X).

### Contraction mapping (10 both, 2 named)

both: `m01J05` `m02A06` `m93A02` `m94A05` `m94J05` `m95J04` `m96A02` `m96J06` `m97A03` `m99A06`
named: `m00A05` `m03J02`

Lean: `ContractingWith`, `ContractingWith.fixedPoint`, `ContractingWith.fixedPoint_isFixedPt`, `ContractingWith.fixedPoint_unique`, `ContractingWith.exists_fixedPoint'`

- m02A06: Unique solution of the BVP (warrant: contraction mapping principle). Lean: `apm_m02a06_solutionFunctionSpace_apply`.

- m94A05: By the Banach fixed-point theorem, T has a unique fixed point u ∈ Br (warrant: Banach fixed-point theorem). Lean: `apm_m94A05_bridge_2`.

## ODE and PDE

### ODE existence and uniqueness (5 both, 1 named)

both: `m00A05` `m03J02` `m93J06` `m96A02` `m99J01`
named: `m96J02`

Lean: `IsPicardLindelof`, `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`, `IsPicardLindelof.of_time_independent`, `ODE_solution_unique`, `ODE_solution_unique_univ`

- m03J02: the existence and uniqueness of a solution to the IVP for each u0∈ℝ (warrant: existence and uniqueness of a solution to the IVP for each u0∈ℝ). Lean: `m03J02_uniform_local_solution_at`.

### Linear ODE and matrix exponential (1 both, 3 named)

both: `m95J03`
named: `m93J04` `m98A05` `m99J02`

Lean: `NormedSpace.exp_series_hasSum_exp'`, `NormedSpace.exp`

### Boundary value and Sturm-Liouville problems (0 both, 15 named)

named: `m00A04` `m01J06` `m02A06` `m02J02` `m03J02` `m03J05` `m93J04` `m94J05` `m95A03` `m95A04` `m95J04` `m96A05` `m96A06` `m98J05` `m99J02`

- m02J02: The eigenfunctions e_n are a complete orthogonal system in L^2(0,1) (warrant: eigenfunctions of a self-adjoint operator with compact resolvent). Lean: `apm_m02j02_sine_orthogonal`.

- m96A06: F'(u) = 0 is equivalent to the Sturm-Liouville boundary value problem with Neumann conditions (warrant: F'(u) = 0 is equivalent to the Sturm-Liouville boundary value problem). Lean: `apm_m96A06_bridge_2`.

### Heat, wave and Laplace equations (0 both, 1 named)

named: `a96A04`

- a96A04: u(x,t) is the solution to the heat equation ∂tu = Δu with initial data u(⋅,0) = f (warrant: u(x,t) is the solution to the heat equation ∂tu = Δu with initial data).

### Energy and variational methods (1 both, 16 named)

both: `m96A06`
named: `m00A04` `m01J06` `m02A02` `m02A05` `m02J04` `m03J01` `m03J05` `m93J05` `m93J06` `m95A03` `m95A05` `m97A06` `m98A06` `m98J04` `m99A01` `m99J05`

Lean: `IsCoercive.continuousLinearEquivOfBilin`, `IsCoercive`, `IsCoercive.continuousLinearEquivOfBilin_apply`

- m02J04: The Beltrami identity when F=F(y,y') (warrant: The Euler-Lagrange equation is defined as F_y - d/dx F_y' = 0). Lean: `apm_m02J04_stationary_eulerLagrange`.

- m03J01: There is a unique weak solution to the boundary-value problem (warrant: unique weak solution). Lean: `apm_m03J01_weakSolution_zero_iff`.

### Sobolev and Poincaré inequalities (0 both, 22 named)

named: `bpm-1-1-2` `m00A04` `m01J04` `m02A02` `m02J02` `m03J01` `m03J05` `m93A01` `m94A03` `m95A02` `m95A03` `m95A04` `m96A06` `m98A05` `m98A06` `m99A02` `m99J06` `t00J02` `t01A06` `t02A06` `t91A05` `t97J08`

- m02J02: The eigenfunctions e_n are orthogonal in the H^1_0 inner product (warrant: orthogonality in the H^1_0 inner product). Lean: `apm_m02j02_inner_hermite_eq_zero_of_inner_normalized_eq_zero`.

- m94A03: log|x| is in H^1(Omega) if and only if n >= 3 (warrant: H^1(Omega) = {u in L^2(Omega): nabla u in L^2(Omega)}). Lean: `apm_m94a03_norm_logNormGradient`.

### Laplace transform (0 both, 1 named)

named: `a01A09`

## Numerics

### Numerical integration and interpolation (0 both, 2 named)

named: `a01A02` `a02J01`

### Finite elements (0 both, 3 named)

named: `a96A02` `m03J01` `m99J06`

### Iterative methods and root finding (0 both, 3 named)

named: `m01J05` `m02A05` `m97A06`

- m97A06: The Jacobi operator is positive (warrant: Jacobi operator).

### Matrix norms and conditioning (11 both, 2 named)

both: `a94J04` `a98J03` `m01J03` `m93A01` `m93A04` `m94J02` `m94J03` `m96A05` `m97A04` `m98A03` `m99A03`
named: `m94J06` `m98A02`

Lean: `ContinuousLinearMap.opNorm_le_bound`, `det_ne_zero_of_sum_row_lt_diag`, `ContinuousLinearMap.opNorm_comp_le`, `ContinuousLinearMap.opNorm_subsingleton`, `IsStarNormal.spectralRadius_eq_nnnorm`

- a98J03: The operator norm of T_y is less than or equal to 1. (warrant: The operator norm of T_y is less than or equal to 1 by definition of T).

- m94J02: σ(T) = {0} ∪ {2^(-n) : n = 0, 1, 2, ...} (warrant: spectral radius).

### Difference schemes and stability (0 both, 0 named)


## Calculus

### Mean value theorem and Taylor expansion (9 both, 13 named)

both: `a98A03` `m00A05` `m00A06` `m03J02` `m93J01` `m94A01` `m98A03` `m98A04` `m99J01`
named: `a00J06` `a01J04` `a03J06` `a95J04` `a96A06` `a96J09` `a97A06` `a97J05` `aunk04` `bpm-1-4-1` `bpm-1-6-2` `m96J02` `m99J03`

Lean: `exists_hasDerivAt_eq_slope`, `exists_deriv_eq_slope`, `Convex.norm_image_sub_le_of_norm_deriv_le`, `taylorWithinEval`, `taylorWithinEval_succ`

- a98A03: The Mean Value Theorem applies to f on each subinterval [x_{i-1},x_{i}] (warrant: Mean Value Theorem). Lean: `apm_a98a03_riemann_ftc`.

- a03J06: the Taylor series of f at 0 (warrant: Taylor series of an entire function).

### Riemann integration and the fundamental theorem (11 both, 7 named)

both: `a01A03` `a02J05` `bpm-1-1-2` `bpm-1-7-1` `m01J04` `m02J01` `m02J02` `m03J05` `m95A03` `m96J02` `m98J04`
named: `a00J02` `a95A01` `a97A03` `a98A03` `m02A02` `m03J03` `m95A04`

Lean: `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, `intervalIntegral.integral_eq_sub_of_hasDerivAt`, `intervalIntegral.integral_hasDerivAt_right`, `intervalIntegral.integral_deriv_eq_sub`, `intervalIntegral.integral_deriv_of_contDiffOn_uIcc`

- m96J02: y'(0) = β (warrant: Differentiating the kernel in (V) and using the product rule + FTC).

- a00J02: f(x) = ∫[0,x] f'(t) dt (warrant: fundamental theorem of calculus).

### Uniform convergence of series (13 both, 7 named)

both: `a00J06` `a01A07` `a92J04` `a93J07` `a94A08` `a95A06` `a95J04` `a96J01` `a96J10` `a97J08` `a98A01` `a98A07` `m94J02`
named: `a01J03` `a95A08` `a96J09` `a97J05` `aunk05` `m95A02` `t93A01`

Lean: `TendstoUniformlyOn`, `Metric.tendstoUniformlyOn_iff`, `FormalMultilinearSeries.radius`, `Summable.of_norm_bounded`, `continuousOn_tsum`

- m95A02: Every weakly convergent sequence in H converges in the maximum-norm topology (warrant: Definition of uniform convergence). Lean: `m95A02_sq_norm_basisFunction`.

- a98A01: α<0 (warrant: uniform convergence).

### Inverse and implicit function theorems (3 both, 5 named)

both: `t91A07` `t97J05` `t99J04`
named: `m93A02` `m93J03` `m96J06` `m97A02` `m98A05`

Lean: `OpenPartialHomeomorph.contDiffAt_symm`, `HasStrictFDerivAt.localInverse_apply_image`, `HasStrictFDerivAt.localInverse`, `ContDiffAt.to_localInverse`

- m93J03: By the implicit function theorem, there exist δ > 0, a neighborhood W ∋ (0,0) ∈ ℝ², and a unique C¹ map ε ↦ (a(ε), b(ε)) with (a(0),b(0)) = (0,0) such that, for (warrant: implicit function theorem). Lean: `apm_m93J03_solution_eq_affine_trig`.

- t91A07: g is a diffeomorphism onto its image (warrant: inverse function theorem).

### Multivariable change of variables (1 both, 5 named)

both: `a03J02`
named: `a00J03` `a95A03` `a98J04` `m93J03` `t97J05`

Lean: `MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`

- a95A03: int|f|^p = c_3 int_0^infty r^{-2p}(1+r^2)^{-p} * r^2 dr (warrant: spherical coordinates). Lean: `f_radial_integral`.

- a98J04: The Jacobian matrix Jf(x,y) equals [ux uy; vx vy] with a=ux=vy and b=vx=−uy. (warrant: definition of Jacobian matrix).

### Stokes and divergence theorems (2 both, 11 named)

both: `t03J06` `t96J08`
named: `m96J03` `t01A06` `t01J06` `t02A05` `t91A05` `t92J09` `t93A06` `t94A10` `t95J05` `t97A06` `t98A05`

Lean: `extDeriv_extDeriv`

- t94A10: Omega is not exact (warrant: Stokes' theorem). Lean: `apm_t94A10_bridge_solidAngle_not_exact`.

- t01A06: The exact term drops out. (warrant: Stokes' theorem).

## Geometry

### Differential forms and exterior calculus (10 both, 5 named)

both: `t00J04` `t01J06` `t03J06` `t91A08` `t93A06` `t94A10` `t96J08` `t97A06` `t98A05` `t99J06`
named: `t00A05` `t01A06` `t91A05` `t92J09` `t95J05`

Lean: `ContinuousAlternatingMap`, `extDeriv`, `ContinuousAlternatingMap.ext`, `extDeriv_apply`, `AlternatingMap`

- t98A05: Compute d\beta (warrant: definition of exterior derivative). Lean: `apm_t98A05_bridge_extDerivs`.

- t99J06: Compute the exterior derivative of alpha (warrant: exterior derivative of alpha). Lean: `extDeriv_alpha_aux_wedge`.

### de Rham cohomology (0 both, 2 named)

named: `t01A06` `t91A08`

- t01A06: There is no closed 1-form η on R³ and smooth γ : S¹ → T with ∫S¹ γ*η ≠ 0. (warrant: Poincaré lemma).

- t91A08: Integral of h^* beta over T^2 depends only on the de Rham cohomology class of beta (warrant: Integral of h^* beta over T^2 depends only on the de Rham cohomology c).

### Manifolds, charts and smooth structures (17 both, 4 named)

both: `t00J04` `t01A08` `t01J04` `t01J05` `t03J04` `t91A07` `t92J07` `t92J08` `t93A04` `t93A06` `t94A06` `t96A08` `t96J05` `t97A05` `t97A07` `t98A04` `t99J04`
named: `t01A07` `t94A05` `t94A08` `t96J07`

Lean: `ContMDiff`, `ContMDiffAt.mdifferentiableAt`, `ContMDiffOn`, `ContMDiffAt`, `ContMDiffOn.comp`

- t94A05: M is locally path connected. (warrant: charts land in open subsets of R^n). Lean: `connected_manifold_path_connected`.

- t96J05: X ∩ S_√c = ρ^(-1)(c) is a nonempty smooth manifold (warrant: definition of a nonempty smooth manifold).

### Submanifolds, immersions and embeddings (3 both, 15 named)

both: `t95A04` `t97A05` `t97A06`
named: `t00J02` `t01A07` `t01A08` `t01J04` `t02A07` `t92J07` `t94A06` `t94A08` `t96A07` `t96J05` `t97A07` `t97J02` `t97J05` `t97J07` `t98A04`

Lean: `Manifold.IsImmersion`, `Manifold.IsImmersionAtOfComplement.trans_F`, `Manifold.IsImmersionAtOfComplement`, `Manifold.IsImmersionAt.complement`, `Manifold.IsImmersionAt`

- t02A07: Z is a 2-dimensional submanifold (warrant: definition of submanifold).

- t94A08: \Sigma_{1} is a smooth submanifold of \mathbb{CP}^{2} (warrant: definition of smooth submanifold).

### Tangent bundle and vector fields (5 both, 8 named)

both: `t00J04` `t03J04` `t92J08` `t96A07` `t96A08`
named: `m93J06` `t01J05` `t91A01` `t93J06` `t94A09` `t94J08` `t95J06` `t98A06`

Lean: `mfderiv_comp`, `mfderiv_eq_fderiv`, `Filter.EventuallyEq.mfderiv_eq`, `mfderiv_extChartAt_self`, `mulInvariantVectorField`

- t98A06: f^(-1)(1,0) and f^(-1)(-1,0) are diffeomorphic (warrant: flows).

- t01J05: Nowhere-zero smooth vector field V on X. (warrant: Definition of a nowhere-zero vector field).

### Sard and regular values (5 both, 13 named)

both: `a03J02` `a94A05` `a95J07` `t94J05` `t95J04`
named: `t00J01` `t01A07` `t01A08` `t01J04` `t02A07` `t92J07` `t93A04` `t94A06` `t94A08` `t96A07` `t96J05` `t97A07` `t97J05`

Lean: `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`, `MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`

- t96J05: the set of critical values of ρ has Lebesgue measure zero in ℝ (warrant: Sard’s theorem). Lean: `apm_t96j05_exists_positive_nonempty_radialLevel`.

- t92J07: By Sard's theorem, for the smooth map f_i: M_i → ℝ^m the set of critical values has Lebesgue measure zero. (warrant: Sard's theorem). Lean: `apm_t92J07_criticalValues_fin_zero`.

### Lie groups and homogeneous spaces (0 both, 0 named)


### Projective spaces (13 both, 7 named)

both: `t00J03` `t00J07` `t01A01` `t01A07` `t92J05` `t94A08` `t95A04` `t96A06` `t96A07` `t96J06` `t96J07` `t98A03` `t99J05`
named: `t00A02` `t91A02` `t94J09` `t96A02` `t98A01` `t99A03` `tunk01`

Lean: `Projectivization`, `Projectivization.mk`, `Projectivization.mk_eq_mk_iff'`, `Projectivization.ind`, `Projectivization.rep`

- t01A01: RP^2 minus a point is homotopy equivalent to S^1. (warrant: RP^2 minus a point is homotopy equivalent to S^1). Lean: `apm_t01A01_punctured_homotopyEquiv_projectiveLine`.

- t95J05: there exists a 3-form eta on RP^3 with pi^*eta = i^*omega (warrant: descent of i^*omega to RP^3). Lean: `t95J05_existsUnique_projectiveThreeForm`.

### Tubular neighbourhoods and partitions of unity (1 both, 3 named)

both: `t00J04`
named: `t01J05` `t97A05` `t97A06`

Lean: `SmoothBumpFunction.contMDiff_smul`, `SmoothBumpFunction.eventuallyEq_one`

- t97A06: X has a tubular neighborhood T (warrant: tubular neighborhood).

- t98A06: there exists a vector field w on X (warrant: partition of unity).

## Algebraic topology

### Fundamental group (37 both, 12 named)

both: `t00A01` `t00J06` `t00J07` `t01A01` `t01A03` `t01A04` `t01J03` `t02A01` `t02A03` `t03J02` `t91A02` `t91A05` `t91J02` `t91J03` `t92J05` `t92J06` `t93A03` `t93J03` `t94A04` `t94J04` `t95A01` `t95J03` `t95J04` `t96A01` `t96J02` `t97A01` `t97A02` `t97A03` `t97J03` `t97J04` `t98A01` `t98A03` `t99A01` `t99A02` `t99A03` `t99J01` `t99J02`
named: `m01J01` `t00A02` `t00J08` `t01A02` `t01J02` `t01J06` `t02A04` `t03J01` `t03J03` `t91J05` `t95J02` `t97J02`

Lean: `Path.Homotopic`, `FundamentalGroup`, `Path.Homotopic.Quotient`, `FundamentalGroupoid.as`, `Path.Homotopic.Quotient.mk`

- t00J07: pi_1(X) = pi_1(RP^2)/<1> = Z/2 when f is homotopically trivial (warrant: Fundamental group definition). Lean: `apm_t00J07_rp2_bridge_projectivePlane_fundamentalGroup`.

- t02A04: The solid torus is homotopy equivalent to S^1. (warrant: homotopy equivalence implies same fundamental group). Lean: `apm_t02a04_continuous_solidInclusion`.

### Van Kampen (0 both, 13 named)

named: `t00A01` `t01A04` `t01J03` `t03J02` `t92J05` `t93A03` `t93J03` `t94A04` `t97A01` `t97J04` `t98A03` `t99A01` `t99J02`

- t99A01: The fundamental group of X is isomorphic to Z/2. (warrant: Van Kampen's theorem). Lean: `t99A01_piOne_Y`.

- t00A01: pi1(X) is the free product of pi1(M1) and pi1(M2) (warrant: van Kampen theorem). Lean: `apm_t00A01_pathConnected_of_hequiv`.

### Covering spaces (28 both, 2 named)

both: `t00A02` `t00J05` `t00J06` `t01A01` `t01A02` `t01A04` `t01J02` `t02A01` `t02A06` `t03J03` `t03J04` `t91A02` `t91J03` `t91J05` `t92J05` `t92J06` `t93J03` `t96J02` `t97A02` `t97A04` `t97J01` `t97J03` `t97J08` `t98A01` `t98A03` `t99A02` `t99A03` `t99J01`
named: `t95J05` `t97J06`

Lean: `IsCoveringMap`, `IsCoveringMap.continuous`, `IsCoveringMap.homeomorph_comp`, `IsCoveringMap.liftPath_zero`, `IsCoveringMap.liftPath`

- t03J03: every embedded cylinder lifts to Y (warrant: Lifting criterion). Lean: `apm_t03J03_bridge_3`.

- t91J05: Y is a closed surface. (warrant: A covering space of a 2-manifold is a 2-manifold (covers are local hom). Lean: `apm_t91J05_isFiniteCover_of_homeomorph`.

### Homology and exact sequences (30 both, 1 named)

both: `t00A01` `t00J02` `t00J07` `t01A03` `t01J03` `t02A03` `t02A04` `t02A06` `t03J01` `t03J02` `t93J04` `t94A07` `t95J02` `t95J04` `t96A02` `t96A03` `t96A06` `t96J07` `t97A01` `t97A03` `t97A04` `t97J04` `t97J06` `t98A02` `t98A04` `t98J01` `t98J03` `t99A01` `t99A03` `t99J02`
named: `t00A04`

Lean: `AlgebraicTopology.singularHomologyFunctor`, `CategoryTheory.ShortComplex.Exact.fIsKernel`, `HomologicalComplex.homologyπ`, `ChainComplex.alternatingConst`, `CategoryTheory.ShortComplex.ShortExact.comp_δ`

- t97A01: H_{2}(X) = \ker\varphi = 0 (warrant: Homology group of a surface). Lean: `ker_mulEquiv_comp`.

- t97A03: H_{0}(X)=ℤ (warrant: homology group definition). Lean: `apm_t97A03_bridge_invariants_of_model`.

### Cohomology ring and duality (0 both, 3 named)

named: `t00J02` `t02A06` `t95J04`

- t00J02: deg(f) scales the cup-product pairing (warrant: Naturality of cup product and definition of degree).

- t95J04: S^3 × S^3: by K"{u}nneth, H_i = Z, 0, 0, Z^2, 0, 0, Z for i = 0, …, 6 (warrant: Künneth formula).

### Euler characteristic and CW complexes (0 both, 35 named)

named: `a97J02` `t00A02` `t00A03` `t00J01` `t00J06` `t00J07` `t00J08` `t01J01` `t01J03` `t01J05` `t02A02` `t02A04` `t03J04` `t91A01` `t91A02` `t91J05` `t92J05` `t93J03` `t94J04` `t94J09` `t95J03` `t96A01` `t96A03` `t97A01` `t97A03` `t97J04` `t97J07` `t98A01` `t98A02` `t98J03` `t99A01` `t99J01` `t99J02` `t99J05` `tunk01`

- t03J03: chi(X) = 2 - 3 = -1 (warrant: Euler characteristic). Lean: `apm_t03J03_euler_Sigma2`.

- t99J01: The Euler characteristic of an n-sheeted connected cover is -2n (warrant: Definition of the Euler characteristic of a cover). Lean: `t99J01_connected_cover_fundamentalGroup`.

### Degree and fixed-point theorems (0 both, 28 named)

named: `a01J05` `a02J07` `a94A09` `a94J07` `a95J03` `a96A07` `t00A05` `t00J01` `t01A02` `t01J05` `t02A04` `t03J04` `t91A01` `t91J03` `t93J06` `t94A07` `t94A09` `t94J06` `t95J06` `t96A02` `t96A06` `t96J07` `t97A04` `t97J07` `t97J08` `t98A04` `t98J01` `t99J05`

- t96J07: global Lefschetz number is the sum of local Lefschetz numbers (warrant: global Lefschetz number is the sum of local Lefschetz numbers). Lean: `apm_t96j07_local_numbers`.

- t02A04: For every f, the Lefschetz number L(f) is 1. (warrant: definition of Lefschetz number). Lean: `apm_t02A04_bridge_1`.

### Homotopy and retractions (36 both, 7 named)

both: `t00A01` `t00J02` `t00J05` `t00J07` `t01A01` `t01A02` `t01A03` `t01A04` `t01J02` `t01J03` `t02A01` `t02A03` `t02A04` `t02A06` `t03J05` `t91A05` `t91A08` `t91J02` `t91J03` `t93A03` `t93J04` `t94A07` `t94J05` `t94J06` `t95J02` `t95J04` `t96A05` `t96A06` `t97A02` `t97A06` `t97J03` `t97J04` `t97J06` `t97J07` `t98J01` `t99J05`
named: `t00A04` `t01J01` `t03J01` `t03J02` `t94A04` `t94J03` `t97A03`

Lean: `ContinuousMap.Homotopic`, `ContinuousMap.Homotopy`, `ContinuousMap.Homotopy.apply_one`, `ContinuousMap.Homotopic.refl`, `ContinuousMap.Homotopic.comp`

- t02A04: The solid torus is homotopy equivalent to S^1. (warrant: deformation-retraction implies homotopy equivalence). Lean: `apm_t02a04_gluedDesc_solidInclusion`.

- t01A01: RP^2 minus a point is homotopy equivalent to S^1. (warrant: RP^2 minus a point is homotopy equivalent to S^1). Lean: `apm_t01A01_punctured_homotopyEquiv_projectiveLine`.

### Surfaces and classification (0 both, 53 named)

named: `m02A02` `t00A02` `t00A03` `t00J01` `t00J02` `t00J03` `t00J05` `t00J06` `t01A02` `t01A03` `t01A04` `t01A06` `t01A07` `t01J01` `t01J03` `t02A01` `t02A02` `t02A03` `t02A04` `t03J01` `t03J03` `t03J04` `t03J05` `t91A01` `t91A08` `t91J02` `t91J05` `t92J05` `t93A06` `t93J03` `t94A07` `t94J04` `t94J09` `t95A01` `t95J02` `t95J03` `t95J05` `t95J06` `t96A01` `t96J02` `t96J06` `t97A01` `t97A02` `t97A04` `t97A05` `t97J02` `t97J03` `t97J04` `t97J06` `t98A01` `t98A03` `t99J02` `tunk01`

- t97J02: M is either orientable Σg with χ = 2 - 2g, or non-orientable Nk with χ = 2 - k (warrant: By the classification of closed surfaces, M is either orientable Σg wi). Lean: `apm_t97J02_eulerCharacteristic_orientable`.

- t01J01: gamma_1 and gamma_2 are null-homologous and separating (warrant: orientable surface). Lean: `apm_t01J01_bridge_separates_of_nullHomologous`.

## General topology

### Compactness and Hausdorff arguments (2 both, 6 named)

both: `t92J02` `t96J01`
named: `t91A03` `t91A06` `t92J04` `t94J02` `t95A02` `t96A04`

Lean: `IsCompact.image`, `Continuous.homeoOfEquivCompactToT2`

- t96A04: C is not sequentially compact (warrant: sequentially compact implies every sequence has a convergent subsequen).

- t91A03: The subfamily {W_λ ∩ ({x} x Y)}_λ has a finite subcover W_λ₁,...,W_λₙₓ. (warrant: The subfamily {W_λ ∩ ({x} x Y)}_λ has a finite subcover W_λ₁,...,W_λₙₓ).

### Connectedness (44 both, 5 named)

both: `a00J04` `a01A08` `a93J07` `aunk02` `m93J02` `t00A01` `t00A02` `t00A03` `t00J02` `t00J06` `t01A01` `t01A03` `t01J02` `t02A04` `t03J03` `t03J04` `t91J02` `t91J05` `t92J01` `t92J05` `t92J06` `t93A03` `t93J02` `t93J03` `t94A04` `t94A08` `t94J01` `t94J04` `t94J05` `t95A01` `t95J03` `t95J04` `t95J06` `t96A01` `t96A02` `t96J05` `t97A02` `t97A05` `t97A07` `t97J07` `t98A03` `t98J03` `t99J01` `t99J02`
named: `t94A03` `t94A05` `t96J04` `t97J01` `t99J04`

Lean: `IsPathConnected`, `PathConnectedSpace.somePath`, `pathConnectedSpace_iff_univ`, `PathConnectedSpace.joined`, `IsPathConnected.joinedIn`

- t94A05: Any two points in M are path connected. (warrant: any two points are path connected). Lean: `isPathConnected_univ_of_connected`.

- t94J01: X is connected (warrant: definition of connectedness). Lean: `connected_iff_ladderConnected`.

### Quotient topology (14 both, 2 named)

both: `t00A01` `t00A02` `t00J03` `t00J07` `t02A02` `t92J05` `t93J03` `t94J09` `t94J11` `t95J02` `t96A06` `t97A01` `t98A02` `tunk03`
named: `t03J04` `t98J03`

Lean: `continuous_coinduced_rng`, `Topology.IsQuotientMap.continuous_iff`, `isQuotientMap_quotient_mk'`, `continuous_quotient_mk'`, `Topology.IsQuotientMap.comp`

- b98J04: phi is a ring homomorphism (warrant: product of quotient maps is a ring homomorphism). Lean: `apm_b98j04_of_small`.

- t03J04: V is nowhere zero on T^n (warrant: quotient map is a local diffeomorphism). Lean: `apm_t03J04_constantVectorField_ne_zero`.

### Product topology and Tychonoff (1 both, 1 named)

both: `t94A01`
named: `t93J01`

Lean: `nhds_pi`

- t93J01: X is compact. (warrant: Tychonoff's theorem).

- t94A01: T_rho is the metric topology and T_pi is the product topology (warrant: T_rho is the metric topology and T_pi is the product topology).

### Separation axioms, Urysohn and Tietze (2 both, 4 named)

both: `t94J03` `t96J01`
named: `t93A01` `t94J10` `t96A05` `tunk02`

Lean: `ContinuousMap.exists_restrict_eq`, `exists_continuous_zero_one_of_isClosed`

- t94J03: Every continuous g:A→ℝ extends to a continuous G:X→ℝ (warrant: scalar Tietze extension theorem).

- t93A01: There is a continuous function f_{n} : X → [0,1] with f_{n} ≡ 1 on C_{n} and f_{n} ≡ 0 on X \setminus U (warrant: Urysohn's lemma).

### Metric spaces and completion (9 both, 27 named)

both: `a93A01` `a96J05` `m02J06` `m93J02` `m94J02` `t93A02` `t94A02` `t95A03` `t96J03`
named: `a01J02` `a03J02` `a93A04` `a97A03` `bpm-1-6-2` `m01J05` `m02A02` `m02A06` `m03J02` `m03J05` `m93A02` `m93J06` `m94A05` `m95J04` `m96A02` `m96J02` `m96J06` `m97A02` `m97A03` `m98A02` `m99A04` `m99J01` `t91A04` `t91A06` `t92J03` `t94A01` `t94A03`

Lean: `cauchySeq_tendsto_of_complete`, `TotallyBounded`, `Metric.cauchySeq_iff`, `Metric.infDist`, `TotallyBounded.image`

- a03J02: If g is Lipschitz with constant L on a set S, and m(S) = 0, then m(g(S)) = 0 (warrant: Lipschitz maps send null sets to null sets). Lean: `polynomial_map_image_null`.

- m93J06: y0 mapsto y(t) is Lipschitz for small t (warrant: y0 mapsto y(t) is Lipschitz for small t). Lean: `apm_m93j06_exists_compact_state_lipschitz`.

### Ordinals, well-ordering and cardinality (6 both, 7 named)

both: `a00J04` `m93J07` `t00J01` `t91A02` `t92J07` `t96J04`
named: `a03J02` `a95A02` `a97A04` `b01J01` `b99A01` `t93A01` `t94A03`

Lean: `Cardinal`, `Cardinal.partialOrder`, `Cardinal.addLeftMono`, `Set.countable_range`, `Set.Countable.exists_surjective`

- a03J02: f(E) is null (warrant: countable union of null sets). Lean: `differentiable_image_null_of_null`.

- b99A01: a valuation domain has a unique maximal ideal (warrant: Zorn's lemma).

### Countability axioms (2 both, 2 named)

both: `m93J07` `t92J07`
named: `m02J02` `m99J01`

Lean: `TopologicalSpace.IsSeparable.span`, `TopologicalSpace.IsSeparable.closure`, `TopologicalSpace.IsSeparable.iUnion`, `HereditarilyLindelof.to_Lindelof`

- m02J02: Each H^1_0(Ω) possesses a countable orthonormal basis (warrant: separable Hilbert spaces possess a countable orthonormal basis).

## Groups

### Sylow theorems (13 both, 1 named)

both: `b01A02` `b01J01` `b01J03` `b03J01` `b90A03` `b93A01` `b93J01` `b94A01` `b96A02` `b97A01` `b98A01` `b98J01` `b99A02`
named: `b97J01`

Lean: `Sylow`, `Sylow.normal_of_subsingleton`, `Sylow.card_eq_multiplicity`, `Sylow.card_dvd_index`, `card_sylow_modEq_one`

- b90A03: |P| = p^n (warrant: definition of Sylow p-subgroup). Lean: `apm_b90a03_sylow_card`.

- b01J01: |Sp(K)| divides |Sp(G)| (warrant: Sylow's theorem). Lean: `apm_b01j01_smul_sylow_map`.

### Group actions and the class equation (6 both, 6 named)

both: `b00J03` `b01J03` `b97A01` `b97J01` `b98J01` `t92J06`
named: `b95J01` `b96A03` `b98J02` `b99A03` `t95J06` `t98A04`

Lean: `Subgroup.center`, `MulAction.orbit`, `MulAction.stabilizer`, `IsPGroup.card_center_eq_prime_pow`, `MulAction.index_stabilizer_of_transitive`

- b97A01: Sizes of conjugacy classes sum to $|S_{4}|$ (warrant: Sizes of conjugacy classes sum to |S_{4}|). Lean: `apm_b97A01_conjugacy_classification`.

- b00J03: Every finite p-group G≠{e} has Z(G)≠{e}. (warrant: Class equation).

### Simple and solvable groups (7 both, 2 named)

both: `b00J03` `b01J01` `b96A01` `b96J03` `b97A01` `b97J01` `b98A02`
named: `b98A04` `m96A03`

Lean: `commutator`, `Subgroup.Normal.quotient_commutative_iff_commutator_le`, `IsSolvable`, `solvable_of_ker_le_range`, `Group.IsNilpotent`

- b96J03: A nilpotent group is solvable (warrant: A nilpotent group has a central series, and a solvable group has a sub). Lean: `apm_b96j03_nilpotent_implies_solvable`.

### Direct and semidirect products (7 both, 2 named)

both: `b01A02` `b01A04` `b93A01` `b93J01` `b94A01` `b98J01` `t96J02`
named: `b03J01` `b99A02`

Lean: `Subgroup.IsComplement'`, `SemidirectProduct`, `Subgroup.IsComplement'.disjoint`, `SemidirectProduct.mulEquivSubgroup`, `Subgroup.IsComplement'.card_mul`

- b94A01: G is isomorphic to some semi-direct product of P by Q (warrant: Recognition theorem (internal semidirect product)). Lean: `apm_b94a01_complement`.

- b03J01: G≅P×Q≅Cp×Cq≅Cpq=Cp(p+2), the last step because gcd(p,q)=1 makes Cp×Cq cyclic (warrant: direct product of groups).

### Symmetric and alternating groups (11 both, 30 named)

both: `b00J01` `b93A01` `b93J01` `b96J01` `b96J03` `b97A01` `b97A03` `b97J01` `b98J01` `t00A02` `t96A01`
named: `a01J03` `a92J01` `a93J03` `a96J09` `a96J10` `a97A01` `a97J01` `a97J02` `a98J01` `aunk04` `b93J04` `b94J03` `b95J01` `b98A01` `bpm-1-3-1` `bpm-1-3-2` `bpm-1-7-1` `m00A02` `m03J03` `m93A01` `m95A01` `m95J07` `m96A05` `m98A02` `m99A04` `t91J04` `t92J06` `t93A02` `t97J02` `t98A03`

Lean: `Equiv.Perm.sign`, `alternatingGroup`, `Equiv.Perm.support`, `Equiv.Perm.sign_mul`, `alternatingGroup.normal`

- b93J04: The Klein four subgroup $G$ of $S_4$. (warrant: Klein four subgroup G of S_4). Lean: `apm_b93J04_mulEquiv_kleinFour_of_card_exponent`.

- b96J03: A solvable group is not necessarily nilpotent (warrant: S_3 is a counterexample). Lean: `apm_b96j03_solvable_not_nilpotent_exists`.

### Finite and cyclic abelian groups (27 both, 4 named)

both: `b01A02` `b01A04` `b01J01` `b01J03` `b03J01` `b93A01` `b93J01` `b94A01` `b94J01` `b94J03` `b95J01` `b95J02` `b96A01` `b96A02` `b96J04` `b98A01` `b98J01` `t00J06` `t00J08` `t01A04` `t94J04` `t95A01` `t95J03` `t96A01` `t96J02` `t98A01` `t99J01`
named: `b93A03` `b97J02` `t00A02` `t97A03`

Lean: `Subgroup.index`, `Subgroup.index_eq_card`, `Subgroup.index_ker`, `Subgroup.card_subgroup_dvd_card`, `isCyclic_of_prime_card`

- b01A02: From these facts deduce that any group of order 255 is cyclic (warrant: definition of cyclic group). Lean: `apm_b01A02_isCyclic_of_card_255`.

- b97J02: If Spec(R) is finite, then phi is bijective (warrant: Chinese Remainder Theorem). Lean: `apm_b97j02_toPiQuotient_bijective_of_finite`.

### Free groups and presentations (10 both, 2 named)

both: `b96J03` `t00J08` `t01A03` `t03J02` `t93A03` `t96A01` `t97A03` `t97J04` `t99J01` `t99J02`
named: `t00A01` `t01A04`

Lean: `FreeGroup`, `FreeGroup.of`, `FreeGroup.lift_apply_of`, `FreeGroup.lift`, `FreeGroup.map_injective`

- t01A04: π1(X, x) = <a, b, c | aba-1b-1 = 1> ≅ ℤ2 * ℤ (warrant: definition of free product).

- t97A03: π_{1}(Y)=F_{3} (warrant: free group definition).

## Fields

### Fundamental theorem of Galois theory (17 both, 0 named)

both: `b00J01` `b01A04` `b01J03` `b90A03` `b93A04` `b93J04` `b94J03` `b95J04` `b96A02` `b96J04` `b97A02` `b97A03` `b97J03` `b98A02` `b98J02` `b98J03` `b99A03`

Lean: `AlgEquiv.aut`, `IntermediateField.fixedField`, `IsGalois`, `IsGalois.card_aut_eq_finrank`, `IsGalois.to_normal`

- b98A02: Gal(A/F)≅G/G′ abelian (warrant: Fundamental Theorem of Galois Theory). Lean: `apm_b98a02_le_of_isMaximalAbelian`.

- b94J03: |Gal(K/\mathbb{Q})| = 6 (warrant: order of Galois group). Lean: `apm_b94J03_bridge_rational_conclusion`.

### Splitting fields and normal extensions (14 both, 1 named)

both: `b00J01` `b01A01` `b01J03` `b03J04` `b93J03` `b93J04` `b94J03` `b95J04` `b96A02` `b96J04` `b97A03` `b97J03` `b98A02` `b98J02`
named: `b93A04`

Lean: `Polynomial.IsSplittingField`, `Polynomial.Splits`, `Polynomial.IsSplittingField.finiteDimensional`, `Polynomial.IsSplittingField.splits`, `IsAlgClosed.splits`

- b94J03: K = \mathbb{F}_{7}(\alpha) = \mathbb{F}_{7^{3}} (warrant: splitting field of a separable polynomial). Lean: `apm_b94J03_bridge_complex_model`.

- b96A02: The splitting field of f inside L is exactly F({gα : g∈G}) = L^core_G(H). (warrant: definition of splitting field of f). Lean: `apm_b96a02_normalClosure_adjoin_simple`.

### Minimal polynomials and degree of extensions (9 both, 2 named)

both: `b00J01` `b01J03` `b93J04` `b95J02` `b96A02` `b97A02` `b97J03` `b98J03` `b99A03`
named: `b94J02` `b94J03`

Lean: `minpoly`, `IntermediateField.adjoin`, `IntermediateField.adjoin_le_iff`, `IntermediateField.adjoin.finrank`, `Module.finrank_mul_finrank`

- b94J03: [\mathbb{Q}(\beta):\mathbb{Q}] = 3 (warrant: minimal polynomial x^2+x+1).

- b94J02: A^{m}=0 \Rightarrow \operatorname{tr}(A)=0 (warrant: definition of minimal polynomial and same irreducible factors).

### Finite fields (3 both, 7 named)

both: `b94J03` `b96J04` `b97A02`
named: `a94J07` `b00J01` `b01A01` `b01J02` `b97A04` `b97J02` `b98J03`

Lean: `FiniteField.pow_finrank_eq_natCard`, `FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic`, `FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate`, `FiniteField.frobeniusAlgEquivOfAlgebraic`, `FiniteField.pow_card_sub_one_eq_one`

- b01A01: f(x) = x^p - a splits in k[x] or is irreducible (warrant: Frobenius homomorphism).

- b96J04: Gal(L/\mathbb{F}_{41}) \cong \mathbb{Z}/2. (warrant: The Galois group of a finite field is cyclic.).

### Irreducibility criteria (8 both, 4 named)

both: `b00J01` `b01A01` `b03J04` `b93J04` `b94J03` `b95J04` `b97A03` `b97J03`
named: `b00J02` `b01J02` `b94J02` `b98J03`

Lean: `X_pow_sub_C_irreducible_iff_of_prime`, `Polynomial.IsEisensteinAt`, `Polynomial.IsEisensteinAt.irreducible`, `Polynomial.Monic.irreducible_of_irreducible_map`, `X_pow_sub_C_irreducible_of_prime`

- b00J01: f(x) = x^3 - 7 is irreducible over \mathbb{F}_{13} (warrant: f(x) = x^3 - 7 is irreducible over \mathbb{F}_{13}). Lean: `apm_b00j01_irreducible_rat`.

- b93J04: The polynomial $x^4-10x^2+1$ is irreducible over $\mathbb{Q}$. (warrant: Polynomial x^4-10x^2+1 is irreducible over Q). Lean: `apm_b93j04_poly_irreducible`.

### Cyclotomic extensions and roots of unity (6 both, 2 named)

both: `b00J01` `b01A04` `b94J03` `b95J04` `b96J04` `b97A03`
named: `b03J04` `b96A03`

Lean: `IsPrimitiveRoot`, `IsPrimitiveRoot.pow_eq_one`, `IsCyclotomicExtension.numberField`, `IsCyclotomicExtension.finrank`, `IsCyclotomicExtension.Rat.galEquivZMod`

- b94J03: \omega \in \mathbb{F}_{7} (warrant: primitive cube root of unity).

- b95J04: x^{p}-1 = \prod_{i=1}^{p}(x-z^{i}). (warrant: primitive p-th root of unity).

### Separability (2 both, 1 named)

both: `b01A01` `b94J03`
named: `b93A04`

Lean: `Polynomial.Separable`, `PerfectField.separable_of_irreducible`, `Polynomial.separable_X_pow_sub_C`

- b94J03: K = \mathbb{F}_{7}(\alpha) = \mathbb{F}_{7^{3}} (warrant: splitting field of a separable polynomial). Lean: `apm_b94J03_bridge_complex_model`.

## Rings

### Euclidean domains, PIDs and UFDs (6 both, 4 named)

both: `b00J04` `b01A03` `b01J02` `b03J02` `b03J03` `b93J02`
named: `b90A02` `b95J02` `b96A03` `b99A01`

Lean: `IsPrincipalIdealRing`, `IsPrincipalIdealRing.principal`, `UniqueFactorizationMonoid.irreducible_iff_prime`, `UniqueFactorizationMonoid`, `IsPrincipalIdealRing.of_surjective`

- b00J04: S is a PID (warrant: PID). Lean: `apm_b00J04_first_conjunct`.

- b95J02: Ann_R(M) = (d_k) (warrant: PID structure theorem, invariant-factor form).

### Prime and maximal ideals (7 both, 0 named)

both: `b01J02` `b90A04` `b93A02` `b97J02` `b98A03` `b98J02` `b99A01`

Lean: `Ideal.IsPrime`, `Ideal.IsMaximal`, `Ideal.IsPrime.mem_or_mem`, `Ideal.jacobson_eq_self_of_isMaximal`, `Ideal.jacobson`

### Noetherian and Artinian rings (4 both, 0 named)

both: `b93A02` `b93J02` `b98A04` `b98J04`

Lean: `IsNoetherian`, `IsArtinianRing`, `IsArtinian`, `IsArtinianRing.setOf_isPrime_finite`, `IsNoetherianRing`

### Localisation and integral closure (6 both, 2 named)

both: `b00J04` `b03J03` `b93J02` `b94J04` `b98J02` `b99A01`
named: `b90A02` `b95J04`

Lean: `IsIntegrallyClosed`, `IsIntegral`, `OreLocalization.oreSetComm`, `IsIntegralClosure.of_isIntegrallyClosed`, `IsLocalization`

- b00J04: S = D^(-1)R (warrant: localization).

### Gauss lemma and polynomial rings (0 both, 0 named)


### Semisimple rings and Wedderburn (5 both, 0 named)

both: `b97A04` `b97J04` `b98A04` `b98J04` `b99A04`

Lean: `IsSimpleModule`, `IsSimpleModule.nontrivial`, `IsSimpleRing`, `IsSimpleRing.matrix`, `IsSimpleModule.congr`

- b97A04: dim_C V < ∞ (warrant: definition of faithful simple module). Lean: `apm_b97a04_module_finite`.

- b97J04: S is semisimple (warrant: S is semisimple because it is diagonalizable). Lean: `apm_b97j04_multiplicative`.

### Tensor products (4 both, 0 named)

both: `b90A02` `b93A03` `b94A02` `b95J03`

Lean: `TensorProduct.map`, `TensorProduct`, `TensorProduct.tmul`, `TensorProduct.tmul_zero`, `TensorProduct.induction_on`

- b94A02: bR \otimes_R R/I \cong R/I (warrant: universal property of tensor product). Lean: `apm_b94A02_exists_surjective_tensorLift`.

### Modules, exactness and flatness (9 both, 11 named)

both: `b01A03` `b90A02` `b94J04` `b96A04` `b98A04` `t00A01` `t00J07` `t96A02` `t99A03`
named: `b93A03` `b95J02` `b96A01` `b96A03` `t01A01` `t02A04` `t03J02` `t95J02` `t96A03` `t97A01` `t97A02`

Lean: `Function.Exact`, `Module.Free`, `Module.Flat`, `Module.Free.ChooseBasisIndex`, `Module.Free.chooseBasis`

- b90A02: Projective modules are flat (warrant: Part (a): free modules are flat).

- b96A01: The e_{i} are Q-linearly independent in V (warrant: A finitely generated torsion-free abelian group is free of finite rank).

## Linear algebra

### Modules over a PID and canonical forms (2 both, 3 named)

both: `b93J03` `b97J04`
named: `b95J02` `b96J02` `m95J03`

Lean: `Module.End.iSup_maxGenEigenspace_eq_top`, `Module.End.isNilpotent.restrict`, `Module.End.exists_isNilpotent_isSemisimple`

- b96J02: The pair (a,b) is an isomorphism invariant (warrant: The pair (a,b) is an isomorphism invariant (uniqueness of Jordan form,).

### Characteristic and minimal polynomials of matrices (9 both, 19 named)

both: `b01J04` `b95J02` `b95J04` `b97J04` `m00A03` `m01J03` `m94A02` `m96A01` `m99J04`
named: `b93J03` `b94J02` `m01J06` `m02A05` `m94J02` `m94J03` `m95J01` `m95J03` `m96J04` `m97A06` `m98A05` `m98A06` `m98J03` `m99A03` `t91A07` `t94A07` `t96J07` `t97J07` `t99J05`

Lean: `Module.End.eigenspace`, `Module.End.HasEigenvalue.exists_hasEigenvector`, `Matrix.charpoly`, `LinearMap.charpoly_monic`, `LinearMap.charpoly`

- t99J05: The fixed points of f are precisely the coordinate lines (warrant: since the three eigenvalues are distinct, only one coordinate can be n).

- b01J04: A^{-1} is a polynomial in A (warrant: Cayley-Hamilton theorem).

### Diagonalisation and bilinear forms (2 both, 10 named)

both: `m94A02` `m99J04`
named: `b01J04` `b93J03` `b97J04` `m02A05` `m03J04` `m94J03` `m95J03` `m96A06` `m97A06` `t94A08`

Lean: `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`, `LinearMap.IsSymmetric`, `Matrix.IsHermitian.eq_1`, `Matrix.IsHermitian.eigenvalues₀`, `Matrix.IsHermitian.eigenvectorUnitary`

- b97J04: S is semisimple (warrant: S is semisimple because it is diagonalizable). Lean: `apm_b97j04_multiplicative`.

- m95J03: The solution to x' = B(0)x is x(t) = e^(tB(0))v (warrant: B(rho) is diagonalizable for generic rho). Lean: `apm_m95J03_bridge_1`.

### Determinants and rank (6 both, 7 named)

both: `b00J02` `b95J03` `b97A01` `t93A06` `t98J06` `t99J05`
named: `t01J03` `t91A08` `t94J08` `t96J07` `t97A04` `t97J06` `t97J07`

Lean: `Matrix.det`, `LinearMap.det`, `Matrix.det_one`, `LinearMap.finrank_range_add_finrank_ker`, `Matrix.detRowAlternating`

- t96J07: compute local Lefschetz numbers for each fixed point (warrant: compute each (I-df is diagonal, so the determinant is the product of 1).

- b95J03: dim_F ker phi = n^2 - n (warrant: rank-nullity applied to phi).

### Representations and characters (0 both, 0 named)

