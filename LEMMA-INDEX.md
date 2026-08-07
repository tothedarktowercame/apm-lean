# Helper-lemma index (generated — do not hand-edit)

1095 lemmas already proved in this repo, outside the problems'
own statements. GREP THIS BEFORE RE-DERIVING ANYTHING.

`LIB:` rows are importable today (`import ConstructionTargets.X`).
The rest live inside one problem file: read the proof there and reuse the
argument, or ask for the lemma to be promoted into ConstructionTargets.

| lemma | where | signature |
|---|---|---|
| `A_nonneg` | a01J06 | `(data : ProblemData) : 0 ≤ data.A :=` |
| `B_nonneg` | a01J06 | `(data : ProblemData) : 0 ≤ data.B :=` |
| `G_zero` | a94A06 | `: G 0 = -(Real.sqrt 3 * π) / 72 := by` |
| `IsPolynomialMap.differentiable` | a03J02 | `{n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)}` |
| `L1_disk_convergence_analytic_upgrade` | a01A07 | `{f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}` |
| `MvPolynomial.eval_differentiable` | a03J02 | `{n : ℕ} (p : MvPolynomial (Fin n) ℝ) :` |
| `SpikeFunctionSpec.at_inv_nat` | a96A02 | `{f : ℝ → ℝ}` |
| `SpikeFunctionSpec.at_midpoint` | a96A02 | `{f : ℝ → ℝ}` |
| `a96A08` | a96A08 | `: ∫ x, a96A08_f x ∂volume = -(2 * Real.pi) := by` |
| `a96A08_integrable` | a96A08 | `: Integrable a96A08_f volume := by` |
| `a96J02` | a96J02 | `(A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)` |
| `a_def` | a96J01 | `(n : ℕ) : a n = 1 - (2 : ℝ)⁻¹ ^ n := rfl` |
| `a_le_mid` | a96J01 | `(n : ℕ) : a n ≤ mid n := by` |
| `a_le_one` | a96J01 | `(n : ℕ) : a n ≤ 1 := by` |
| `a_lt_b` | a96J01 | `(n : ℕ) : a n < b n := by` |
| `a_mono` | a96J01 | `(n : ℕ) : a n ≤ a (n + 1) := by` |
| `a_monotone` | a96J01 | `{j k : ℕ} (hjk : j ≤ k) : a j ≤ a k := by` |
| `a_nonneg` | a96J01 | `(n : ℕ) : 0 ≤ a n := by` |
| `a_zero` | a96J01 | `: a 0 = 0 := by simp [a]` |
| `abs_arctan_eq_arctan_abs` | a95J05 | `(t : ℝ) : |arctan t| = arctan |t| := by` |
| `abs_arctan_lt` | a95J05 | `(t : ℝ) : |arctan t| < π / 2 := by` |
| `abs_cexp_I_mul` | a03J07 | `(ε : ℝ) (z : ℂ) :` |
| `abs_exp_mul_real` | a01A09 | `(z : ℂ) (t : ℝ) :` |
| `abs_integral_exp_neg_mul_sinc_Ioi_le_four_div` | LIB:ConstructionTargets.Sinc | `{a A : ℝ} (ha : 0 < a) (hA : 0 < A) :` |
| `abs_integral_exp_neg_mul_sinc_le_four_div` | LIB:ConstructionTargets.Sinc | `{a A B : ℝ} (ha : 0 < a) (hA : 0 < A) (hAB : A ≤ B) :` |
| `abs_integral_sinc_le_two_div` | LIB:ConstructionTargets.Sinc | `{a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :` |
| `abs_laplace_kernel` | a01A09 | `(z : ℂ) (t : ℝ) :` |
| `abs_polynomial_eval_le_absCoeff` | a96A04 | `(p : Polynomial ℝ) (x : ℝ) :` |
| `abs_sq` | a02J06 | `(z : ℂ) : ‖z ^ 2‖ = ‖z‖ ^ 2 := by` |
| `abs_sub_pow_le` | a02J02 | `{p : ℕ} (a b : ℝ) :` |
| `absolute_continuity_integral` | a94J01 | `{f : (Fin n → ℝ) → ℝ}` |
| `absolute_continuity_integral_norm` | a94J01 | `{f : (Fin n → ℝ) → ℝ}` |
| `absolutelyContinuousOnInterval_maps_null_to_null` | LIB:ConstructionTargets.LusinN | `{f : ℝ → ℝ} {a b : ℝ}` |
| `acOnUnitInterval_iff` | LIB:ConstructionTargets.LusinN | `(f : ℝ → ℝ) :` |
| `acOnUnitInterval_iff` | a95A02 | `(f : ℝ → ℝ) :` |
| `ac_continuousOn` | LIB:ConstructionTargets.LusinN | `{f : ℝ → ℝ}` |
| `ac_continuousOn` | a95A02 | `{f : ℝ → ℝ}` |
| `ac_dist_le_integral_norm_deriv` | LIB:ConstructionTargets.LusinN | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f)` |
| `ac_dist_le_integral_norm_deriv` | a95A02 | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f)` |
| `ac_iff_lipschitz_V_approx` | a93A04 | `(f : ℝ → ℝ) :` |
| `ac_image_compact_is_compact` | LIB:ConstructionTargets.LusinN | `{f : ℝ → ℝ}` |
| `ac_image_compact_is_compact` | a95A02 | `{f : ℝ → ℝ}` |
| `ac_implies_lipschitz_V_approx` | a93A04 | `{f : ℝ → ℝ} (hac : AbsolutelyContinuousOnInterval f 0 1) :` |
| `ac_integral_deriv_eq_sub` | LIB:ConstructionTargets.LusinN | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f)` |
| `ac_integral_deriv_eq_sub` | a95A02 | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f)` |
| `ac_intervalIntegrable_deriv` | LIB:ConstructionTargets.LusinN | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) :` |
| `ac_intervalIntegrable_deriv` | a95A02 | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) :` |
| `ac_lusin_condition_N` | LIB:ConstructionTargets.LusinN | `{f : ℝ → ℝ}` |
| `ac_lusin_condition_N` | a95A02 | `{f : ℝ → ℝ}` |
| `ac_lusin_condition_N_lt_aux` | LIB:ConstructionTargets.LusinN | `{f : ℝ → ℝ}` |
| `ac_lusin_condition_N_lt_aux` | a95A02 | `{f : ℝ → ℝ}` |
| `ac_maps_measurable_to_measurable` | a95A02 | `{f : ℝ → ℝ}` |
| `ac_maps_null_to_null` | LIB:ConstructionTargets.LusinN | `{f : ℝ → ℝ}` |
| `ac_maps_null_to_null` | a95A02 | `{f : ℝ → ℝ}` |
| `ac_monotone_maps_null_to_null` | a96J04 | `(f : ℝ → ℝ)` |
| `ac_of_bv_continuous_conditionN` | a95J06 | `{f : ℝ → ℝ}` |
| `ac_on_01_of_continuous_bv_ac_from_a` | a93J01 | `{f : ℝ → ℝ}` |
| `ac_on_01_of_homeo_fixing_cantor` | a95J06 | `{f : ℝ → ℝ}` |
| `ac_volume_image_component_le_lintegral_enorm_deriv` | LIB:ConstructionTargets.LusinN | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f)` |
| `ac_volume_image_component_le_lintegral_enorm_deriv` | a95A02 | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f)` |
| `ac_volume_image_subset_Icc_le_integral_norm_deriv` | LIB:ConstructionTargets.LusinN | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f)` |
| `ac_volume_image_subset_Icc_le_integral_norm_deriv` | a95A02 | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f)` |
| `accPt_closedBall_of_mem_sphere` | LIB:ConstructionTargets.Rouche | `{c z : ℂ} {R : ℝ} (hR : 0 < R) (hz : z ∈ sphere c R) :` |
| `add_pow_le_two_pow_mul` | a02J02 | `{p : ℕ} (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :` |
| `add_smul_ne_zero_of_norm_le_one` | LIB:ConstructionTargets.Rouche | `{f g : ℂ → ℂ} {z t : ℂ}` |
| `adjoint_eq` | m98J03 | `: P.adjoint = P := by` |
| `ae_abs_le_of_interval_integral_bound` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ)` |
| `ae_hasDerivAt_constructedH_zero_on` | a94J02 | `(C : Set ℝ) (hC_meas : MeasurableSet C) :` |
| `ae_limit_indicator_eq_indicator` | a94A01 | `{Eₙ : ℕ → Set ℝ}` |
| `ae_ne_restrict` | a96A08 | `(s : Set ℝ) (a : ℝ) :` |
| `ae_pos_of_limit_pos` | a96A01 | `{f : ℝ → ℝ}` |
| `ae_tendsto_radialLaverage` | LIB:ConstructionTargets.RadialMajorantAE | `{f : ℝ → ℝ}` |
| `aeval_g` | a92J05 | `(z : ℂ) : aeval z g = 5 * z ^ 3 := by simp [g]` |
| `aeval_h` | a92J05 | `(z : ℂ) : aeval z h = z ^ 10 + 2 * z + 1 := by simp [h]` |
| `aeval_p` | a92J05 | `(z : ℂ) : aeval z p = z ^ 10 + 5 * z ^ 3 + 2 * z + 1 := by simp [p]` |
| `affine_of_entire_of_linear_growth` | LIB:ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f)` |
| `affine_of_entire_pick` | LIB:ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f)` |
| `affine_of_entire_pick_neg` | LIB:ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f)` |
| `algPoly_degree_le` | a95J03 | `(a : ℤ → ℂ) (N : ℕ) :` |
| `algPoly_sub_degree_le` | a95J03 | `(a : ℤ → ℂ) (N : ℕ) (z : ℂ) :` |
| `alg_G_deriv` | a94A06 | `(x : ℝ) :` |
| `alg_h3` | a94A06 | `(u : ℝ) :` |
| `alg_sum` | a94A06 | `(u : ℝ) (hu : 0 ≤ u) :` |
| `almostEqualVolume_comm` | a01J02 | `{A B : Set ℝ} :` |
| `alone` | m97A03 | `therefore does not close the goal within this pass's budget.` |
| `alpha_ge_one` | a01J06 | `(data : ProblemData) : 1 ≤ data.α :=` |
| `alpha_nonneg` | a01J06 | `(data : ProblemData) : 0 ≤ data.α :=` |
| `alpha_pos` | a01J06 | `(data : ProblemData) : 0 < data.α :=` |
| `alpha_sub_one_nonneg` | a01J06 | `(data : ProblemData) : 0 ≤ data.α - 1 :=` |
| `alpha_sub_one_pos` | a01J06 | `(data : ProblemData) : 0 < data.α - 1 :=` |
| `alternating_harmonic_eq_log_two` | a93J02 | `:` |
| `analyticOn_closedUnitDisk_continuous` | a01J05 | `{f : ℂ → ℂ} (hhol : AnalyticOn ℂ f closedUnitDisk) :` |
| `analyticOrderAt_sub_self_ne_top_of_injOn` | LIB:ConstructionTargets.UnivalentDeriv | `{U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}` |
| `analytic_blowup_surjective` | a03J08 | `{F : Finset ℂ}` |
| `analytic_compactSupport_eq_zero` | a01A03 | `(f : ℝ → ℝ) (hf : ContDiff ℝ ω f) (hfc : HasCompactSupport f) :` |
| `apmB03NotIntegrallyClosed` | b03J03 | `:` |
| `apmB03RootSq` | b03J03 | `:` |
| `apmN_eq_apmEc` | a03J01 | `{d : ℕ} (E : ℕ → Set (EuclideanSpace ℝ (Fin d))) :` |
| `apmTwoGeneratorIdeal_not_principal` | b03J02 | `(R : Type*) [CommRing R] [IsDomain R] (a : R)` |
| `apm_a01J05_main` | a01J05 | `(f : ℂ → ℂ)` |
| `apm_a01J06_main` | a01J06 | `(data : ProblemData) :` |
| `apm_a94J06_at_zero` | a94J06 | `:` |
| `apm_a94J06_inside` | a94J06 | `{z : ℂ} (hz : ‖z‖ < 1) :` |
| `apm_a94J06_inside_nonzero` | a94J06 | `{z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :` |
| `apm_a94J06_outside` | a94J06 | `{z : ℂ} (hz : 1 < ‖z‖) :` |
| `apm_a94a02_ae_all_differentiable` | a94A02 | `(f : ℕ → ℝ → ℝ)` |
| `apm_a96J09_coeff_tendsto_zero_of_contains_closed_disk` | a96J09 | `(D : Set ℂ) (hD_open : IsOpen D)` |
| `apm_a96J09_main` | a96J09 | `(D : Set ℂ) (hD_open : IsOpen D) (_hD_zero : (0 : ℂ) ∈ D)` |
| `apm_a96J10_even_factors` | a96J10 | `(h : ℂ → ℂ) (hh : AnalyticOn ℂ h (Metric.ball (0:ℂ) 1))` |
| `apm_a96J10_f_analytic` | a96J10 | `:` |
| `apm_a96J10_f_even` | a96J10 | `(z : ℂ) (hz : ‖z‖ < 1) :` |
| `apm_a96J10_main` | a96J10 | `:` |
| `apm_a96J10_q_analytic` | a96J10 | `: AnalyticOn ℂ apm_a96J10_q univ := by` |
| `apm_a96J10_q_nonzero_on_ball` | a96J10 | `{z : ℂ} (hz : ‖z‖ < 1) :` |
| `apm_a96J10_q_of_ne` | a96J10 | `(z : ℂ) (hz0 : z ≠ 0) :` |
| `apm_a97A05_cayley_maps_RHP_to_disk` | a97A05 | `(w : ℂ) (hw : 0 < w.re) :` |
| `apm_a97A05_main` | a97A05 | `(f : ℂ → ℂ) (hf : AnalyticOn ℂ f UHP)` |
| `apm_a97A05_psi_analytic` | a97A05 | `(f : ℂ → ℂ) (hf : AnalyticOn ℂ f UHP)` |
| `apm_a97A05_psi_bdd` | a97A05 | `(f : ℂ → ℂ) (hf : AnalyticOn ℂ f UHP)` |
| `apm_a97A05_shift_to_RHP` | a97A05 | `(f : ℂ → ℂ) (M : ℝ) (hM : 0 ≤ M)` |
| `apm_a97A06_F_analytic` | a97A06 | `: AnalyticOn ℂ apm_a97A06_F univ := by` |
| `apm_a97A06_F_continuousAt_zero` | a97A06 | `:` |
| `apm_a97A06_arc_exp_vanishes` | a97A06 | `:` |
| `apm_a97A06_arc_inv_eq_iPi` | a97A06 | `(R : ℝ) (hR : 0 < R) :` |
| `apm_a97A06_arc_inv_sq_vanishes` | a97A06 | `:` |
| `apm_a97A06_finite_identity` | a97A06 | `(R : ℝ) :` |
| `apm_a97A06_integrable` | a97A06 | `:` |
| `apm_a97A06_main` | a97A06 | `:` |
| `apm_a97A06_q_deriv` | a97A06 | `(x : ℝ) :` |
| `apm_a97A06_q_hasDerivAt` | a97A06 | `(x : ℝ) :` |
| `apm_a97A06_real_part` | a97A06 | `(x : ℝ) (hx : x ≠ 0) :` |
| `apm_a97A06_tendsto_finite_identity` | a97A06 | `:` |
| `apm_a97A06_tendsto_q_atTop` | a97A06 | `:` |
| `apm_a97A07_P_polynomial` | a97A07 | `(n : ℕ) (hn : 0 < n)` |
| `apm_a97A07_Q_eval_zs` | a97A07 | `(zs : Fin n → ℂ) (k : Fin n) (zeta : ℂ)` |
| `apm_a97A07_Q_polynomial_in_z` | a97A07 | `(n : ℕ) (hn : 0 < n) (zs : Fin n → ℂ) (ζ : ℂ) :` |
| `apm_a97A07_interpolates` | a97A07 | `(n : ℕ) (hn : 0 < n)` |
| `apm_a97A07_main` | a97A07 | `(n : ℕ) (hn : 0 < n)` |
| `apm_a97A08_count_inner` | a97A08 | `:` |
| `apm_a97A08_count_outer` | a97A08 | `:` |
| `apm_a97A08_main` | a97A08 | `:` |
| `apm_a97A08_no_zeros_inner` | a97A08 | `(z : ℂ) (hz : ‖z‖ = 3/2) :` |
| `apm_a97A08_no_zeros_outer` | a97A08 | `(z : ℂ) (hz : ‖z‖ = 2) :` |
| `apm_a97A08_rouche_inner` | a97A08 | `(z : ℂ) (hz : ‖z‖ = 3/2) :` |
| `apm_a97A08_rouche_outer` | a97A08 | `(z : ℂ) (hz : ‖z‖ = 2) :` |
| `apm_a97J03_convolution_continuous` | a97J03 | `{p q : ℝ}` |
| `apm_a97J03_convolution_tendsto_zero` | a97J03 | `{p q : ℝ}` |
| `apm_a97J05_hasFPowerSeriesAt_div_sub_one` | a97J05 | `(A : ℂ) :` |
| `apm_a97J05_remainder_update_continuousAt` | a97J05 | `(f g : ℂ → ℂ) (z₀ A : ℂ)` |
| `apm_b01J03_selfNormalizer_count` | b01J03 | `(G : Type*) [Group G] [Finite G]` |
| `apm_b01J04_simultaneous_of_commute` | b01J04 | `{n : Type*} [Fintype n] [DecidableEq n]` |
| `apm_b03J01_isZGroup_of_twinPrime_card` | b03J01 | `(G : Type*) [Group G] [Fintype G] (p : ℕ) (hp : p.Prime)` |
| `apm_b03J01_twinPrime_squarefree` | b03J01 | `(p : ℕ) (hp : p.Prime)` |
| `apm_b90a02_rat_to_int_eq_zero` | b90A02 | `(f : ℚ →ₗ[ℤ] ℤ) (q : ℚ) : f q = 0 := by` |
| `apm_b93a01_abelian_of_normal_prime_factors` | b93A01 | `(G : Type) [Group G] [Fintype G] (p q : ℕ)` |
| `apm_b93a03_flat_addEquiv` | b93A03 | `{M N : Type}` |
| `apm_b93a03_flat_int` | b93A03 | `: apm_b93a03_flat ℤ := by` |
| `apm_b93a03_flat_of_addEquiv` | b93A03 | `{M N : Type}` |
| `apm_b93j04_radical_root` | b93J04 | `(K : Type*) [Field K] [Algebra ℚ K]` |
| `apm_m94J04_inner_curlValue` | m94J04 | `(φ : apm_m94J04_E → apm_m94J04_E) (p : apm_m94J04_E) :` |
| `apm_m94J04_inner_u_curlTest` | m94J04 | `(φ : apm_m94J04_E → apm_m94J04_E) (p : apm_m94J04_E) :` |
| `apm_m96J06_half_shift_mem` | m96J06 | `{t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) :` |
| `apm_m96J06_linearPart_involutive` | m96J06 | `(x : ℝ → ℝ) :` |
| `apm_m96J06_quadratic_continuousOn` | m96J06 | `{x : ℝ → ℝ}` |
| `apm_m96J06_quadratic_sub_bound` | m96J06 | `{x z : ℝ → ℝ} {r : ℝ} (hr : 0 ≤ r)` |
| `apm_m96a05_unique_of_det` | m96A05 | `{n : ℕ} {a b c : ℝ → ℝ}` |
| `apm_m96a06_integrable_force` | m96A06 | `{α : Type*} [MeasurableSpace α] {μ : Measure α}` |
| `apm_m96a06_integrable_pair` | m96A06 | `{α : Type*} [MeasurableSpace α] {μ : Measure α} (f g : Lp ℝ 2 μ) :` |
| `apm_m96a06_integrable_weighted_pair` | m96A06 | `{α : Type*} [MeasurableSpace α] {μ : Measure α}` |
| `apm_m96j02_continuousOn_comp_graph` | m96J02 | `(g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)` |
| `apm_m96j02_intervalIntegrable_comp_graph` | m96J02 | `(g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)` |
| `apm_m96j03_integral_ballIndicator` | m96J03 | `{n : ℕ}` |
| `apm_m96j04_block_exists` | m96J04 | `:` |
| `apm_m96j05_symbol_norms` | m96J05 | `(ε ξ : ℝ) :` |
| `apm_m97A01_modulus_core` | m97A01 | `(X : Type*) [NormedAddCommGroup X]` |
| `apm_m97A02_anchor_preserved` | m97A02 | `{α : ℝ} (hα : Real.cos α = α)` |
| `apm_m97A02_anchored_pointwise_bound` | m97A02 | `{α r t : ℝ} {x : ℝ → ℝ}` |
| `apm_m97A02_cos_mem_Icc` | m97A02 | `{t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :` |
| `apm_m97A03_t_sqrt_bound` | m97A03 | `{t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :` |
| `apm_m98J04_arcLength_line` | m98J04 | `(a b α β : ℝ) (hab : a < b) :` |
| `apm_m98J04_deriv_line` | m98J04 | `(a b α β x : ℝ) :` |
| `apm_m98J05_fourier_integrable` | m98J05 | `(f : ℝ → ℂ) (hf : Integrable f) (ξ : ℝ) :` |
| `apm_m98a02_trivial_space_obstruction` | m98A02 | `(A B : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ)) :` |
| `apm_m98a03_integrable_kernel_section` | m98A03 | `(K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)` |
| `apm_m98a05_hasStrictFDerivAt_of_contDiff` | m98A05 | `{E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]` |
| `apm_m98a06_nonresonant_candidate_admissible` | m98A06 | `{a : ℝ} (ha : Real.sin a ≠ 0) :` |
| `apm_m99A01_extremal_ode` | m99A01 | `(t : ℝ) :` |
| `apm_m99A01_sine_family_admissible` | m99A01 | `(n : ℝ) :` |
| `apm_m99J06_galerkin_energy` | m99J06 | `{H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]` |
| `apm_m99j01_cos_fixed_unique` | m99J01 | `{x y : ℝ}` |
| `apm_m99j02_wronskian_eq_zero` | m99J02 | `(u₁ u₂ q : ℝ → ℝ) (hu₁ : ContDiff ℝ 2 u₁) (hu₂ : ContDiff ℝ 2 u₂)` |
| `apm_m99j03_dilation_integrable` | m99J03 | `(ψ φ : ℝ → ℝ) (hψ : Continuous ψ) (hφ : Continuous φ)` |
| `apm_m99j04_weight_inner` | m99J04 | `{𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]` |
| `arctan_pos'` | a95J05 | `{t : ℝ} (ht : 0 < t) : 0 < arctan t :=` |
| `arctan_zero'` | a95J05 | `: arctan 0 = 0 := arctan_zero` |
| `argStar_eq` | a02J07 | `(z : ℂ) : argStar z = arg (-z) + π := by` |
| `argStar_lt_two_pi` | a02J07 | `{z : ℂ} (hz : z ∈ posSlitPlane) : argStar z < 2 * π := by` |
| `argStar_pos` | a02J07 | `{z : ℂ} (hz : z ∈ posSlitPlane) : 0 < argStar z := by` |
| `auxProd_continuousOn` | a95A05 | `{f : ℂ → ℂ} (hf : ContinuousOn f (closedBall 0 1)) :` |
| `auxProd_diffContOnCl` | a95A05 | `{f : ℂ → ℂ}` |
| `auxProd_differentiableOn` | a95A05 | `{f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) :` |
| `auxProd_vanish_on_frontier` | a95A05 | `{f : ℂ → ℂ}` |
| `b_def` | a96J01 | `(n : ℕ) : b n = 1 - (2 : ℝ)⁻¹ ^ (n + 1) := rfl` |
| `b_eq_a_succ` | a96J01 | `(n : ℕ) : b n = a (n + 1) := rfl` |
| `b_le_one` | a96J01 | `(n : ℕ) : b n ≤ 1 := by` |
| `ballSlice_integral_eq_sin_pow` | a01A04 | `(n : ℕ) (hn : 0 < n) :` |
| `ballSlice_integral_tendsto_zero` | a01A04 | `:` |
| `ballSlice_le_one` | a01A04 | `(t : ℝ) : ballSlice t ≤ 1 := by` |
| `ballSlice_lt_one_of_ne_zero` | a01A04 | `{t : ℝ} (ht : t ≠ 0) : ballSlice t < 1 := by` |
| `ballSlice_nonneg` | a01A04 | `(t : ℝ) : 0 ≤ ballSlice t := by` |
| `ball_bounded` | a95A05 | `: Bornology.IsBounded (ball (0 : ℂ) 1) :=` |
| `ball_volume_recursion` | a01A04 | `(n : ℕ) (hn : 0 < n) :` |
| `ball_volume_superexponential_decay` | a01A04 | `(A : ℝ) (hA : 0 < A) :` |
| `banachZarecki_monotone` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `blaschke_factorization` | a01J05 | `(f : ℂ → ℂ)` |
| `bound_origin` | a01J06 | `(data : ProblemData) :` |
| `bound_pos` | a97A04 | `(k : ℕ) : 0 < bound k := by` |
| `bound_rhs_nonneg` | a01J06 | `(data : ProblemData) (z : ℂ) :` |
| `boundary_has_no_zeros` | a01J05 | `{f : ℂ → ℂ}` |
| `bounded_integral_implies_integrable` | a97J01 | `(f : ℝ → ℝ)` |
| `bpm_1_1_1` | bpm-1-1-1 | `(θ p : ℝ)` |
| `bpm_1_1_2` | bpm-1-1-2 | `(f : ℝ → ℝ)` |
| `bpm_1_2_2` | bpm-1-2-2 | `(f : ℝ → ℝ)` |
| `bpm_1_3_1` | bpm-1-3-1 | `(k : ℕ)` |
| `bpm_1_3_2` | bpm-1-3-2 | `:` |
| `bpm_1_4_1` | bpm-1-4-1 | `(a b : ℝ)` |
| `bpm_1_5_1` | bpm-1-5-1 | `(f : ℝ → ℝ)` |
| `bpm_1_6_2` | bpm-1-6-2 | `(f : ℕ → ℝ → ℝ)` |
| `bpm_1_7_1` | bpm-1-7-1 | `(f : ℝ → ℝ)` |
| `bpm_1_8_1` | bpm-1-8-1 | `(f : ℝ → ℝ)` |
| `canonicalFactor_self_zero` | a01J05 | `(R : ℝ) (w : ℂ) :` |
| `canonicalFactor_unitCircle_norm_one` | a01J05 | `{w z : ℂ} (hw : ‖w‖ < 1) (hz : z ∈ unitCircle) :` |
| `cantorSet_measure_zero` | a95J06 | `: volume cantorSet = 0 := by` |
| `card_roots_le_degree` | LIB:ConstructionTargets.LemniscateComponents | `(hp : 0 < p.natDegree) :` |
| `card_roots_le_degree` | a00J04 | `(hp : 0 < p.natDegree) :` |
| `card_roots_le_degree` | a01A08 | `(hp : 0 < p.natDegree) :` |
| `card_sym3` | b93J01 | `:` |
| `card_zmod2_cubed` | b93J01 | `:` |
| `cauchyTransform_differentiableAt` | a00J05 | `{z₀ : ℂ} (hz₀ : z₀ ∉ (↑) '' K) :` |
| `cauchyTransform_differentiableAt` | a01A11 | `(z : ℂ) (hz : z ∉ ofReal '' K) :` |
| `cauchyTransform_differentiableOn` | a00J05 | `:` |
| `cauchyTransform_mul_z_tendsto` | a00J05 | `:` |
| `cauchyTransform_not_entire` | a01A11 | `(h_diff : ∀ z, z ∉ ofReal '' K → DifferentiableAt ℂ (cauchyTransform K) z)` |
| `cauchyTransform_not_extendable_to_entire` | a00J05 | `(g : ℂ → ℂ) (hg : Differentiable ℂ g)` |
| `cauchyTransform_tendsto_neg_vol` | a01A11 | `:` |
| `cauchy_estimate_taylor` | a96A06 | `(g : ℂ → ℂ) (hg : Differentiable ℂ g) (n : ℕ) {R : ℝ} (hR : 0 < R)` |
| `cauchy_riemann_ray_implies_const` | a92J07 | `{u v : ℝ → ℝ → ℝ}` |
| `cauchy_schwarz_bound` | a00J02 | `(f : ℝ → ℝ) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)` |
| `chain_rule_at_zero` | a95J01 | `{f g h : ℂ → ℂ}` |
| `characterizing` | m93A01 | `compact diagonal multipliers on `lp`, and no theorem` |
| `circleAverage_poissonKernel_smul_im_eq` | LIB:ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f)` |
| `circleAverage_poissonKernel_smul_im_eq_upper` | LIB:ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f)` |
| `circleIntegrable_sub_inv_of_not_on_circle` | a94J06 | `{w : ℂ} (hw : ‖w‖ ≠ 1) :` |
| `circleIntegral_inv` | a96A05 | `:` |
| `circleIntegral_inv_sub_polynomial` | a96A05 | `(P : Polynomial ℂ) :` |
| `circleIntegral_logDeriv_eq_divisor_sum` | LIB:ConstructionTargets.Rouche | `{f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)` |
| `circleIntegral_logDeriv_eq_zero_of_analyticOnNhd_of_ne_zero` | LIB:ConstructionTargets.Rouche | `{h : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)` |
| `circleIntegral_logDeriv_factorizedRational` | LIB:ConstructionTargets.Rouche | `{U : Set ℂ} (D : Function.locallyFinsuppWithin U ℤ)` |
| `circleIntegral_polynomial` | a96A05 | `(P : Polynomial ℂ) :` |
| `circleMap_two_pi_sub` | LIB:ConstructionTargets.HerglotzRigidity | `(R θ : ℝ) :` |
| `clamp01_eq_self` | LIB:ConstructionTargets.BanachZarecki | `{x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : clamp01 x = x := by` |
| `clamp01_mem` | LIB:ConstructionTargets.BanachZarecki | `(x : ℝ) : clamp01 x ∈ Icc (0 : ℝ) 1 := by` |
| `coefficients_bounded_of_simple_poles` | a95J04 | `{D : Set ℂ} (hD : IsOpen D) (hD_contains : closedBall (0 : ℂ) 1 ⊆ D)` |
| `coefficients_bounded_simple_pole` | a95J04 | `(ζ : ℂ) (c : ℂ) (hζ : ‖ζ‖ = 1) :` |
| `commute_preserves` | m98J03 | `(A : H ->L[Real] H) (hcomm : A.comp P = P.comp A) :` |
| `compact_is_measurable` | LIB:ConstructionTargets.LusinN | `{K : Set ℝ}` |
| `compact_is_measurable` | a95A02 | `{K : Set ℝ}` |
| `complete_square` | a01A10 | `(x y : ℝ) :` |
| `componentSet_connected` | LIB:ConstructionTargets.LemniscateComponents | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_connected` | a00J04 | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_connected` | a01A08 | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_eq_of_common_point` | LIB:ConstructionTargets.LemniscateComponents | `{x y : ↥((lemniscate p)ᶜ)} {z : ℂ}` |
| `componentSet_eq_of_common_point` | a00J04 | `{x y : ↥((lemniscate p)ᶜ)} {z : ℂ}` |
| `componentSet_eq_of_common_point` | a01A08 | `{x y : ↥((lemniscate p)ᶜ)} {z : ℂ}` |
| `componentSet_frontier_subset_lemniscate` | LIB:ConstructionTargets.LemniscateComponents | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_frontier_subset_lemniscate` | a00J04 | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_frontier_subset_lemniscate` | a01A08 | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_nonempty` | LIB:ConstructionTargets.LemniscateComponents | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_nonempty` | a00J04 | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_nonempty` | a01A08 | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_open` | LIB:ConstructionTargets.LemniscateComponents | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_open` | a00J04 | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_open` | a01A08 | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_subset_compl` | LIB:ConstructionTargets.LemniscateComponents | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_subset_compl` | a00J04 | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_subset_compl` | a01A08 | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_subset_superlevel_or_sublevel` | LIB:ConstructionTargets.LemniscateComponents | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_subset_superlevel_or_sublevel` | a00J04 | `(x : ↥((lemniscate p)ᶜ)) :` |
| `componentSet_subset_superlevel_or_sublevel` | a01A08 | `(x : ↥((lemniscate p)ᶜ)) :` |
| `component_eq_of_subset_superlevel` | LIB:ConstructionTargets.LemniscateComponents | `(hp : 0 < p.natDegree) {x y : ↥((lemniscate p)ᶜ)}` |
| `component_eq_of_subset_superlevel` | a00J04 | `(hp : 0 < p.natDegree) {x y : ↥((lemniscate p)ᶜ)}` |
| `component_eq_of_subset_superlevel` | a01A08 | `(hp : 0 < p.natDegree) {x y : ↥((lemniscate p)ᶜ)}` |
| `composition_isometric_isomorphism` | a00J03 | `[Fact (1 ≤ p)]` |
| `composition_isometry` | a00J03 | `[Fact (1 ≤ p)]` |
| `conditionN_on_cantor_of_fix` | a95J06 | `{f : ℝ → ℝ} (hf_fix : ∀ x ∈ cantorSet, f x = x) :` |
| `conformalMap_maps_H_to_A` | a01A12 | `(z : ℂ) (hz : 0 < z.im) :` |
| `conj_apply_conj_eq` | LIB:ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f)` |
| `conj_eq_inv_on_circle` | a94J06 | `{ζ : ℂ} (hζ : ‖ζ‖ = 1) :` |
| `connectedComponents_complement_lemniscate_le` | LIB:ConstructionTargets.LemniscateComponents | `(p : ℂ[X]) :` |
| `connectedComponents_complement_lemniscate_le` | a00J04 | `:` |
| `connectedComponents_complement_lemniscate_le` | a01A08 | `:` |
| `connected_iff_ladderConnected` | t94J01 | `:` |
| `connected_manifold_path_connected` | t94A05 | `(H M : Type*) [TopologicalSpace H] [TopologicalSpace M]` |
| `connected_of_ladderConnected` | t94J01 | `(h : LadderConnectedSpace X) :` |
| `connected_superset_meets_unit_sphere` | a95A06 | `{U : Set ℂ} (hconn : IsConnected U)` |
| `connected_union` | t92J01 | `{C : A → Set X} {x : X}` |
| `constant_of_symmetric_mean_value` | a95A04 | `{f : ℝ → ℝ}` |
| `constructedH_deriv_zero_pos_measure` | a94J02 | `(C : Set ℝ) (hC_meas : MeasurableSet C) (hC_pos : 0 < volume C) :` |
| `constructedH_mono` | a94J02 | `(C : Set ℝ) (hC_meas : MeasurableSet C) {x y : ℝ}` |
| `constructedH_nonneg` | a94J02 | `(C : Set ℝ) {x : ℝ} (hx : 0 ≤ x) :` |
| `constructedH_strictMonoOn` | a94J02 | `(C : Set ℝ) (hC_closed : IsClosed C) (_hC_sub : C ⊆ Icc 0 1)` |
| `constructedH_strictMonoOn_counterexample` | a94J02 | `:` |
| `constructedH_strictMonoOn_of_isClosed` | a94J02 | `(C : Set ℝ) (hC_closed : IsClosed C) (hC_int : interior C = ∅) :` |
| `continuous_circleIntegral_logDeriv_roucheHomotopy` | LIB:ConstructionTargets.Rouche | `{f g : ℂ → ℂ} {c : ℂ} {R : ℝ}` |
| `continuous_clamp01` | LIB:ConstructionTargets.BanachZarecki | `: Continuous clamp01 := by` |
| `continuous_convolution_indicator` | a96J02 | `(A B : Set ℝ) (hA : MeasurableSet A)` |
| `continuous_distTo` | t94A02 | `(S : Set ℝ) : Continuous fun x : ℝ => distTo S x := by` |
| `continuous_folded_poisson_integrand` | LIB:ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f)` |
| `continuous_monotoneExtension` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ}` |
| `continuous_overlapMeasure` | a96J02 | `(A B : Set ℝ) (hA : MeasurableSet A)` |
| `continuous_overlapSet` | a96J02 | `(A B : Set ℝ) (hA : MeasurableSet A)` |
| `continuous_poissonKernel_mul_im_circle` | LIB:ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f)` |
| `continuous_satisfies_pointwise_pole_alternative` | a95J04 | `{f : ℂ → ℂ}` |
| `continuous_sepFun` | t94A02 | `{A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)` |
| `continuous_subtractionMap` | a96J02 | `: Continuous subtractionMap := by` |
| `contour_integral_eval` | a92J06 | `:` |
| `contraction_fixedPoint` | t91A04 | `{λ : ℝ} (hλ₀ : 0 ≤ λ) (hλ₁ : λ < 1)` |
| `convergenceSet_eq_approx` | a97A04 | `(f : ℕ → α → ℝ) :` |
| `convergesInMeasure.exists_subseq_ae_tendsto` | a92J02 | `{f : ℕ → α → ℝ} {g : α → ℝ}` |
| `convergesInMeasure.tendstoInMeasure` | a92J02 | `{f : ℕ → α → ℝ} {g : α → ℝ}` |
| `convolution_aestronglyMeasurable` | LIB:ConstructionTargets.YoungConvolution | `{f g : ℝ → ℝ}` |
| `convolution_continuous` | a03J03 | `{p q : ℝ} (hpq : p.HolderConjugate q)` |
| `convolution_identity_counterexample` | a01A03 | `:` |
| `convolution_identity_implies_indicator` | a01A03 | `(g : ℝ → ℝ) (hg1 : Integrable g volume)` |
| `convolution_indicator_eq_overlapReal` | a96J02 | `(A B : Set ℝ) (hA : MeasurableSet A)` |
| `convolution_integrand_integrableAE` | a95J08 | `{f g : ℝ → ℝ}` |
| `convolution_memLp` | LIB:ConstructionTargets.YoungConvolution | `{f g : ℝ → ℝ}` |
| `convolution_tendsto_zero` | a03J03 | `{p q : ℝ} (hpq : p.HolderConjugate q)` |
| `countable_ordConnectedSection_of_isOpen` | LIB:ConstructionTargets.LusinN | `{U : Set ℝ} (hU : IsOpen U) :` |
| `countable_ordConnectedSection_of_isOpen` | a95A02 | `{U : Set ℝ} (hU : IsOpen U) :` |
| `counterexample_from_spikes` | a01J01 | `:` |
| `curve_length_ge_two_pi` | a95A08 | `{f : ℂ → ℂ}` |
| `damped_fresnel_boundary_norm_le` | a01A10 | `{ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 < x) :` |
| `damped_fresnel_integration_by_parts` | a01A10 | `{ε a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :` |
| `damped_fresnel_remainder_norm_le` | a01A10 | `{ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 < x) :` |
| `dense_compl_of_interior_empty` | a95A01 | `(K : Set ℝ) (hK_int : interior K = ∅) :` |
| `dense_iInter_of_open_dense` | t92J03 | `{X : Type*} [MetricSpace X] [CompleteSpace X] {U : ℕ → Set X}` |
| `densityFun_nonneg` | a94J02 | `(C : Set ℝ) (t : ℝ) : 0 ≤ densityFun C t := by` |
| `derivZeroFinset_subset_closedUnitDisk` | a01J05 | `(f : ℂ → ℂ)` |
| `derivZeroSet_finite_of_analytic` | a01J05 | `{f : ℂ → ℂ}` |
| `derivZeroSet_mul_const` | a01J05 | `{f : ℂ → ℂ} {μ : ℂ} (hμ : μ ≠ 0) :` |
| `derivZeroSet_subset_closedUnitDisk` | a01J05 | `(f : ℂ → ℂ) :` |
| `deriv_eq_zero_of_factorization` | a94A10 | `(f : ℂ → ℂ)` |
| `deriv_ne_zero_of_injOn` | LIB:ConstructionTargets.UnivalentDeriv | `{U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}` |
| `deriv_ne_zero_on_reals` | a94A10 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f) (hreal : RealIffReal f) :` |
| `deriv_norm_le_norm` | a93J06 | `{f : ℂ → ℂ}` |
| `deriv_norm_le_sup_div_radius` | a01A07 | `{g : ℂ → ℂ} {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)` |
| `deriv_sum_of_monotone` | a01J03 | `(f : ℝ → ℝ) (fns : ℕ → ℝ → ℝ)` |
| `deriv_sum_of_monotone_ae` | a01J03 | `(f : ℝ → ℝ) (fns : ℕ → ℝ → ℝ)` |
| `derivative_zero_count` | a01J05 | `(f : ℂ → ℂ)` |
| `derivative_zero_subset` | a01J05 | `(f : ℂ → ℂ)` |
| `derives` | a94J04 | `this from the Lebesgue differentiation theorem and the` |
| `diffContOnCl_aeval` | LIB:ConstructionTargets.LemniscateComponents | `(p : ℂ[X]) (U : Set ℂ) :` |
| `diffContOnCl_aeval` | a00J04 | `(p : ℂ[X]) (U : Set ℂ) :` |
| `diffContOnCl_aeval` | a01A08 | `(p : ℂ[X]) (U : Set ℂ) :` |
| `diffQuot_implies_unifCont` | a93A01 | `{f : ℝ → ℝ} (hf : DiffQuotientCondition f) :` |
| `differentiableOn_of_L1_limit` | a01A07 | `{f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}` |
| `differentiable_image_null_of_null` | a03J02 | `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]` |
| `directly` | a94J05 | `). We use Mathlib's packaged Liouville instead.` |
| `dirichlet_integral_improper` | LIB:ConstructionTargets.Sinc | `:` |
| `dirichlet_integral_improper` | a02J05 | `:` |
| `disk_not_subset_image_of_length_gt` | a95A08 | `{f : ℂ → ℂ}` |
| `disk_selfmap_deriv_one_eq_identity` | a92J04 | `{f : ℂ → ℂ}` |
| `disk_selfmap_tangent_identity` | a92J04 | `{a : ℕ → ℂ}` |
| `disk_selfmap_tangent_identity'` | a92J04 | `(f : ℂ → ℂ)` |
| `distTo_add_pos` | t94A02 | `{A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)` |
| `distTo_eq_zero_iff` | t94A02 | `{S : Set ℝ} (hS : IsClosed S) (x : ℝ) :` |
| `distTo_nonneg` | t94A02 | `(S : Set ℝ) (x : ℝ) : 0 ≤ distTo S x := by` |
| `distribution_polynomial_decay` | a01A06 | `{g : ℝ → ℝ} {A : ℝ} (hg : OrliczBound g A) (hA : 0 < A) :` |
| `dominant_ne_zero_on_sphere` | LIB:ConstructionTargets.Rouche | `{f g : ℂ → ℂ} {c : ℂ} {R : ℝ}` |
| `doubly_periodic_entire_is_const` | a93J05 | `(f : ℂ → ℂ)` |
| `dyadicRadius_add` | a01J06 | `(m n : ℕ) :` |
| `dyadicRadius_ge_one` | a01J06 | `(m : ℕ) : 1 ≤ dyadicRadius m := by` |
| `dyadicRadius_mono` | a01J06 | `{m n : ℕ} (h : m ≤ n) :` |
| `dyadicRadius_nonneg` | a01J06 | `(m : ℕ) : 0 ≤ dyadicRadius m :=` |
| `dyadicRadius_pos` | a01J06 | `(m : ℕ) : 0 < dyadicRadius m := by` |
| `dyadicRadius_succ_succ` | a01J06 | `(m : ℕ) :` |
| `dyadicShell_bound_using_constant` | a01J06 | `(data : ProblemData)` |
| `dyadicShell_cast_nonneg` | a01J06 | `(data : ProblemData) (m : ℕ) :` |
| `dyadicShell_le_upper` | a01J06 | `(data : ProblemData) (m : ℕ) :` |
| `dyadicShell_linear_bound` | a01J06 | `(data : ProblemData)` |
| `dyadicShell_linear_bound_of_zeroCountLinear` | a01J06 | `(data : ProblemData) (m : ℕ)` |
| `dyadic_integral_eq` | a95A04 | `{f : ℝ → ℝ}` |
| `eLpNorm_indicator_rpow_eq` | a02J02 | `{α : Type*} [MeasurableSpace α] {μ : Measure α}` |
| `eLpNorm_tendsto_top` | a00J01 | `{f : ℝ → ℝ}` |
| `eLpNorm_top_eq_essSup` | a93J04 | `{α : Type*} {E : Type*} [NormedAddCommGroup E]` |
| `eLpNorm_translation_tendsto` | LIB:ConstructionTargets.L2Translation | `(f : ℝ → ℝ) (hf : MemLp f 2 volume) :` |
| `eLpNorm_translation_tendsto` | LIB:ConstructionTargets.L2Translation | `{p : ENNReal} (hp : 1 ≤ p) (hp' : p ≠ ⊤)` |
| `eVariationOn_intervalIntegral_le_integral_norm` | a93A04 | `{g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)` |
| `entire_avoids_ray_const` | a92J07 | `{f : ℂ → ℂ}` |
| `entire_coeffs_tendsto_zero` | a96A06 | `(g : ℂ → ℂ) (hg : Differentiable ℂ g) :` |
| `entire_lower_bound_is_monomial` | a95J02 | `{f : ℂ → ℂ} {lam : ℝ} (hlam : 0 < lam)` |
| `eqOn_deriv_mul` | LIB:ConstructionTargets.SchwarzEquality | `{h : ℂ → ℂ}` |
| `eq_const_of_norm_le_rpow_half` | a94J08 | `(q : ℂ → ℂ) (hq_diff : Differentiable ℂ q)` |
| `eq_deriv_mul` | LIB:ConstructionTargets.SchwarzEquality | `{h : ℂ → ℂ}` |
| `eq_zero_of_vanishing_on_upper_arc` | a95A05 | `{f : ℂ → ℂ}` |
| `eq_zero_on_closure_of_frontier_zero` | a95A05 | `{g : ℂ → ℂ}` |
| `eval_bound_outside` | a99J07 | `(p : Polynomial ℂ) {w : ℂ}` |
| `evenCoefficients_radius_pos` | a96J10 | `(p : FormalMultilinearSeries ℂ ℂ ℂ) (hp : 0 < p.radius) :` |
| `evenCoefficients_sum` | a96J10 | `(h : ℂ → ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)` |
| `evenFactorRoot_sq` | a96J10 | `(w : ℂ) : evenFactorRoot w ^ 2 = w := by` |
| `evenFactorRoot_tendsto` | a96J10 | `:` |
| `even_ball_volume` | a01A04 | `(k : ℕ) (hk : 0 < k) :` |
| `even_ball_volume_exact` | a01A04 | `(k : ℕ) (hk : 0 < k) :` |
| `eventually_le_norm_of_weak` | a93A03 | `{h : ℕ → H} {x : H} (hweak : WeakTendsto h x) :` |
| `exists_ac_strictly_mono_deriv_zero_pos_measure` | a94J02 | `:` |
| `exists_closedBall_subset_of_mem_open` | a01A07 | `{U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U) :` |
| `exists_factorization_of_order_ge_two` | a94A10 | `(f : ℂ → ℂ) (x₀ : ℂ) (hf : Differentiable ℂ f)` |
| `exists_fat_cantor` | a94J02 | `:` |
| `exists_local_normal_form_of_deriv_eq_zero` | LIB:ConstructionTargets.UnivalentDeriv | `{U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}` |
| `exists_nonreal_preimage_of_real` | a94A10 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f)` |
| `exists_not_mem_of_dense_compl` | a95A01 | `(K : Set ℝ) (hK_int : interior K = ∅)` |
| `exists_pole_on_boundary` | a95J04 | `{D : Set ℂ} (hD : IsOpen D) (hD_contains : closedBall (0 : ℂ) 1 ⊆ D)` |
| `exists_pos_measure_bounded_subset` | a96J02 | `(A : Set ℝ) (hA : MeasurableSet A)` |
| `exists_radialLaverage_bound_of_memLp` | LIB:ConstructionTargets.RadialMajorantAE | `{f : ℝ → ℝ}` |
| `exists_rat_Icc_subset_of_mem_open` | a95J06 | `{U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U) :` |
| `exists_root_in_bounded_isOpen_sublevel_frontier_lemniscate` | LIB:ConstructionTargets.LemniscateComponents | `{U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ sublevel p)` |
| `exists_root_in_bounded_isOpen_sublevel_frontier_lemniscate` | a00J04 | `{U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ sublevel p)` |
| `exists_root_in_bounded_isOpen_sublevel_frontier_lemniscate` | a01A08 | `{U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ sublevel p)` |
| `exists_root_in_componentSet_of_subset_sublevel` | LIB:ConstructionTargets.LemniscateComponents | `(hp : 0 < p.natDegree) (x : ↥((lemniscate p)ᶜ))` |
| `exists_root_in_componentSet_of_subset_sublevel` | a00J04 | `(hp : 0 < p.natDegree) (x : ↥((lemniscate p)ᶜ))` |
| `exists_root_in_componentSet_of_subset_sublevel` | a01A08 | `(hp : 0 < p.natDegree) (x : ↥((lemniscate p)ᶜ))` |
| `exists_rotation` | LIB:ConstructionTargets.SchwarzEquality | `{h : ℂ → ℂ}` |
| `exists_spike` | a96A02 | `(x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :` |
| `exists_spikeWidth_lt` | a01J01 | `{δ : ℝ} (hδ : 0 < δ) :` |
| `exists_tendsto_integral_fresnel` | a01A10 | `:` |
| `exists_tendsto_integral_sinc` | LIB:ConstructionTargets.Sinc | `:` |
| `exists_tendsto_symmetric_integral_sinc` | LIB:ConstructionTargets.Sinc | `:` |
| `exists_unit_mul` | LIB:ConstructionTargets.SchwarzEquality | `{h : ℂ → ℂ}` |
| `exists_zeroFree_factorization_on_closedBall` | LIB:ConstructionTargets.Rouche | `{f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)` |
| `exp_two_pi_mul_sub_ne_zero_of_norm_lt_one` | a96J10 | `{z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :` |
| `exponential_decay_implies_L2` | a01A06 | `{g : ℝ → ℝ} (hg_meas : Measurable g)` |
| `extend_uniformContinuous_dense` | m99A04 | `{A : Set X} (hA : Dense A) {f : A → Y}` |
| `extension_deriv_eq_lacunary_deriv_series` | a95A06 | `{F : ℂ → ℂ} {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1)` |
| `extension_deriv_eventually_bounded` | a95A06 | `{U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U)` |
| `exterior_pathConnected` | LIB:ConstructionTargets.LemniscateComponents | `(R : ℝ) (hR : 0 ≤ R) :` |
| `exterior_pathConnected` | a00J04 | `(R : ℝ) (hR : 0 ≤ R) :` |
| `exterior_pathConnected` | a01A08 | `(R : ℝ) (hR : 0 ≤ R) :` |
| `f_continuous` | a96J01 | `(n : ℕ) : Continuous (f n) := by` |
| `f_eq_pf` | a96A08 | `(x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :` |
| `f_eq_zero_of_ne` | a96J01 | `{n m : ℕ} {x : ℝ} (hmn : m ≠ n) (hn : 0 < f n x) : f m x = 0 := by` |
| `f_le` | a96J01 | `(n : ℕ) (x : ℝ) : f n x ≤ 1 / ((n + 1 : ℕ) : ℝ) := by` |
| `f_mid` | a96J01 | `(n : ℕ) : f n (mid n) = 1 / ((n + 1 : ℕ) : ℝ) := by` |
| `f_nonneg` | a96J01 | `(n : ℕ) (x : ℝ) : 0 ≤ f n x := by` |
| `f_nonzero_unique` | a96J01 | `{n : ℕ} {x : ℝ} (hn : f n x ≠ 0) : ∀ m, m ≠ n → f m x = 0 := by` |
| `f_poly_exp_deriv_ne_zero` | a94J07 | `{z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :` |
| `f_poly_exp_injective_on_disk` | a94J07 | `:` |
| `f_pos_imp` | a96J01 | `(n : ℕ) {x : ℝ} (hfx : 0 < f n x) : a n < x ∧ x < b n := by` |
| `f_radial_conv_L2_bound` | a95A03 | `{g : E → ℝ}` |
| `f_radial_eq_of_ne_zero` | a95A03 | `(x : E) (hx : x ≠ 0) :` |
| `f_radial_integrable` | a95A03 | `:` |
| `f_radial_integral` | a95A03 | `:` |
| `f_radial_memLp_iff` | a95A03 | `{p : ℝ} (hp : 0 < p) :` |
| `f_radial_not_memLp_top` | a95A03 | `:` |
| `f_summable` | a96J01 | `(x : ℝ) : Summable (fun n => f n x) := by` |
| `f_tail_le` | a96J01 | `(N : ℕ) (x : ℝ) :` |
| `f_unique_pos` | a96J01 | `{n m : ℕ} {x : ℝ} (hn : 0 < f n x) (hm : 0 < f m x) : n = m := by` |
| `f_zero_eq_zero` | a95J02 | `{f : ℂ → ℂ} {lam : ℝ} (hlam : 0 < lam)` |
| `factorial_dvd_of_le` | a95A06 | `{n q : ℕ} (hq : 0 < q) (hn : q ≤ n) :` |
| `false_of_affine_factorization` | a94A10 | `(f : ℂ → ℂ) (hreal : RealIffReal f)` |
| `false_of_entire_nonvanishing_lower_bound` | a94J08 | `(f : ℂ → ℂ) (hf_diff : Differentiable ℂ f) (hf_ne : ∀ z, f z ≠ 0)` |
| `finrank_E_eq_three` | a95A03 | `:` |
| `five_cycle_transposition_generate` | b96J01 | `(G : Subgroup (Equiv.Perm (Fin 5)))` |
| `for` | LIB:ConstructionTargets.LpRepresentative | ``Lᵖ` representatives and applies on infinite-measure spaces where` |
| `for` | m00A05 | `a globally Lipschitz autonomous vector field. Completing this` |
| `for` | m98J04 | `endpoint-zero `C¹` test variations. I searched Mathlib's` |
| `fourierTransform_continuous` | a92J03 | `{f : ℝ → ℂ} (hf : Integrable f volume) :` |
| `fourierTransform_norm_le` | a92J03 | `{f : ℝ → ℂ} (hf : Integrable f volume) (ξ : ℝ) :` |
| `fourierTransform_tendsto_zero` | a92J03 | `{f : ℝ → ℂ} (hf : Integrable f volume) :` |
| `fourier_maps_L1_to_C0` | a92J03 | `{f : ℝ → ℂ} (hf : Integrable f volume) :` |
| `fourthRoot_not_mem_unitSegment` | a01A12 | `(η : ℂ)` |
| `fresnel_bochner_integral_eq_zero` | a01A10 | `:` |
| `fresnel_claimed_value_ne_zero` | a01A10 | `:` |
| `fresnel_integral` | a01A10 | `:` |
| `fresnel_integrand_not_integrable` | a01A10 | `:` |
| `fresnel_remainder_norm_eq` | a01A10 | `{x : ℝ} (hx : 0 < x) :` |
| `frontier_connectedComponentIn_subset_frontier` | LIB:ConstructionTargets.LemniscateComponents | `{α : Type*} [TopologicalSpace α] [LocallyConnectedSpace α]` |
| `ftc_a00j02` | a00J02 | `(f : ℝ → ℝ)` |
| `gamma_half_nat_lower` | a01A04 | `(k : ℕ) :` |
| `gaussConv_Lp_contraction` | a94A03 | `{p : ENNReal} (hp : 1 ≤ p) (hp' : p ≠ ⊤)` |
| `gaussConv_eq_integral_unitKernel` | a94A03 | `{t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) (x : ℝ) :` |
| `gaussConv_memLp` | a94A03 | `{p : ENNReal} (hp : 1 ≤ p) (hp' : p ≠ ⊤)` |
| `gaussConv_tendsto_Lp` | a94A03 | `{p : ENNReal} (hp : 1 ≤ p) (hp' : p ≠ ⊤)` |
| `gaussKernel_integrable` | a94A03 | `{t : ℝ} (ht : 0 < t) :` |
| `gaussKernel_integral_eq_one` | a94A03 | `{t : ℝ} (ht : 0 < t) :` |
| `gaussKernel_neg` | a94A03 | `(t x : ℝ) :` |
| `gaussKernel_nonneg` | a94A03 | `{t : ℝ} (ht : 0 < t) (x : ℝ) :` |
| `gaussKernel_scale` | a94A03 | `{t : ℝ} (ht : 0 < t) (x : ℝ) :` |
| `gaussian_fourier_transform` | a01A10 | `(y : ℝ) :` |
| `gaussian_translation_average_tendsto_Lp` | a94A03 | `{p : ENNReal} [Fact (1 ≤ p)] (hp' : p ≠ ⊤)` |
| `gaussian_translation_average_toLp` | a94A03 | `{p : ENNReal} [Fact (1 ≤ p)] (hp' : p ≠ ⊤)` |
| `geom_iteratedDeriv` | a96A06 | `(n : ℕ) :` |
| `geom_taylor_coeff` | a96A06 | `(n : ℕ) :` |
| `geometric_decay_tendsto_zero` | a01A05 | `:` |
| `geometric_mean_le_quasiNorm_of_integrable_log` | a96A01 | `{f : ℝ → ℝ}` |
| `gives` | a94J04 | ``‖P_y * f - f‖₂ → 0`. This uses L² translation continuity` |
| `grid_count_converges_to_measure` | a97J02 | `(A : Set ℝ)` |
| `hasDerivAt_G` | a94A06 | `(x : ℝ) : HasDerivAt G (x^7 / (1 + x^12)) x := by` |
| `hasDerivAt_H` | a94A06 | `(u : ℝ) (hu : 0 ≤ u) : HasDerivAt H (u / (1 + u^3)) u := by` |
| `hasDerivAt_argStar_comp` | a02J07 | `{γ : ℝ → ℂ} (hγ : SlitPath γ)` |
| `hasDerivAt_cauchyKernel` | a01A11 | `(t : ℝ) (z : ℂ) (hz : (t : ℂ) ≠ z) :` |
| `hasDerivAt_integral_iterate_heatKernel` | a96A04 | `{t : ℝ} (ht : 0 < t) (n : ℕ) {f : ℝ → ℝ}` |
| `hasDerivAt_integrand` | a00J05 | `(t : ℝ) (z₀ : ℂ) (hz : (t : ℂ) ≠ z₀) :` |
| `hasDerivAt_logStar` | a02J07 | `{z : ℂ} (hz : z ∈ posSlitPlane) :` |
| `hasDerivAt_logStar_comp` | a02J07 | `{γ : ℝ → ℂ} (hγ : SlitPath γ)` |
| `hasDerivAt_sub_mul_of_continuousAt` | a95J04 | `{f : ℂ → ℂ} {z : ℂ}` |
| `hasFiniteIntegral_indicator_lift` | LIB:ConstructionTargets.LpRepresentative | `{Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]` |
| `heatConv_L2_le` | a96A04 | `{t : ℝ} (ht : 0 < t)` |
| `heatConv_contDiff` | a96A04 | `{t : ℝ} (ht : 0 < t)` |
| `heatConv_eq_integral_translation` | a96A04 | `(t : ℝ) (f : ℝ → ℝ) (x : ℝ) :` |
| `heatConv_eq_integral_unitKernel` | a96A04 | `{t : ℝ} (ht : 0 < t)` |
| `heatConv_memLp` | a96A04 | `{t : ℝ} (ht : 0 < t)` |
| `heatConv_tendsto_L2` | a96A04 | `{f : ℝ → ℝ}` |
| `heatKernel_contDiff` | a96A04 | `{t : ℝ} (_ht : 0 < t) :` |
| `heatKernel_deriv` | a96A04 | `{t x : ℝ} (ht : 0 < t) :` |
| `heatKernel_deriv_integrable` | a96A04 | `{t : ℝ} (ht : 0 < t) :` |
| `heatKernel_deriv_memLp_two` | a96A04 | `{t : ℝ} (ht : 0 < t) :` |
| `heatKernel_deriv_mul_integrable` | a96A04 | `{t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : MemLp f 2 volume)` |
| `heatKernel_hasDerivAt` | a96A04 | `{t x : ℝ} (_ht : 0 < t) :` |
| `heatKernel_integrable` | a96A04 | `{t : ℝ} (ht : 0 < t) :` |
| `heatKernel_integral` | a96A04 | `{t : ℝ} (ht : 0 < t) :` |
| `heatKernel_iterate_deriv_eq_polynomial_gaussian` | a96A04 | `{t : ℝ} (_ht : 0 < t) (n : ℕ) (x : ℝ) :` |
| `heatKernel_iterate_deriv_local_envelope` | a96A04 | `{t : ℝ} (ht : 0 < t) (n : ℕ) (x₀ : ℝ)` |
| `heatKernel_iterate_deriv_memLp_two` | a96A04 | `{t : ℝ} (ht : 0 < t) (n : ℕ) :` |
| `heatKernel_iterate_deriv_polynomial_bound` | a96A04 | `{t : ℝ} (ht : 0 < t) (n : ℕ) :` |
| `heatKernel_memLp_two` | a96A04 | `{t : ℝ} (ht : 0 < t) :` |
| `heatKernel_nonneg` | a96A04 | `{t : ℝ} (ht : 0 < t) (x : ℝ) :` |
| `heatKernel_scale` | a96A04 | `{t : ℝ} (ht : 0 < t) (x : ℝ) :` |
| `heat_translation_average_tendsto_L2` | a96A04 | `{f : ℝ → ℝ} (hf : MemLp f 2 volume) :` |
| `heat_translation_average_toLp` | a96A04 | `{t : ℝ} (ht : 0 < t)` |
| `holder_from_sq` | a96A02 | `{z d : ℝ} (hz : 0 ≤ z) (_hd : 0 ≤ d)` |
| `holder_to_left` | a96A02 | `{f : ℝ → ℝ} (hf : SpikeFunctionSpec f)` |
| `holder_to_right` | a96A02 | `{f : ℝ → ℝ} (hf : SpikeFunctionSpec f)` |
| `holder_within_spike` | a96A02 | `{f : ℝ → ℝ} (hf : SpikeFunctionSpec f)` |
| `holo_on_larger_ball_implies_bounded` | a95J04 | `{f : ℂ → ℂ} {R : ℝ} (hR : 1 < R) (hf : DifferentiableOn ℂ f (ball 0 R)) :` |
| `homeomorph_of_compact_to_T2` | t92J02 | `{X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]` |
| `hurwitz_eventually_nonvanishing_on_sphere` | a93J07 | `{Ω : Set ℂ} (hΩ : IsOpen Ω)` |
| `hurwitz_zero_persistence` | a93J07 | `{Ω : Set ℂ} (hΩ : IsOpen Ω)` |
| `hw_eq` | a96J01 | `(n : ℕ) : hw n = (2 : ℝ)⁻¹ ^ (n + 2) := by` |
| `hw_pos` | a96J01 | `(n : ℕ) : 0 < hw n := by` |
| `iInter_nested_compact_nonempty` | t93J02 | `{C : ℕ → Set Y}` |
| `iUnion` | a95J06 | `{f : ℝ → ℝ} {s : ℕ → Set ℝ} (h : ∀ n, LusinConditionN f (s n)) :` |
| `iUnion_ordConnectedComponents_eq` | LIB:ConstructionTargets.LusinN | `{U : Set ℝ} :` |
| `iUnion_ordConnectedComponents_eq` | a95A02 | `{U : Set ℝ} :` |
| `im_apply_star_eq_neg` | LIB:ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f)` |
| `im_image_mul_pos_of_im_pos` | a94A10 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f) (hreal : RealIffReal f)` |
| `im_linear_growth_of_entire_pick` | LIB:ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f)` |
| `im_neg_of_im_neg` | LIB:ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f)` |
| `image_Icc_eq_Icc` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `image_of_compact_isCompact` | t92J02 | `{X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]` |
| `indicator_bound` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ)` |
| `indicator_case` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ) (hM : 0 < M)` |
| `indicator_not_riemann_integrable` | a95A01 | `(K : Set ℝ) (hK : IsCompact K) (hK_sub : K ⊆ Icc 0 1)` |
| `infDist_pos_of_not_mem_image` | a01A11 | `(hK' : IsCompact K) (hKne' : K.Nonempty) (z : ℂ) (hz : z ∉ ofReal '' K) :` |
| `inf_indicator_eq_zero` | a95A01 | `(K : Set ℝ) (hK_int : interior K = ∅)` |
| `inflate5_center` | a95J07 | `(α β : ℝ) (_hab : α < β) :` |
| `inflate5_length` | a95J07 | `(α β : ℝ) (_hab : α < β) :` |
| `injOn_disk_of_injOn_circle` | a96A07 | `{g : ℂ → ℂ}` |
| `inner_tendsto_zero` | a01A05 | `[CompleteSpace H]` |
| `inner_tendsto_zero_of_mem_closure_span` | a01A05 | `(seq : NearOrthogonalSeq H) {v : H}` |
| `inner_tendsto_zero_of_mem_span` | a01A05 | `(seq : NearOrthogonalSeq H) {v : H}` |
| `intCast_zeroCountInClosedBall` | LIB:ConstructionTargets.Rouche | `(f : ℂ → ℂ) (c : ℂ) (R : ℝ) :` |
| `integrableOn_exp_neg_mul_sinc_Ioi` | LIB:ConstructionTargets.Sinc | `{a : ℝ} (ha : 0 < a) :` |
| `integrable_convolution_at` | a03J03 | `{p q : ℝ} (hpq : p.HolderConjugate q)` |
| `integrable_damped_cos_prod` | LIB:ConstructionTargets.Sinc | `{a : ℝ} (ha : 0 < a) :` |
| `integrable_indicator_of_finite_measure` | a96J02 | `(s : Set ℝ) (hs : MeasurableSet s)` |
| `integrable_iterate_deriv_standardGaussian` | a96A04 | `(n : ℕ) :` |
| `integrable_kernel_smul_of_norm_le` | LIB:ConstructionTargets.KernelAverage | `{Y E : Type*} [MeasurableSpace Y] [NormedAddCommGroup E]` |
| `integrable_polynomial_mul_exp_neg_mul_sq` | a96A04 | `(p : Polynomial ℝ) {b : ℝ} (hb : 0 < b) :` |
| `integrable_posPart_log_norm` | a96A01 | `{f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 1) volume) :` |
| `integrable_pow_mul_exp_neg_mul_sq` | a96A04 | `(n : ℕ) {b : ℝ} (hb : 0 < b) :` |
| `integrable_radial_R3_iff` | LIB:ConstructionTargets.RadialIntegrationR3 | `{g : ℝ → ℝ} :` |
| `integral_abs_rpow_eq_eLpNorm_rpow` | a02J02 | `{α : Type*} [MeasurableSpace α] {μ : Measure α}` |
| `integral_arctan_tendsto_of_tendstoInMeasure` | a95J05 | `{f : ℕ → Ω → ℝ}` |
| `integral_closedBall_eq_area_smul` | a01A07 | `{g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)` |
| `integral_closedBall_eq_translate` | a01A07 | `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]` |
| `integral_closedBall_zero_eq_area_smul` | a01A07 | `{g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)` |
| `integral_closedBall_zero_eq_polar` | a01A07 | `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]` |
| `integral_cos_mul_eq_sinc` | LIB:ConstructionTargets.Sinc | `(x : ℝ) :` |
| `integral_eq_rational` | a94J06 | `{z : ℂ} :` |
| `integral_even_neg_to_pos` | a96A08 | `(S₁ : ℝ) (f : ℝ → ℝ) (heven : ∀ x, f (-x) = f x) :` |
| `integral_exp_neg_mul_cos_Ioi` | LIB:ConstructionTargets.Sinc | `{a : ℝ} (ha : 0 < a) (t : ℝ) :` |
| `integral_exp_neg_mul_sinc_Ioi` | LIB:ConstructionTargets.Sinc | `{a : ℝ} (ha : 0 < a) :` |
| `integral_form_on_sphere` | t92J09 | `:` |
| `integral_inv_one_plus_sq` | a95A03 | `:` |
| `integral_inv_one_plus_x` | a93J02 | `: ∫ x in (0:ℝ)..1, 1 / (1 + x) = log 2 := by` |
| `integral_inv_sq_half` | a01A10 | `{a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :` |
| `integral_inv_two_plus_cos` | a92J06 | `:` |
| `integral_le_bound_mul_measure` | a94J01 | `{f : (Fin n → ℝ) → ℝ} {M : ℝ} (hM : 0 ≤ M)` |
| `integral_norm_rpow_tendsto_measure_support` | a96A01 | `{f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 1) volume) :` |
| `integral_one_div_sq` | LIB:ConstructionTargets.Sinc | `{a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :` |
| `integral_partial_fractions` | a94J06 | `{z : ℂ} (hz0 : z ≠ 0) (hz1 : ‖z‖ ≠ 1) :` |
| `integral_poissonLayerWeight_Ioi` | LIB:ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) (t : ℝ) :` |
| `integral_sin_pi_div_sub_one` | a96A08 | `(R : ℝ) :` |
| `integral_sin_pi_div_subst` | a96A08 | `(R : ℝ) :` |
| `integral_sin_pow_even_doubleFactorial` | a01A04 | `(k : ℕ) :` |
| `integral_sin_pow_odd_doubleFactorial` | a01A04 | `(k : ℕ) :` |
| `integral_sinc_eq_cos_div_sub` | LIB:ConstructionTargets.Sinc | `{a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :` |
| `integral_spike` | a01J01 | `(n : ℕ) : ∫ t, spike n t = 1 := by` |
| `integral_sub_center_inv` | a94J06 | `:` |
| `integral_sub_inv_eq_zero` | a94J06 | `{w : ℂ} (hw : 1 < ‖w‖) :` |
| `integral_sub_inv_of_mem` | a94J06 | `{w : ℂ} (hw : ‖w‖ < 1) :` |
| `integral_translate_norm` | a95J08 | `{f : ℝ → ℝ} (hf : Integrable f volume) (y : ℝ) :` |
| `integral_univ_inv_one_plus_sq_eq` | a95A03 | `:` |
| `integral_x7_over_1_plus_x12` | a94A06 | `:` |
| `integral_zero_to_dyadic_eq` | a95A04 | `{f : ℝ → ℝ}` |
| `integral_zero_to_eq_mul` | a95A04 | `{f : ℝ → ℝ}` |
| `integrand_eq_rational` | a94J06 | `{ζ z : ℂ} (hζ : ‖ζ‖ = 1) (hne : ζ ≠ z) :` |
| `intervalIntegrable_sin_pi_div` | a96A08 | `(a b : ℝ) :` |
| `intervalIntegrable_sin_pi_div_sub_one` | a96A08 | `(a b : ℝ) :` |
| `intervalIntegral_zero_two_pi_eq_add_reflection` | LIB:ConstructionTargets.HerglotzRigidity | `(q : ℝ → ℝ) (hq : Continuous q) :` |
| `inv_le_one_of_le_one` | a94J08 | `{a : ℝ} (ha : 1 ≤ a) : a⁻¹ ≤ 1 := by` |
| `is` | m96A05 | `a three-support `Finset.univ` sum normal form, followed by the` |
| `isBounded_sublevel` | LIB:ConstructionTargets.LemniscateComponents | `(hp : 0 < p.natDegree) :` |
| `isBounded_sublevel` | a00J04 | `(hp : 0 < p.natDegree) :` |
| `isBounded_sublevel` | a01A08 | `(hp : 0 < p.natDegree) :` |
| `isClosed_closedUnitDisk` | a01J05 | `: IsClosed closedUnitDisk := by` |
| `isClosed_lemniscate` | LIB:ConstructionTargets.LemniscateComponents | `: IsClosed (lemniscate p) := by` |
| `isClosed_lemniscate` | a00J04 | `: IsClosed (lemniscate p) := by` |
| `isClosed_lemniscate` | a01A08 | `: IsClosed (lemniscate p) := by` |
| `isClosed_unitCircle` | a01J05 | `: IsClosed unitCircle := by` |
| `isCompact_closedUnitDisk` | a01J05 | `: IsCompact closedUnitDisk := by` |
| `isCompact_prod` | t91A03 | `(hX : IsCompact (univ : Set X)) (hY : IsCompact (univ : Set Y)) :` |
| `isCompact_unitCircle` | a01J05 | `: IsCompact unitCircle := by` |
| `isCompact_unit_sphere` | a95J04 | `: IsCompact (sphere (0 : ℂ) 1) :=` |
| `isOpen_ordConnectedComponent_of_isOpen` | LIB:ConstructionTargets.LusinN | `{U : Set ℝ} (hU : IsOpen U) (x : ℝ) :` |
| `isOpen_ordConnectedComponent_of_isOpen` | a95A02 | `{U : Set ℝ} (hU : IsOpen U) (x : ℝ) :` |
| `isPathConnected_univ_of_connected` | t94A05 | `(M : Type*) [TopologicalSpace M]` |
| `isPreconnected_subset_superlevel_or_sublevel` | LIB:ConstructionTargets.LemniscateComponents | `{S : Set ℂ} (hS : IsPreconnected S) (hSL : Disjoint S (lemniscate p)) :` |
| `isPreconnected_subset_superlevel_or_sublevel` | a00J04 | `{S : Set ℂ} (hS : IsPreconnected S) (hSL : Disjoint S (lemniscate p)) :` |
| `isPreconnected_subset_superlevel_or_sublevel` | a01A08 | `{S : Set ℂ} (hS : IsPreconnected S) (hSL : Disjoint S (lemniscate p)) :` |
| `iterate_deriv_heatConv_eq_integral` | a96A04 | `{t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : MemLp f 2 volume)` |
| `iteratedDeriv_inv_shift` | a01J04 | `(n : ℕ) :` |
| `jensen_exp_circle` | a95A08 | `{g : ℝ → ℝ} (hg_meas : AEStronglyMeasurable g (volume.restrict (Icc 0 (2 * π))))` |
| `lacunarySeries_continuousOn` | a95A06 | `:` |
| `lacunarySeries_differentiableOn` | a95A06 | `:` |
| `lacunarySeries_hasDerivAt_of_norm_lt_one` | a95A06 | `{z : ℂ} (hz : ‖z‖ < 1) :` |
| `lacunarySeries_has_disconnected_extension` | a95A06 | `:` |
| `lacunarySeries_natural_boundary` | a95A06 | `:` |
| `lacunaryTerm_continuousOn` | a95A06 | `(n : ℕ) :` |
| `lacunaryTerm_differentiableOn` | a95A06 | `(n : ℕ) :` |
| `lacunaryTerm_hasDerivAt` | a95A06 | `(n : ℕ) (z : ℂ) :` |
| `lacunary_majorant_summable` | a95A06 | `:` |
| `lacunary_term_bound` | a95A06 | `(n : ℕ) (z : ℂ)` |
| `ladderConnected_of_connected` | t94J01 | `(h : IsPreconnected (Set.univ : Set X)) :` |
| `ladderConnected_of_subsingleton` | t94J01 | `(X : Type*) [TopologicalSpace X] [Subsingleton X] :` |
| `laplace_deriv_bound_integrable` | a01A09 | `(data : LaplaceData) {a : ℝ} (ha : 0 < a) :` |
| `laplace_integrand_integrable` | a01A09 | `(data : LaplaceData) {z : ℂ}` |
| `laplace_transform_analytic` | a01A09 | `(data : LaplaceData) :` |
| `laplace_transform_entire_of_compact_support` | a01A09 | `(f : ℝ → ℂ) (hf : compactSupportOnHalfLine f) :` |
| `le_of_lt_of_interval` | a96J01 | `{n m : ℕ} (hnm : n < m) : b n ≤ a m := by` |
| `lebesgue_decomposition_answer` | a02J04 | `:` |
| `limit_ge_geometric_mean` | a96A01 | `{f : ℝ → ℝ}` |
| `linearBoundConstant_bound` | a01J06 | `(data : ProblemData)` |
| `linearBoundConstant_nonneg` | a01J06 | `(data : ProblemData)` |
| `linear_growth_of_entire_of_im_growth` | LIB:ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f) {C : ℝ} (hC : 0 ≤ C)` |
| `linear_growth_of_entire_pick` | LIB:ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f)` |
| `lintegral_eq_ofReal_mul_lintegral_comp_mul` | LIB:ConstructionTargets.RadialMajorantAE | `{F : ℝ → ℝ≥0∞} (hF : Measurable F) {y : ℝ} (hy : 0 < y) :` |
| `lintegral_mul_le_lintegral_rpow` | LIB:ConstructionTargets.YoungConvolution | `{α : Type*} [MeasurableSpace α] {μ : Measure α}` |
| `lintegral_mul_radial_layerCake` | LIB:ConstructionTargets.RadialMajorantAE | `{g w φ : ℝ → ℝ≥0∞} (hg : Measurable g) (hw : Measurable w)` |
| `lintegral_poissonKernel_mul_enorm_sub_eq_radialLaverage` | LIB:ConstructionTargets.RadialMajorantAE | `{f : ℝ → ℝ} (hfm : Measurable f) (x : ℝ) {y : ℝ} (hy : 0 < y) :` |
| `lintegral_poissonLayerWeight_Ici` | LIB:ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) (t : ℝ) :` |
| `liouville_bounded` | a94J05 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f)` |
| `liouville_re_bounded_below` | a94J05 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f)` |
| `lipschitz_V_limit_implies_ac` | a93A04 | `{f : ℝ → ℝ} {fₙ : ℕ → ℝ → ℝ}` |
| `lipschitz_implies_ac` | a93A04 | `{f : ℝ → ℝ} (h : LipschitzOn01 f) :` |
| `locallyUniformLimit_injective_or_constant` | a93J07 | `{Ω : Set ℂ} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)` |
| `logDeriv_factorizedRational_eq_finsum` | LIB:ConstructionTargets.Rouche | `{U : Set ℂ} (D : Function.locallyFinsuppWithin U ℤ)` |
| `logIntegral_im_bounds` | a02J07 | `{γ : ℝ → ℂ} (hγ : SlitPath γ) :` |
| `logIntegral_im_eq_argStar_diff` | a02J07 | `{γ : ℝ → ℂ} (hγ : SlitPath γ) :` |
| `logStar_im` | a02J07 | `(z : ℂ) : (logStar z).im = argStar z := rfl` |
| `lowerQuantile_maps` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `lowerQuantile_mem` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `lowerQuantile_mono` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (hy₂ : y₂ ≤ f 1) :` |
| `lower_bound` | a00J01 | `{f : ℝ → ℝ}` |
| `lp_prod_complete` | a96J05 | `{α : Type*} {E : Type*} {m : MeasurableSpace α}` |
| `m95A01_left_residual` | m95A01 | `{𝕜 X : Type*}` |
| `m95A01_right_residual` | m95A01 | `{𝕜 X : Type*}` |
| `m95A02MaxDist_self` | m95A02 | `(f : m95A02H) : m95A02MaxDist f f = 0 := by` |
| `m95A02Value_zero` | m95A02 | `(x : ℝ) : m95A02Value (0 : m95A02H) x = 0 := by` |
| `m96A01_eigenspace_eq_ker` | m96A01 | `{X : Type*} [NormedAddCommGroup X]` |
| `m99A02Function_pos` | m99A02 | `{x : m99A02Point}` |
| `m99A02_neg_log_norm_pos` | m99A02 | `{x : m99A02Point}` |
| `m99A03Shift_cube` | m99A03 | `: m99A03Shift ^ 3 = 0 := by` |
| `m99A03Shift_sq_apply` | m99A03 | `(x : m99A03ExampleSpace) :` |
| `m99A06_selfConvolution_integrable` | m99A06 | `{f : ℝ → ℝ}` |
| `m99A06_sin_mul_selfConvolution_integrable` | m99A06 | `{f : ℝ → ℝ}` |
| `maps_upper_halfPlane_one_side` | a94A10 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f) (hreal : RealIffReal f) :` |
| `measurableSet_cauchySet` | a97A04 | `{f : ℕ → α → ℝ} (hf : ∀ n, Measurable fun x => f n x)` |
| `measurableSet_convergenceSet` | a97A04 | `{f : ℕ → α → ℝ}` |
| `measurable_ballSlice` | a01A04 | `: Measurable ballSlice := by` |
| `measurable_function_ae_eq_borel` | a01J02 | `{f : Set.Icc (0 : ℝ) 1 → ℝ}` |
| `measurable_quantile` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) :` |
| `measurable_set_ae_eq_borel` | a01J02 | `{A : Set ℝ} (hA : NullMeasurableSet A volume) :` |
| `measurable_subset_Icc_eq_sigmaCompact_union_null` | LIB:ConstructionTargets.LusinN | `{E : Set ℝ} (hE_meas : MeasurableSet E) (hE_sub : E ⊆ Icc (0:ℝ) 1) :` |
| `measurable_subset_Icc_eq_sigmaCompact_union_null` | a95A02 | `{E : Set ℝ} (hE_meas : MeasurableSet E) (hE_sub : E ⊆ Icc (0:ℝ) 1) :` |
| `measurable_sum_contains_interval` | a96J02 | `(A B : Set ℝ) (hA : MeasurableSet A)` |
| `measure_image_criticalSet_eq_zero` | a95J07 | `{f : ℝ → ℝ} :` |
| `measure_image_critical_set_eq_zero` | a94A05 | `(I : Set ℝ) (hI : IsOpen I)` |
| `measure_symmDiff_eq_zero` | a01J02 | `{A B : Set ℝ}` |
| `memLp_limit_of_ae_tendsto_bounded` | a96A03 | `{f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}` |
| `memLp_radial_R3_iff` | LIB:ConstructionTargets.RadialIntegrationR3 | `{g : ℝ → ℝ} {p : ℝ≥0∞}` |
| `memLp_two_iterate_deriv_standardGaussian` | a96A04 | `(n : ℕ) :` |
| `memLp_two_polynomial_abs_add_one_gaussian` | a96A04 | `(p : Polynomial ℝ) {b : ℝ} (hb : 0 < b) :` |
| `mem_posSlitPlane_iff` | a02J07 | `{z : ℂ} :` |
| `mem_zeroSet` | a01J05 | `{f : ℂ → ℂ} {z : ℂ} :` |
| `mid_add_hw` | a96J01 | `(n : ℕ) : mid n + hw n = b n := by` |
| `mid_le_b` | a96J01 | `(n : ℕ) : mid n ≤ b n := by` |
| `mid_mem` | a96J01 | `(n : ℕ) : mid n ∈ Set.Icc (0:ℝ) 1 := by` |
| `mid_sub_hw` | a96J01 | `(n : ℕ) : mid n - hw n = a n := by` |
| `mono` | a95J06 | `{f : ℝ → ℝ} {s t : Set ℝ} (h : LusinConditionN f s) (hts : t ⊆ s) :` |
| `monotoneExtension_eq_self` | LIB:ConstructionTargets.BanachZarecki | `(f : ℝ → ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :` |
| `monotone_clamp01` | LIB:ConstructionTargets.BanachZarecki | `: Monotone clamp01 := by` |
| `monotone_image_Icc` | a96J04 | `(f : ℝ → ℝ) (hf : MonotoneOn f (Icc 0 1))` |
| `monotone_image_interval` | a96J04 | `(f : ℝ → ℝ) (hf : MonotoneOn f (Icc 0 1))` |
| `monotone_monotoneExtension` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ}` |
| `monotone_of_homeomorphism` | a95J06 | `{f : ℝ → ℝ}` |
| `monotone_of_homeomorphism_fixing_cantor` | a95J06 | `{f : ℝ → ℝ}` |
| `monotone_quantile` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) :` |
| `nat_tsum_decomp` | a03J01 | `(n : ℕ) :` |
| `neg_alpha_nonpos` | a01J06 | `(data : ProblemData) : (-data.α) ≤ 0 :=` |
| `neg_mem_slitPlane_of_posSlitPlane` | a02J07 | `{z : ℂ} (hz : z ∈ posSlitPlane) :` |
| `no_entire_lower_bound_three_halves` | a94J08 | `:` |
| `nonconstant_of_realIffReal` | a94A10 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f) (hreal : RealIffReal f) :` |
| `nonempty_nested_inter` | t91J04 | `{a b : ℕ → ℝ}` |
| `nonzero_of_lower_bound` | a94J08 | `(f : ℂ → ℂ)` |
| `norm_comp_eq` | a00J03 | `{φ : X → X} (hφ : MeasurePreserving φ μ μ)` |
| `norm_damped_fresnel_le_one` | a01A10 | `{ε x : ℝ} (hε : 0 ≤ ε) :` |
| `norm_eval_le_supNormUnitDisk` | a99J07 | `(p : Polynomial ℂ) {z : ℂ}` |
| `norm_exp_le_e` | a94J07 | `{z : ℂ} (hz : ‖z‖ ≤ 1) : ‖cexp z‖ ≤ Real.exp 1 := by` |
| `norm_finset_prod_eq_one` | a01J05 | `{ι : Type*} :` |
| `norm_integral_Ioi_damped_fresnel_le_inv` | a01A10 | `{ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :` |
| `norm_integral_damped_fresnel_le_inv` | a01A10 | `{ε a b : ℝ} (hε : 0 ≤ ε) (ha : 0 < a) (hab : a ≤ b) :` |
| `norm_integral_fresnel_le_inv` | a01A10 | `{a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :` |
| `norm_integral_kernel_smul_le` | LIB:ConstructionTargets.KernelAverage | `{Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]` |
| `norm_inv_le_one_of_lower_bound` | a94J08 | `(f : ℂ → ℂ) (hf_ne : ∀ z, f z ≠ 0)` |
| `norm_le_area_integral_div_area` | a01A07 | `{g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)` |
| `norm_le_area_integral_div_area_of_integral_eq` | a01A07 | `{g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)` |
| `norm_le_circleAverage_norm` | a01A07 | `{g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)` |
| `norm_le_liminf_of_weak` | a93A03 | `[CompleteSpace H]` |
| `norm_pow_of_norm_one` | a92J05 | `(z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) : ‖z ^ n‖ = 1 := by` |
| `norm_quadraticQuotient_le` | a94J08 | `(f : ℂ → ℂ)` |
| `norm_smul_pow_of_norm_one` | a92J05 | `(z : ℂ) (hz : ‖z‖ = 1) (c : ℂ) (n : ℕ) :` |
| `norm_spike` | a01J01 | `(n : ℕ) (x : ℝ) : ‖spike n x‖ = spike n x := by` |
| `norm_sub_le_area_integral_div_area` | a01A07 | `{g : ℂ → ℂ} {z₀ c : ℂ} {r : ℝ} (hr : 0 < r)` |
| `norm_sub_tendsto_zero_of_weak_and_norm` | a93A03 | `{h : ℕ → H} {x : H}` |
| `normalizedQuotient_differentiable` | a95J02 | `{f g : ℂ → ℂ} {n : ℕ}` |
| `not_bounded_isOpen_superlevel_frontier_lemniscate` | LIB:ConstructionTargets.LemniscateComponents | `{U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ superlevel p)` |
| `not_bounded_isOpen_superlevel_frontier_lemniscate` | a00J04 | `{U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ superlevel p)` |
| `not_bounded_isOpen_superlevel_frontier_lemniscate` | a01A08 | `{U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ superlevel p)` |
| `not_fresnel_integral_statement` | a01A10 | `:` |
| `not_isBounded_componentSet_of_subset_superlevel` | LIB:ConstructionTargets.LemniscateComponents | `(x : ↥((lemniscate p)ᶜ)) (hsuper : componentSet x ⊆ superlevel p) :` |
| `not_isBounded_componentSet_of_subset_superlevel` | a00J04 | `(x : ↥((lemniscate p)ᶜ)) (hsuper : componentSet x ⊆ superlevel p) :` |
| `not_isBounded_componentSet_of_subset_superlevel` | a01A08 | `(x : ↥((lemniscate p)ᶜ)) (hsuper : componentSet x ⊆ superlevel p) :` |
| `odd_ball_volume_exact` | a01A04 | `(k : ℕ) :` |
| `odd_ball_volume_le` | a01A04 | `(k : ℕ) :` |
| `ofReal_poissonLayerWeight_mul_radialLIntegral_scale` | LIB:ConstructionTargets.RadialMajorantAE | `(f : ℝ → ℝ) (x : ℝ) {y : ℝ} (hy : 0 < y) (u : ℝ) :` |
| `one_le_norm_damping` | a01A10 | `{ε : ℝ} (hε : 0 ≤ ε) :` |
| `one_le_of_uniform_bound` | a96A05 | `(P : Polynomial ℂ) {C : ℝ}` |
| `openComponentRat_injective` | a96J04 | `(U : Set ℝ) (hU : IsOpen U) :` |
| `openComponentRat_mem` | a96J04 | `(U : Set ℝ) (hU : IsOpen U) (c : ConnectedComponents U) :` |
| `openComponentSet_eq_Ioo` | a96J04 | `(U : Set ℝ) (hU : IsOpen U) (hUI : U ⊆ Ioo 0 1)` |
| `openComponentSet_eq_endpoints` | a96J04 | `(U : Set ℝ) (hU : IsOpen U) (hUI : U ⊆ Ioo 0 1)` |
| `openComponentSet_exists_rat` | a96J04 | `(U : Set ℝ) (hU : IsOpen U)` |
| `openComponentSet_injective` | a96J04 | `(U : Set ℝ) : Function.Injective (openComponentSet U) := by` |
| `openComponentSet_nonempty` | a96J04 | `(U : Set ℝ) (c : ConnectedComponents U) :` |
| `openComponentSet_open` | a96J04 | `(U : Set ℝ) (hU : IsOpen U) (c : ConnectedComponents U) :` |
| `openComponentSet_pairwiseDisjoint` | a96J04 | `(U : Set ℝ) :` |
| `openComponentSet_preconnected` | a96J04 | `(U : Set ℝ) (c : ConnectedComponents U) :` |
| `openComponentSet_subset` | a96J04 | `(U : Set ℝ) (c : ConnectedComponents U) :` |
| `openComponent_endpoints_mem_Icc` | a96J04 | `(U : Set ℝ) (hUI : U ⊆ Ioo 0 1)` |
| `openComponent_image_subset` | a96J04 | `(f : ℝ → ℝ) (hf : MonotoneOn f (Icc 0 1))` |
| `open_mem_unit_sphere_contains_rational_angle` | a95A06 | `{U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hzU : z ∈ U) (hz_norm : ‖z‖ = 1) :` |
| `or` | b98A03 | `proved sibling packages this chain. The statement appears sound.` |
| `ordConnectedSection_pairwiseDisjoint` | LIB:ConstructionTargets.LusinN | `(U : Set ℝ) :` |
| `ordConnectedSection_pairwiseDisjoint` | a95A02 | `(U : Set ℝ) :` |
| `order_ge_two_of_deriv_zero` | a94A10 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f)` |
| `orlicz_bound_not_implies_L2` | a01A06 | `:` |
| `orthogonal_isClosed` | m98J03 | `: IsClosed (Vperp : Set H) :=` |
| `orthogonal_to_polynomials` | a94A04 | `{f : ℝ → ℝ} {μ : Measure ℝ}` |
| `p_card_roots` | a92J05 | `: p.roots.card = 10 := by` |
| `p_monic` | a92J05 | `: p.Monic := by` |
| `p_natDegree` | a92J05 | `: p.natDegree = 10 := by` |
| `p_no_roots_on_circle` | a92J05 | `(z : ℂ) (hz : ‖z‖ = 1) : aeval z p ≠ 0 := by` |
| `partial_fractions` | a94J06 | `{ζ z : ℂ} (hζ : ζ ≠ 0) (hz : z ≠ 0) (hζz : ζ ≠ z) :` |
| `periodic_int_aux` | a93J05 | `{f : ℂ → ℂ} (ω : ℂ) (hper : ∀ z, f (z + ω) = f z) (z : ℂ) :` |
| `pid_isIntegrallyClosed` | b93J02 | `(R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :` |
| `pointwiseSum_monotone` | a01J03 | `(fns : ℕ → ℝ → ℝ) (hmono : ∀ n, Monotone (fns n))` |
| `poissonConv_L2_contraction` | a94J04 | `(y : ℝ) (hy : 0 < y)` |
| `poissonConv_aestronglyMeasurable` | a94J04 | `(y : ℝ) (hy : 0 < y) (f : ℝ → ℝ) (hfm : AEStronglyMeasurable f volume) :` |
| `poissonConv_eq_integral_translation` | a94J04 | `(y : ℝ) (f : ℝ → ℝ) (x : ℝ) :` |
| `poissonConv_eq_integral_unitKernel` | a94J04 | `{y : ℝ} (hy : 0 < y)` |
| `poissonConv_memLp` | a94J04 | `(y : ℝ) (hy : 0 < y) (f : ℝ → ℝ) (hf : MemLp f 2 volume) :` |
| `poissonConv_tendsto_L2` | a94J04 | `(f : ℝ → ℝ) (hf : MemLp f 2 volume)` |
| `poissonConv_tendsto_ae` | a94J04 | `(f : ℝ → ℝ) (hf : MemLp f 2 volume)` |
| `poissonConv_tendsto_ae_of_memLp` | LIB:ConstructionTargets.RadialMajorantAE | `{f : ℝ → ℝ} (hf : MemLp f 2 volume) :` |
| `poissonConv_tendsto_at_of_memLp` | LIB:ConstructionTargets.RadialMajorantAE | `{f : ℝ → ℝ} (hfm : Measurable f)` |
| `poissonKernel_dilation` | LIB:ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) (t : ℝ) :` |
| `poissonKernel_even` | LIB:ConstructionTargets.RadialMajorantAE | `(y t : ℝ) :` |
| `poissonKernel_hasDerivAt` | LIB:ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) (s : ℝ) :` |
| `poissonKernel_inner_nonneg` | a94J04 | `(y : ℝ) (hy : 0 < y) (x : ℝ) :` |
| `poissonKernel_integrable` | LIB:ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) :` |
| `poissonKernel_integrable` | a94J04 | `(y : ℝ) (hy : 0 < y) :` |
| `poissonKernel_integral` | LIB:ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) :` |
| `poissonKernel_integral_Ioo` | a94J04 | `(y : ℝ) (hy : 0 < y) (δ : ℝ) (hδ : 0 < δ) :` |
| `poissonKernel_integral_one` | a94J04 | `(y : ℝ) (hy : 0 < y) :` |
| `poissonKernel_nonneg` | LIB:ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) (t : ℝ) :` |
| `poissonKernel_nonneg` | a94J04 | `(y : ℝ) (hy : 0 < y) (x : ℝ) :` |
| `poissonKernel_one_abs_mono` | LIB:ConstructionTargets.RadialMajorantAE | `{s t : ℝ} (hst : |s| ≤ |t|) :` |
| `poissonKernel_one_antitoneOn` | LIB:ConstructionTargets.RadialMajorantAE | `:` |
| `poissonKernel_one_integral` | LIB:ConstructionTargets.RadialMajorantAE | `:` |
| `poissonKernel_scale` | a94J04 | `{y : ℝ} (hy : 0 < y) (z : ℝ) :` |
| `poissonKernel_sub_star` | LIB:ConstructionTargets.HerglotzRigidity | `{w z : ℂ} (hzw : ‖w‖ < ‖z‖) :` |
| `poissonKernel_sub_star_ge` | LIB:ConstructionTargets.HerglotzRigidity | `{R : ℝ} {w z : ℂ} (hR : 1 < R) (hz : ‖z‖ = R) (` |
| `poissonKernel_sub_star_le` | LIB:ConstructionTargets.HerglotzRigidity | `{R : ℝ} {w z : ℂ} (hR : 0 < R) (hz : ‖z‖ = R)` |
| `poissonKernel_tail_tendsto` | a94J04 | `(δ : ℝ) (hδ : 0 < δ) :` |
| `poissonKernel_tendsto_atTop` | LIB:ConstructionTargets.RadialMajorantAE | `{y : ℝ} (_hy : 0 < y) :` |
| `poissonLayerDensity_eq` | LIB:ConstructionTargets.RadialMajorantAE | `(u : ℝ) :` |
| `poissonLayerDensity_integrable` | LIB:ConstructionTargets.RadialMajorantAE | `:` |
| `poissonLayerDensity_lintegral_ne_top` | LIB:ConstructionTargets.RadialMajorantAE | `:` |
| `poissonLayerDensity_nonneg` | LIB:ConstructionTargets.RadialMajorantAE | `(u : ℝ) :` |
| `poissonLayerWeight_nonneg` | LIB:ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) {s : ℝ} (hs : 0 ≤ s) :` |
| `poissonLayerWeight_scale` | LIB:ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) (u : ℝ) :` |
| `poisson_translation_average_tendsto_L2` | a94J04 | `{f : ℝ → ℝ} (hf : MemLp f 2 volume) :` |
| `poisson_translation_average_toLp` | a94J04 | `{y : ℝ} (hy : 0 < y) {f : ℝ → ℝ} (hf : MemLp f 2 volume) :` |
| `polynomialAbsCoeff_coeff_nonneg` | a96A04 | `(p : Polynomial ℝ) (n : ℕ) :` |
| `polynomial_eval_mono_of_coeff_nonneg` | a96A04 | `{p : Polynomial ℝ} (hp : ∀ i, 0 ≤ p.coeff i)` |
| `polynomial_eval_nonneg_of_coeff_nonneg` | a96A04 | `{p : Polynomial ℝ} (hp : ∀ i, 0 ≤ p.coeff i) {x : ℝ} (hx : 0 ≤ x) :` |
| `polynomial_map_image_null` | a03J02 | `{n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)}` |
| `polynomial_supNorm_bound` | a99J07 | `(p : Polynomial ℂ) (w : ℂ) :` |
| `posSlitPlane_ne_zero` | a02J07 | `{z : ℂ} (hz : z ∈ posSlitPlane) : z ≠ 0 := by` |
| `pos_quad` | a94A06 | `(u : ℝ) : 0 < u^2 - u + 1 := by nlinarith [sq_nonneg (u - 1/2)]` |
| `positive_convolution_exists` | a96J02 | `(A B : Set ℝ) (hA : MeasurableSet A)` |
| `pow_half_pos` | a96J01 | `(n : ℕ) : 0 < (2 : ℝ)⁻¹ ^ n := by positivity` |
| `proj_idempotent` | m96J01 | `(V : ClosedSubmodule ℝ H) :` |
| `proj_isSelfAdjoint` | m96J01 | `(V : ClosedSubmodule ℝ H) : IsSelfAdjoint (proj V) := by` |
| `proj_linear` | m96J01 | `(V : ClosedSubmodule ℝ H) :` |
| `proj_norm_one` | m96J01 | `(V : ClosedSubmodule ℝ H)` |
| `projection_properties` | m96J01 | `(V : ClosedSubmodule ℝ H) (hV : (V : Submodule ℝ H) ≠ ⊥) :` |
| `quadraticQuotient_continuousAt_zero` | a94J08 | `(f : ℂ → ℂ)` |
| `quadraticQuotient_differentiable` | a94J08 | `(f : ℂ → ℂ) (hf_diff : Differentiable ℂ f)` |
| `quadratic_bound` | a02J06 | `(data : SchwarzData)` |
| `quadratic_factor` | a92J06 | `(z : ℂ) :` |
| `quantifies` | b97A01 | `over arbitrary finite groups of order 24, and its` |
| `quantileMeasure_Iic` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `quantileMeasure_Ioc` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `quantile_le_iff` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `quantile_maps` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `quantile_mem_Ioc_iff` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `quantile_mem_unit` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `quasiNorm_antitone` | a96A01 | `{f : ℝ → ℝ}` |
| `quasiNorm_eq_lpNorm` | a96A01 | `{f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 1) volume)` |
| `quasiNorm_tendsto_exists` | a96A01 | `{f : ℝ → ℝ}` |
| `quotient_complete` | a96J05 | `{M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]` |
| `radialLIntegral_eq_lintegral_closedBall` | LIB:ConstructionTargets.RadialMajorantAE | `(f : ℝ → ℝ) (x s : ℝ) :` |
| `radialLIntegral_measurable` | LIB:ConstructionTargets.RadialMajorantAE | `(f : ℝ → ℝ) (x : ℝ) :` |
| `radialLIntegral_monotone` | LIB:ConstructionTargets.RadialMajorantAE | `(f : ℝ → ℝ) (x : ℝ) :` |
| `radialLaverage_le_of_memLp` | LIB:ConstructionTargets.RadialMajorantAE | `{f : ℝ → ℝ} (hf : MemLp f 2 volume)` |
| `radialLaverage_measurable` | LIB:ConstructionTargets.RadialMajorantAE | `(f : ℝ → ℝ) (x : ℝ) :` |
| `radial_integral_R3` | LIB:ConstructionTargets.RadialIntegrationR3 | `{g : ℝ → ℝ}` |
| `radial_integral_R3` | a95A03 | `{g : ℝ → ℝ}` |
| `radius_gt_one_of_summable` | a00J06 | `(ha : ∀ n, 0 ≤ a n) {ε : ℝ} (he : 0 < ε)` |
| `radius_gt_one_of_summable_aux` | a00J06 | `(ha : ∀ n, 0 ≤ a n) {ε : ℝ} (he : 0 < ε)` |
| `radon_riesz` | a02J02 | `{p : ℝ} (hp1 : 1 < p)` |
| `range_inter_quantile_preimage_Iic` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `range_inter_quantile_preimage_Ioc` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `rational_angle_factorial_pow_eq_one` | a95A06 | `(θ : ℚ) {n : ℕ} (hn : θ.den ≤ n) :` |
| `residue_limit_statement` | a01J04 | `(g : ℂ → ℂ) (hg : Differentiable ℂ g)` |
| `reverse_bound_on_disk` | a99J07 | `(p : Polynomial ℂ) {z : ℂ}` |
| `reverse_eval` | a99J07 | `(p : Polynomial ℂ) {z : ℂ} (hz : z ≠ 0) :` |
| `reverse_norm_le_on_sphere` | a99J07 | `(p : Polynomial ℂ) {z : ℂ}` |
| `riemann_lebesgue_sandwich` | a95A01 | `(f : ℝ → ℝ)` |
| `rigidity` | a02J06 | `(data : SchwarzData) {w : ℂ}` |
| `rnDeriv_mul_density` | a02J04 | `(x : ℝ) (hx : x ∈ Ioc 0 1) :` |
| `roots_inside_add_outside` | a92J05 | `:` |
| `roots_outside_card_eq_of_inside_card_eq` | a92J05 | `(hinside : (p.roots.filter (fun z => ‖z‖ < 1)).card = 3) :` |
| `roots_outside_unit_disk` | a92J05 | `:` |
| `rotationCounterexample_deriv_zero` | a95A08 | `:` |
| `rotationCounterexample_differentiable` | a95A08 | `:` |
| `rotationCounterexample_not_rotation` | a95A08 | `:` |
| `rotationCounterexample_surj_ball` | a95A08 | `:` |
| `rotation_of_disk_subset_image` | a95A08 | `{f : ℂ → ℂ}` |
| `rotation_of_disk_subset_image_counterexample` | a95A08 | `:` |
| `rouche_condition` | a92J05 | `(z : ℂ) (hz : ‖z‖ = 1) : ‖aeval z h‖ < ‖aeval z g‖ := by` |
| `rouche_deriv_bound` | a94J07 | `{z : ℂ} (hz : ‖z‖ = 1) :` |
| `rouche_f_bound` | a94J07 | `{z : ℂ} (hz : ‖z‖ = 1) :` |
| `rouche_homotopy_analyticOnNhd` | LIB:ConstructionTargets.Rouche | `{f g : ℂ → ℂ} {s : Set ℂ}` |
| `rouche_homotopy_analyticOnNhd_and_ne_zero` | LIB:ConstructionTargets.Rouche | `{f g : ℂ → ℂ} {c : ℂ} {R : ℝ}` |
| `rouche_homotopy_ne_zero_on_circle` | a92J05 | `(t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (z : ℂ) (hz : ‖z‖ = 1) :` |
| `rouche_homotopy_ne_zero_on_sphere` | LIB:ConstructionTargets.Rouche | `{f g : ℂ → ℂ} {c : ℂ} {R : ℝ}` |
| `rpow_le_one_add` | a96A01 | `{t : ℝ} (ht : 0 ≤ t) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :` |
| `rpow_sub_le` | a02J02 | `{p : ℝ} (hp : 1 ≤ p) (a b : ℝ) :` |
| `rpow_sub_one_div_posPart_le` | a96A01 | `{t p : ℝ} (ht : 0 ≤ t) (hp : 0 < p) (hp1 : p ≤ 1) :` |
| `scaled_integral_vanishes` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ) (hM : 0 < M)` |
| `scaled_integral_vanishes_of_compact_continuous` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ) (hM : 0 < M)` |
| `scaled_integral_vanishes_of_compact_smooth` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ) (hM : 0 < M)` |
| `scaled_intervalIntegral_bound` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ)` |
| `scaled_intervalIntegral_bound_div` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)` |
| `scaled_setIntegral_bound` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ)` |
| `schur_fubini` | a02J01 | `(k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (u : (Fin d → ℝ) → ℝ)` |
| `schur_pointwise` | a02J01 | `(k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (u : (Fin d → ℝ) → ℝ)` |
| `schur_test` | a02J01 | `(k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)` |
| `schur_weight_integrable` | a02J01 | `(k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (u : (Fin d → ℝ) → ℝ)` |
| `schwarz_deriv_bound` | a95J01 | `{h : ℂ → ℂ}` |
| `schwarz_equality` | a95J01 | `{h : ℂ → ℂ}` |
| `schwarz_second_order_bound` | a93J06 | `{f : ℂ → ℂ}` |
| `second_deriv_bound` | a02J06 | `(data : SchwarzData) :` |
| `sepFun_den_ne_zero` | t94A02 | `{A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)` |
| `sepFun_eq_one_iff` | t94A02 | `{A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)` |
| `sepFun_eq_zero_iff` | t94A02 | `{A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)` |
| `sepFun_mem_Icc` | t94A02 | `{A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B)` |
| `separate_closed_sets` | t94A02 | `{A B : Set ℝ}` |
| `setIntegralCLM_apply` | LIB:ConstructionTargets.LpRepresentative | `{X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ENNReal}` |
| `sin_pi_div_x_even` | a96A08 | `(x : ℝ) :` |
| `sin_pi_shift` | a96A08 | `(u : ℝ) :` |
| `singular_at_one` | a00J06 | `(ha : ∀ n, 0 ≤ a n)` |
| `solves_of_weight_summable` | a01J06 | `{data : ProblemData}` |
| `solves_problem` | a02J06 | `(data : SchwarzData) :` |
| `spikeFunction_at_left` | a96A02 | `(n : ℕ) (hn : 0 < n) :` |
| `spikeFunction_holderWith` | a96A02 | `:` |
| `spikeFunction_not_absolutelyContinuous` | a96A02 | `:` |
| `spikeFunction_spec` | a96A02 | `: SpikeFunctionSpec spikeFunction := by` |
| `spikeIndex_at_left` | a96A02 | `(n : ℕ) (hn : 0 < n) :` |
| `spikeIndex_eq_of_mem_of_ne_left` | a96A02 | `(n : ℕ) (hn : 0 < n) (x : ℝ)` |
| `spikeMidpoint_mem` | a96A02 | `(n : ℕ) (hn : 0 < n) :` |
| `spikeWidth_le_one` | a01J01 | `(n : ℕ) : spikeWidth n ≤ 1 := by` |
| `spike_base_length` | a96A02 | `(n : ℕ) (hn : 0 < n) :` |
| `spike_height_slope_bound` | a96A02 | `(n : ℕ) (hn : 0 < n) :` |
| `spike_lipschitz` | a96A02 | `{f : ℝ → ℝ} (hf : SpikeFunctionSpec f)` |
| `spike_nonneg` | a01J01 | `(n : ℕ) (x : ℝ) : 0 ≤ spike n x := by` |
| `spike_value_bounds` | a96A02 | `{f : ℝ → ℝ} (hf : SpikeFunctionSpec f)` |
| `sq_integral_le` | a02J01 | `{α : Type*} [MeasurableSpace α]` |
| `sq_sqrt3` | a94A06 | `: (Real.sqrt 3 : ℝ)^2 = 3 := sq_sqrt (by norm_num)` |
| `sq_sqrt_three_complex` | a92J06 | `: (sqrt 3 : ℂ) ^ 2 = 3 := by` |
| `sqrt_three_gt_one` | a92J06 | `: 1 < sqrt 3 := by` |
| `starProjection_kills_perp` | m98J03 | `(x : H) (hx : x ∈ (Vperp : Set H)) : P x = 0 := by` |
| `starProjection_maps_onto` | m98J03 | `(x : H) (hx : x ∈ (V : Set H)) : P x = x := by` |
| `step1_inj` | a01A12 | `: Function.Injective (fun z : ℂ => -I * z) :=` |
| `step1_maps` | a01A12 | `(z : ℂ) (hz : 0 < z.im) : 0 < (-I * z).re := by` |
| `step2_diff` | a01A12 | `(w : ℂ) : DifferentiableAt ℂ (· ^ 2) w :=` |
| `step2_image` | a01A12 | `: MapsTo (· ^ 2 : ℂ → ℂ) {w | 0 < w.re} {ζ : ℂ | (0:ℝ) < ζ.re ∨ ζ.im ≠ 0} := by` |
| `step2_inj_RHP` | a01A12 | `: InjOn (· ^ 2 : ℂ → ℂ) {w | 0 < w.re} := by` |
| `step4_to_wedge` | a01A12 | `(η : ℂ) (hη : η ≠ 0 ∧ η.arg ≠ Real.pi) :` |
| `stieltjesFunction_monotoneExtension_eq` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `stieltjesMeasure_Iic` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `stieltjesMeasure_Ioc` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `stieltjesMeasure_Ioc_eq_volume_image_Icc` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `stieltjesMeasure_absolutelyContinuous_of_maps_null` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `stieltjesMeasure_compl_Icc` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `stieltjesMeasure_eq_quantileMeasure` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `stieltjesMeasure_isFinite` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `stieltjesMeasure_le_volume_image` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `stieltjesMeasure_singleton` | LIB:ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))` |
| `subgroup_eq_top_of_fiveCycle_and_swap` | b96J01 | `{G : Subgroup (Equiv.Perm (Fin 5))}` |
| `subordination_deriv_eq` | a95J01 | `{f g : ℂ → ℂ}` |
| `subordination_deriv_le` | a95J01 | `{f g : ℂ → ℂ}` |
| `subordination_deriv_le_of_deriv_ne_zero` | a95J01 | `{f g : ℂ → ℂ}` |
| `sumLinearMap_apply` | t96A03 | `(v : Fin 4 → ℤ) :` |
| `sumLinearMap_surjective` | t96A03 | `:` |
| `sumNorm_nonneg` | a96J05 | `{α : Type*} {E : Type*} {m : MeasurableSpace α}` |
| `sumNorm_set_nonempty` | a96J05 | `{α : Type*} {E : Type*} {m : MeasurableSpace α}` |
| `sumNorm_smul` | a96J05 | `{α : Type*} {E : Type*} {m : MeasurableSpace α}` |
| `sumNorm_triangle` | a96J05 | `{α : Type*} {E : Type*} {m : MeasurableSpace α}` |
| `sum_edist_le_eVariationOn_of_mem_disjWithin` | a93A04 | `{g : ℝ → ℝ} {n : ℕ} {I : ℕ → ℝ × ℝ}` |
| `sum_inv_sq_eq_pi_sq_div_six` | a95A07 | `:` |
| `sum_setIntegral_partition` | a95A01 | `(f : ℝ → ℝ) (n : ℕ) (t : Fin (n + 2) → ℝ)` |
| `sum_space_add_closed` | a96J05 | `{α : Type*} {E : Type*} {m : MeasurableSpace α}` |
| `sum_space_neg_closed` | a96J05 | `{α : Type*} {E : Type*} {m : MeasurableSpace α}` |
| `summable_inv_sq` | a95A07 | `:` |
| `summable_lacunaryTerm_of_mem_closedBall` | a95A06 | `{z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :` |
| `summable_lacunary_deriv_terms_of_norm_lt_one` | a95A06 | `{w : ℂ} (hw0 : 0 < ‖w‖) (hw1 : ‖w‖ < 1) :` |
| `summable_one_div_pow` | a92J01 | `{p : ℝ} (hp : 1 < p) :` |
| `sup_inv_sub_polynomial_ge_one` | a96A05 | `(P : Polynomial ℂ) :` |
| `surjOn_domain_of_injOn_circle` | a96A07 | `{g : ℂ → ℂ}` |
| `sym3_not_isCommutative` | b93J01 | `:` |
| `sym3_not_isCyclic` | b93J01 | `:` |
| `symmetric_split` | a95A04 | `{f : ℝ → ℝ}` |
| `tail_integral_tendsto_zero` | a94J01 | `{f : (Fin n → ℝ) → ℝ}` |
| `tauDensity_eq_zero_outside` | a02J04 | `(x : ℝ) (hx : x ∉ Icc (0:ℝ) 1) :` |
| `tau_supported_Icc` | a02J04 | `(A : Set ℝ) (hA : A ⊆ (Icc 0 1)ᶜ) (hmA : MeasurableSet A) :` |
| `taylor_coeffs_tend_to_one` | a96A06 | `{f : ℂ → ℂ}` |
| `tendstoInMeasure.convergesInMeasure` | a92J02 | `{f : ℕ → α → ℝ} {g : α → ℝ}` |
| `tendstoInMeasureZero_iff_tendstoInMeasure` | a95J05 | `{f : ℕ → Ω → ℝ} :` |
| `tendstoInMeasure_iff_integral_arctan` | a95J05 | `{f : ℕ → Ω → ℝ}` |
| `tendstoInMeasure_of_integral_arctan_tendsto` | a95J05 | `{f : ℕ → Ω → ℝ}` |
| `tendstoUniformlyOn_deriv_of_L1` | a01A07 | `{f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}` |
| `tendstoUniformlyOn_of_L1_on_disks` | a01A07 | `{f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}` |
| `tendsto_G_atTop` | a94A06 | `: Tendsto G atTop (nhds (Real.sqrt 3 * π / 24)) := by` |
| `tendsto_Lp_of_ae_tendsto_of_L2_bounded` | a93A02 | `{f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {μ : Measure ℝ}` |
| `tendsto_arctan_one_div_nhdsWithin` | LIB:ConstructionTargets.Sinc | `:` |
| `tendsto_argStar_nhdsGT_zero_or_two_pi` | a02J07 | `{γ : ℝ → ℂ} (hγ : SlitPath γ) :` |
| `tendsto_argStar_nhdsLT_one` | a02J07 | `{γ : ℝ → ℂ} (hγ : SlitPath γ) :` |
| `tendsto_bound_zero` | a02J03 | `(M c : ℝ) (hc : 0 < c) :` |
| `tendsto_damped_fresnel_closed_form` | a01A10 | `:` |
| `tendsto_eLpNorm_atTop` | a93J04 | `{α : Type*} [MeasurableSpace α] {f : α → ℝ} {μ : Measure α}` |
| `tendsto_eLpNorm_indicator_sub_iff_tendsto_measure_symmDiff` | a94A01 | `{Eₙ : ℕ → Set ℝ} {E : Set ℝ}` |
| `tendsto_gamma_nhdsGT_zero` | a02J07 | `{γ : ℝ → ℂ} (hγ : SlitPath γ) :` |
| `tendsto_gen_sin_pi_div` | a96A08 | `(S₁ S₂ : ℝ → ℝ)` |
| `tendsto_half_line_sin_pi_div` | a96A08 | `:` |
| `tendsto_integral_abs_sub_of_nonneg` | a02J02 | `{α : Type*} [MeasurableSpace α] {μ : Measure α}` |
| `tendsto_integral_damped_fresnel_interval` | a01A10 | `(a : ℝ) :` |
| `tendsto_integral_exp_neg_mul_sinc_nhdsWithin` | LIB:ConstructionTargets.Sinc | `{L : ℝ}` |
| `tendsto_integral_sinc_pi_div_two` | LIB:ConstructionTargets.Sinc | `:` |
| `tendsto_intervalIntegral_exp_neg_mul_sinc` | LIB:ConstructionTargets.Sinc | `{A : ℝ} (hA : 0 < A) :` |
| `tendsto_lintegral_poissonLayerDensity_mul` | LIB:ConstructionTargets.RadialMajorantAE | `{A : ℝ → ℝ≥0∞} (hA : Measurable A) {C : ℝ≥0∞} (hC : C ≠ ∞)` |
| `tendsto_measure_rpow_one_div` | a93J04 | `{m : ℝ≥0∞} (hm₀ : m ≠ 0) (hm_top : m ≠ ⊤) :` |
| `tendsto_monotoneExtension_atBot` | LIB:ConstructionTargets.BanachZarecki | `(f : ℝ → ℝ) :` |
| `tendsto_norm_reciprocal_zero` | a03J08 | `{α : Type*} {l : Filter α}` |
| `tendsto_norm_sub_atTop` | a03J08 | `{α : Type*} {l : Filter α}` |
| `tendsto_of_L1ConvergesOnDisks_at` | a01A07 | `{f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {U : Set ℂ}` |
| `tendsto_one_div_pow_atTop` | a03J06 | `(k : ℕ) :` |
| `tendsto_radialLaverage_mul` | LIB:ConstructionTargets.RadialMajorantAE | `{f : ℝ → ℝ} {x : ℝ}` |
| `tendsto_rpow_inv_nat_atTop` | a00J01 | `(t : ℝ) (ht : 0 < t) :` |
| `tendsto_scaled_primitive_bound_zero` | a02J03 | `(M : ℝ) :` |
| `tendsto_setIntegral_Icc_zero` | LIB:ConstructionTargets.SetIntegralPrimitive | `(g : ℝ → ℝ)` |
| `tendsto_setIntegral_Icc_zero` | a00J02 | `(g : ℝ → ℝ)` |
| `tendsto_setIntegral_of_indicator_limit` | a94A01 | `{Eₙ : ℕ → Set ℝ} {E : Set ℝ}` |
| `tendsto_sum_alternating_harmonic` | a93J02 | `:` |
| `tendsto_symm_sin_pi_div` | a96A08 | `:` |
| `tendsto_symmetric_f` | a96A08 | `:` |
| `test_function_admissible` | a01A06 | `{E : Set ℝ} (hE : MeasurableSet E) (hEsub : E ⊆ Icc (0 : ℝ) 1)` |
| `that` | a97J08 | `a simple closed curve bounds a unique bounded region.` |
| `that` | m00A02 | `two integral-power Poincaré expansions have identical` |
| `to` | t94J05 | `show that `f` misses a point, then stereographic projection and` |
| `toLp_integral_eq_integral` | LIB:ConstructionTargets.LpRepresentative | `{Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]` |
| `totally_bounded_complete_compact` | t95A03 | `(X : Type*) [PseudoMetricSpace X] [CompleteSpace X]` |
| `translation_symmDiff_tendsto_zero` | a96J02 | `(B : Set ℝ) (hB : MeasurableSet B)` |
| `tsum_alternating_harmonic_mul_pow` | a93J02 | `{x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :` |
| `tsum_inv_sq` | a95A07 | `:` |
| `tsum_volume_disjoint_le_one` | a95J07 | `{S : ℕ → Set ℝ}` |
| `two_le_analyticOrderAt_sub_self` | LIB:ConstructionTargets.UnivalentDeriv | `{g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z)` |
| `two_pole_contour_eval` | a96J07 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f)` |
| `two_pole_ml_bound_at_zero` | a96J07 | `(f : ℂ → ℂ) (M : ℝ) (hM : 0 ≤ M)` |
| `unconstrainedZerosCounterexample_not_summable` | a01J06 | `:` |
| `unconstrainedZerosCounterexample_weight` | a01J06 | `(n : ℕ) :` |
| `unconstrainedZerosCounterexample_zeroCountLinear` | a01J06 | `:` |
| `unifContOn01_bounded` | a93A01 | `{f : ℝ → ℝ} (hf : UnifContOn01 f) :` |
| `unifContOn01_imp` | a93A01 | `(f : ℝ → ℝ) (hf : UnifContOn01 f) :` |
| `unifCont_iff_diffQuot` | a93A01 | `(f : ℝ → ℝ) :` |
| `unifCont_implies_diffQuot` | a93A01 | `{f : ℝ → ℝ} (hf : UnifContOn01 f) :` |
| `unifIntegrable_of_L2_bounded` | a93A02 | `{f : ℕ → ℝ → ℝ} {μ : Measure ℝ}` |
| `uniformCauchySeqOn_closedBall_half` | a01A07 | `{f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {U : Set ℂ}` |
| `uniform_bound` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ)` |
| `uniform_small_set_of_L3_bound` | a01J01 | `(f : ℕ → ℝ → ℝ)` |
| `union` | a95J06 | `{f : ℝ → ℝ} {s t : Set ℝ}` |
| `unitCircle_subset_closedUnitDisk` | a01J05 | `:` |
| `unitParam_eq_circleIntegral` | LIB:ConstructionTargets.CircleParam | `(R : ℝ) (g : ℂ → ℂ)` |
| `upperSemicircle_weighted_integral_le` | LIB:ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f)` |
| `upper_bound` | a00J01 | `{f : ℝ → ℝ} {p : ℝ≥0∞}` |
| `vitali_covering_5` | a95J07 | `{A : Set (Set ℝ)}` |
| `vitali_covering_lemma_5` | a94A05 | `{ι : Type*} (t : Set ι)` |
| `volume_closedBall_toReal` | a01A07 | `{z₀ : ℂ} {r : ℝ} (hr : 0 < r) :` |
| `weakL2_implies_L1_bound` | a01A02 | `(f : α → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 < C)` |
| `weak_convergence_of_ae_tendsto_L2_bounded` | a96A03 | `{f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}` |
| `weight_le_one` | a01J06 | `(data : ProblemData) (n : ℕ) :` |
| `weight_nonneg` | a01J06 | `(data : ProblemData) (n : ℕ) :` |
| `weight_summable_of_solves` | a01J06 | `{data : ProblemData}` |
| `weight_summable_of_zeroCountLinear` | a01J06 | `(data : ProblemData) (h : data.zeroCountLinear) :` |
| `width_eq` | a96J01 | `(n : ℕ) : b n - a n = (2 : ℝ)⁻¹ ^ (n + 1) := by` |
| `winding_number_bounded` | a95J03 | `{a : ℤ → ℂ} {N : ℕ}` |
| `with` | m98A05 | `parameters and local uniqueness. The conversion from the` |
| `with` | m98J05 | `exact normalization, differentiation under two improper` |
| `young_convolution_inequality` | LIB:ConstructionTargets.YoungConvolution | `{f g : ℝ → ℝ}` |
| `young_convolution_inequality` | a95J08 | `{f g : ℝ → ℝ}` |
| `young_convolution_inequality_one` | LIB:ConstructionTargets.YoungConvolution | `{f g : ℝ → ℝ}` |
| `young_inequality_L1_L2` | a95A03 | `(φ : E → ℝ) (hφ : Integrable φ volume)` |
| `z1_norm_lt_one` | a92J06 | `: ‖((-2 : ℂ) + (sqrt 3 : ℂ))‖ < 1 := by` |
| `z2_norm_gt_one` | a92J06 | `: 1 < ‖((-2 : ℂ) - (sqrt 3 : ℂ))‖ := by` |
| `zeroCountInClosedBall_add_eq` | LIB:ConstructionTargets.Rouche | `{f g : ℂ → ℂ} {c : ℂ} {R : ℝ}` |
| `zeroCountInClosedBall_aeval_eq_card_filter` | a92J05 | `(q : ℂ[X]) (hq : q.Monic) (c : ℂ) (R : ℝ) :` |
| `zeroCountInClosedBall_aeval_eq_card_filter` | a97A08 | `(q : ℂ[X]) (hq : q.Monic) (c : ℂ) (R : ℝ) :` |
| `zeroCountLinear_of_expBound` | a01J06 | `(data : ProblemData) :` |
| `zeroCountLinear_trivial` | a01J06 | `(data : ProblemData) : data.zeroCountLinear := by` |
| `zeroCount_congr` | a01J05 | `{f g : ℂ → ℂ}` |
| `zeroCount_eq_zero_of_nonvanishing` | a01J05 | `{f : ℂ → ℂ}` |
| `zeroCount_linear_at_dyadic` | a01J06 | `(data : ProblemData)` |
| `zeroFinset_congr` | a01J05 | `{f g : ℂ → ℂ}` |
| `zeroFinset_subset_closedUnitDisk` | a01J05 | `(f : ℂ → ℂ)` |
| `zeroSet_congr` | a01J05 | `{f g : ℂ → ℂ}` |
| `zeroSet_eq_empty_of_nonvanishing` | a01J05 | `{f : ℂ → ℂ}` |
| `zeroSet_finite_of_analytic` | a01J05 | `{f : ℂ → ℂ}` |
| `zeroSet_mul_const` | a01J05 | `{f : ℂ → ℂ} {μ : ℂ} (hμ : μ ≠ 0) :` |
| `zeroSet_subset_closedUnitDisk` | a01J05 | `(f : ℂ → ℂ) :` |
| `zero_of_orthogonal_to_monomials` | a94A04 | `{f : ℝ → ℝ} {μ : Measure ℝ}` |
| `zero_only_at_origin` | a95J02 | `{f : ℂ → ℂ} {lam : ℝ} (hlam : 0 < lam)` |
