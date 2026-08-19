# Frozen-statement dependency map

Generated: 2026-08-19 (deterministic corpus snapshot; rerun updates content)

This phase-one artifact is keyed on each frozen Lean theorem signature. Local
definitions mentioned by that signature are followed transitively through their own
signatures. Informal solutions are scanned independently and never contribute to the
statement dependency fields.

## Coverage

- Bundles: 475
- Parsed frozen statements: 448
- Not encoded (no `lean/Main.lean`): 27
- Encoded but unparseable/unclassified: 0
- Closed parsed frozen theorems: 229

## Machinery mentions: frozen Lean signatures versus informal solution

| Machinery | Statement bundles | Informal-solution bundles |
|---|---:|---:|
| alexander-whitney | 0 | 0 |
| cellular-homology | 0 | 19 |
| cohomology | 1 | 53 |
| covering-space | 15 | 25 |
| degree-theory | 0 | 19 |
| differential-forms | 0 | 16 |
| eilenberg-zilber | 0 | 0 |
| excision | 0 | 0 |
| fundamental-group | 16 | 51 |
| intersection-theory | 0 | 12 |
| kunneth | 0 | 5 |
| mayer-vietoris | 0 | 8 |
| orientation | 9 | 72 |
| singular-homology | 33 | 52 |
| stokes | 0 | 11 |
| transversality | 0 | 20 |
| van-kampen | 0 | 14 |

These counts are lexical observations included to expose divergence. They are
not the declaration dependency classification.

## Not encoded

- `t93A05`: missing lean/Main.lean
- `t93A06`: missing lean/Main.lean
- `t93J01`: missing lean/Main.lean
- `t93J03`: missing lean/Main.lean
- `t93J04`: missing lean/Main.lean
- `t93J05`: missing lean/Main.lean
- `t93J06`: missing lean/Main.lean
- `t94A01`: missing lean/Main.lean
- `t94A03`: missing lean/Main.lean
- `t94A04`: missing lean/Main.lean
- `t94J10`: missing lean/Main.lean
- `t94J11`: missing lean/Main.lean
- `t95A01`: missing lean/Main.lean
- `t95A04`: missing lean/Main.lean
- `t95A05`: missing lean/Main.lean
- `t96A01`: missing lean/Main.lean
- `t96A02`: missing lean/Main.lean
- `t96A04`: missing lean/Main.lean
- `t96A05`: missing lean/Main.lean
- `t96A06`: missing lean/Main.lean
- `t96A07`: missing lean/Main.lean
- `t96J01`: missing lean/Main.lean
- `t96J02`: missing lean/Main.lean
- `t96J03`: missing lean/Main.lean
- `t97A05`: missing lean/Main.lean
- `t97A06`: missing lean/Main.lean
- `t97A07`: missing lean/Main.lean

## Encoded but unparseable or unclassified

None.

## Per-bundle compact view

Full signatures and declaration lists are in the adjacent JSON artifact.

| Problem | Frozen theorem | Closed | Local closure | Unresolved declaration-like | Statement machinery | Informal machinery |
|---|---|---:|---:|---:|---|---|
| a00J01 | `eLpNorm_tendsto_top` | yes | 1 | 0 |  |  |
| a00J02 | `apm_a00j02` | yes | 1 | 1 |  |  |
| a00J03 | `composition_isometry`, `norm_comp_eq`, `composition_isometric_isomorphism` | yes | 3 | 0 |  |  |
| a00J04 | `connectedComponents_complement_lemniscate_le` | yes | 2 | 0 |  |  |
| a00J05 | `cauchyTransform_differentiableAt`, `cauchyTransform_differentiableOn`, `cauchyTransform_mul_z_tendsto`, `cauchyTransform_not_extendable_to_entire` | yes | 5 | 1 |  |  |
| a00J06 | `singular_at_one` | yes | 3 | 0 |  |  |
| a01A01 | `apm_a01a01` | no | 1 | 1 |  |  |
| a01A02 | `weakL2_implies_L1_bound` | yes | 1 | 0 |  |  |
| a01A03 | `convolution_identity_implies_indicator`, `analytic_compactSupport_eq_zero`, `convolution_identity_counterexample` | yes | 3 | 1 |  |  |
| a01A04 | `ball_volume_recursion`, `ballSlice_integral_tendsto_zero`, `ball_volume_superexponential_decay` | yes | 4 | 1 |  |  |
| a01A05 | `apm_a01a05` | yes | 2 | 0 |  |  |
| a01A06 | `distribution_polynomial_decay`, `orlicz_bound_not_implies_L2`, `exponential_decay_implies_L2` | yes | 4 | 0 |  |  |
| a01A07 | `tendstoUniformlyOn_of_L1_on_disks`, `differentiableOn_of_L1_limit`, `tendstoUniformlyOn_deriv_of_L1`, `L1_disk_convergence_analytic_upgrade` | yes | 5 | 0 |  |  |
| a01A08 | `connectedComponents_complement_lemniscate_le` | yes | 2 | 0 |  |  |
| a01A09 | `laplace_transform_analytic`, `laplace_transform_entire_of_compact_support` | yes | 8 | 0 |  |  |
| a01A10 | `gaussian_fourier_transform`, `fresnel_integral` | yes | 2 | 0 |  |  |
| a01A11 | `cauchyTransform_differentiableAt`, `cauchyTransform_tendsto_neg_vol`, `cauchyTransform_not_entire` | yes | 4 | 0 |  |  |
| a01A12 | `apm_a01a12` | no | 6 | 0 |  |  |
| a01J01 | `uniform_small_set_of_L3_bound`, `counterexample_from_spikes` | yes | 4 | 0 |  |  |
| a01J02 | `measurable_set_ae_eq_borel`, `measurable_function_ae_eq_borel` | yes | 3 | 0 |  |  |
| a01J03 | `deriv_sum_of_monotone`, `deriv_sum_of_monotone_ae` | yes | 4 | 1 |  |  |
| a01J04 | `apm_a01j04` | yes | 1 | 0 |  |  |
| a01J05 | `apm_a01j05` | yes | 4 | 0 |  | degree-theory |
| a01J06 | `apm_a01j06` | no | 3 | 1 |  |  |
| a02J01 | `schur_test` | yes | 2 | 3 |  |  |
| a02J02 | `radon_riesz` | yes | 1 | 0 |  |  |
| a02J03 | `scaled_integral_vanishes` | yes | 2 | 0 |  |  |
| a02J04 | `apm_a02j04` | yes | 6 | 2 |  |  |
| a02J05 | `dirichlet_integral_improper` | yes | 1 | 0 |  | orientation |
| a02J06 | `quadratic_bound`, `second_deriv_bound`, `rigidity`, `solves_problem` | yes | 6 | 0 |  |  |
| a02J07 | `logIntegral_im_bounds` | yes | 4 | 0 |  |  |
| a03J01 | `apm_a03j01` | yes | 2 | 1 |  |  |
| a03J02 | `differentiable_image_null_of_null`, `polynomial_map_image_null` | yes | 3 | 2 |  |  |
| a03J03 | `convolution_continuous`, `convolution_tendsto_zero` | yes | 2 | 0 |  |  |
| a03J04 | `apm_a03j04` | yes | 4 | 1 |  |  |
| a03J05 | `apm_a03j05` | no | 2 | 0 |  |  |
| a03J06 | `apm_a03j06` | yes | 1 | 0 |  |  |
| a03J07 | `apm_a03j07` | yes | 2 | 0 |  |  |
| a03J08 | `analytic_blowup_surjective` | yes | 1 | 0 |  |  |
| a92J01 | `apm_a92j01` | no | 5 | 0 |  |  |
| a92J02 | `convergesInMeasure.exists_subseq_ae_tendsto` | yes | 2 | 1 |  |  |
| a92J03 | `fourierTransform_norm_le`, `fourierTransform_continuous`, `fourierTransform_tendsto_zero`, `fourier_maps_L1_to_C0` | yes | 5 | 0 |  |  |
| a92J04 | `disk_selfmap_deriv_one_eq_identity`, `disk_selfmap_tangent_identity`, `disk_selfmap_tangent_identity'` | yes | 3 | 1 |  |  |
| a92J05 | `roots_outside_unit_disk` | yes | 1 | 0 |  | degree-theory |
| a92J06 | `integral_inv_two_plus_cos` | yes | 1 | 0 |  |  |
| a92J07 | `entire_avoids_ray_const`, `cauchy_riemann_ray_implies_const` | yes | 2 | 0 |  |  |
| a93A01 | `diffQuot_implies_unifCont`, `unifCont_implies_diffQuot`, `unifCont_iff_diffQuot` | yes | 6 | 0 |  |  |
| a93A02 | `apm_a93a02` | yes | 3 | 0 |  |  |
| a93A03 | `norm_sub_tendsto_zero_of_weak_and_norm`, `norm_le_liminf_of_weak` | yes | 3 | 0 |  |  |
| a93A04 | `lipschitz_implies_ac`, `lipschitz_V_limit_implies_ac`, `ac_implies_lipschitz_V_approx`, `ac_iff_lipschitz_V_approx` | yes | 6 | 1 |  |  |
| a93J01 | `ac_on_01_of_continuous_bv_ac_from_a` | yes | 1 | 1 |  |  |
| a93J02 | `tendsto_sum_alternating_harmonic`, `alternating_harmonic_eq_log_two` | yes | 2 | 0 |  |  |
| a93J03 | `apm_a93j03` | yes | 2 | 1 |  |  |
| a93J04 | `tendsto_eLpNorm_atTop` | yes | 1 | 1 |  |  |
| a93J05 | `doubly_periodic_entire_is_const` | yes | 1 | 0 |  |  |
| a93J06 | `deriv_norm_le_norm`, `schwarz_second_order_bound` | yes | 2 | 0 |  |  |
| a93J07 | `apm_a93j07` | yes | 1 | 0 |  |  |
| a94A01 | `ae_limit_indicator_eq_indicator`, `tendsto_setIntegral_of_indicator_limit`, `tendsto_eLpNorm_indicator_sub_iff_tendsto_measure_symmDiff` | yes | 3 | 0 |  |  |
| a94A02 | `apm_a94a02` | no | 3 | 2 |  |  |
| a94A03 | `gaussConv_Lp_contraction`, `gaussConv_tendsto_Lp` | yes | 4 | 0 |  |  |
| a94A04 | `zero_of_orthogonal_to_monomials` | yes | 1 | 0 |  |  |
| a94A05 | `vitali_covering_lemma_5`, `measure_image_critical_set_eq_zero` | yes | 2 | 0 |  |  |
| a94A06 | `integral_x7_over_1_plus_x12` | yes | 1 | 0 |  |  |
| a94A07 | `apm_a94a07` | no | 1 | 0 |  |  |
| a94A08 | `apm_a94a08` | yes | 1 | 0 |  |  |
| a94A09 | `apm_a94a09` | yes | 1 | 0 |  |  |
| a94A10 | `deriv_ne_zero_on_reals` | yes | 2 | 0 |  |  |
| a94J01 | `absolute_continuity_integral_norm`, `absolute_continuity_integral` | yes | 2 | 1 |  |  |
| a94J02 | `apm_a94j02` | yes | 1 | 1 |  |  |
| a94J03 | `apm_a94j03` | yes | 1 | 0 |  |  |
| a94J04 | `poissonConv_L2_contraction`, `poissonConv_tendsto_L2`, `poissonConv_tendsto_ae` | yes | 5 | 0 |  |  |
| a94J05 | `liouville_bounded`, `liouville_re_bounded_below` | yes | 2 | 0 |  |  |
| a94J06 | `apm_a94j06` | yes | 2 | 0 |  |  |
| a94J07 | `f_poly_exp_injective_on_disk` | yes | 2 | 0 |  |  |
| a94J08 | `no_entire_lower_bound_three_halves` | yes | 1 | 0 |  |  |
| a95A01 | `riemann_lebesgue_sandwich`, `indicator_not_riemann_integrable` | yes | 4 | 1 |  |  |
| a95A02 | `acOnUnitInterval_iff`, `ac_lusin_condition_N_lt_aux`, `ac_lusin_condition_N`, `ac_maps_null_to_null`, `ac_maps_measurable_to_measurable` | yes | 6 | 3 |  |  |
| a95A03 | `f_radial_integral`, `f_radial_memLp_iff`, `f_radial_not_memLp_top`, `f_radial_integrable`, `f_radial_conv_L2_bound` | yes | 7 | 1 |  |  |
| a95A04 | `constant_of_symmetric_mean_value` | yes | 2 | 0 |  |  |
| a95A05 | `eq_zero_of_vanishing_on_upper_arc` | yes | 1 | 0 |  |  |
| a95A06 | `lacunarySeries_continuousOn`, `lacunarySeries_differentiableOn`, `lacunarySeries_natural_boundary` | yes | 4 | 0 |  |  |
| a95A07 | `sum_inv_sq_eq_pi_sq_div_six`, `tsum_inv_sq`, `summable_inv_sq` | yes | 3 | 2 |  |  |
| a95A08 | `apm_a95a08` | yes | 4 | 0 |  |  |
| a95J01 | `subordination_deriv_le`, `subordination_deriv_eq` | yes | 2 | 0 |  |  |
| a95J02 | `entire_lower_bound_is_monomial` | yes | 1 | 0 |  |  |
| a95J03 | `apm_a95j03` | no | 3 | 0 |  | degree-theory |
| a95J04 | `apm_a95j04` | no | 1 | 2 |  |  |
| a95J05 | `tendstoInMeasure_of_integral_arctan_tendsto`, `integral_arctan_tendsto_of_tendstoInMeasure`, `tendstoInMeasure_iff_integral_arctan` | yes | 4 | 0 |  |  |
| a95J06 | `ac_on_01_of_homeo_fixing_cantor` | yes | 1 | 1 |  | orientation |
| a95J07 | `vitali_covering_5`, `measure_image_criticalSet_eq_zero` | yes | 4 | 0 |  |  |
| a95J08 | `convolution_integrand_integrableAE`, `young_convolution_inequality` | yes | 2 | 0 |  |  |
| a96A01 | `quasiNorm_antitone`, `quasiNorm_tendsto_exists`, `ae_pos_of_limit_pos`, `limit_ge_geometric_mean` | yes | 5 | 0 |  |  |
| a96A02 | `spikeFunction_spec`, `spikeFunction_holderWith`, `spikeFunction_not_absolutelyContinuous` | yes | 7 | 1 |  |  |
| a96A03 | `memLp_limit_of_ae_tendsto_bounded`, `weak_convergence_of_ae_tendsto_L2_bounded` | yes | 2 | 0 |  |  |
| a96A04 | `heatConv_contDiff`, `heatConv_L2_le`, `heatConv_tendsto_L2` | yes | 5 | 0 |  |  |
| a96A05 | `one_le_of_uniform_bound`, `sup_inv_sub_polynomial_ge_one` | yes | 2 | 0 |  |  |
| a96A06 | `taylor_coeffs_tend_to_one` | no | 1 | 0 |  |  |
| a96A07 | `apm_a96a07` | no | 4 | 0 |  | orientation |
| a96A08 | `apm_a96a08` | no | 2 | 0 |  |  |
| a96J01 | `apm_a96J01` | yes | 1 | 2 |  |  |
| a96J02 | `a96J02` | yes | 1 | 0 |  |  |
| a96J03 | `apm_a96j03` | yes | 1 | 0 |  |  |
| a96J04 | `ac_monotone_maps_null_to_null` | yes | 1 | 4 |  |  |
| a96J05 | `apm_a96j05` | yes | 4 | 0 |  |  |
| a96J06 | `apm_a96j06` | yes | 2 | 0 |  |  |
| a96J07 | `apm_a96J07` | yes | 1 | 0 |  |  |
| a96J08 | `apm_a96J08` | no | 2 | 0 |  | orientation |
| a96J09 | `apm_a96J09_main` | yes | 1 | 0 |  |  |
| a96J10 | `apm_a96J10_main` | yes | 1 | 0 |  |  |
| a97A01 | `apm_a97a01` | no | 3 | 0 |  |  |
| a97A02 | `apm_a97a02` | yes | 3 | 0 |  |  |
| a97A03 | `apm_a97a03` | yes | 1 | 1 |  |  |
| a97A04 | `apm_a97a04` | yes | 1 | 1 |  |  |
| a97A05 | `apm_a97A05_main` | yes | 2 | 0 |  | cohomology |
| a97A06 | `apm_a97A06_main` | yes | 1 | 0 |  |  |
| a97A07 | `apm_a97A07_main` | yes | 4 | 1 |  |  |
| a97A08 | `apm_a97A08_main` | yes | 1 | 0 |  |  |
| a97J01 | `bounded_integral_implies_integrable` | yes | 1 | 0 |  |  |
| a97J02 | `grid_count_converges_to_measure` | yes | 1 | 0 |  |  |
| a97J03 | `apm_a97j03` | yes | 2 | 0 |  |  |
| a97J04 | `apm_a97j04` | yes | 1 | 1 |  |  |
| a97J05 | `apm_a97j05` | no | 2 | 1 |  |  |
| a97J06 | `apm_a97j06` | no | 2 | 0 |  |  |
| a97J07 | `apm_a97j07` | no | 1 | 0 |  |  |
| a97J08 | `apm_a97j08` | no | 4 | 0 |  |  |
| a98A01 | `apm_a98a01` | yes | 2 | 1 |  |  |
| a98A02 | `apm_a98a02` | no | 1 | 0 |  |  |
| a98A03 | `apm_a98a03` | no | 2 | 1 |  |  |
| a98A04 | `apm_a98a04` | no | 2 | 0 |  |  |
| a98A05 | `apm_a98a05` | yes | 1 | 0 |  |  |
| a98A06 | `apm_a98a06` | yes | 1 | 0 |  |  |
| a98A07 | `apm_a98a07` | no | 1 | 0 |  |  |
| a98J01 | `apm_a98j01` | yes | 1 | 0 |  |  |
| a98J02 | `apm_a98j02` | no | 1 | 1 |  |  |
| a98J03 | `apm_a98j03` | no | 3 | 0 |  |  |
| a98J04 | `apm_a98j04` | yes | 4 | 0 |  |  |
| a99J01 | `apm_a99j01` | no | 2 | 1 |  |  |
| a99J02 | `apm_a99j02` | yes | 4 | 0 |  |  |
| a99J03 | `apm_a99j03` | no | 3 | 0 |  | cohomology |
| a99J04 | `apm_a99j04` | yes | 14 | 0 |  |  |
| a99J05 | `apm_a99j05` | no | 3 | 0 |  |  |
| a99J06 | `apm_a99j06` | yes | 1 | 0 |  |  |
| a99J07 | `apm_a99j07` | yes | 2 | 0 |  |  |
| a99J08 | `apm_a99j08` | no | 2 | 0 |  |  |
| a99J09 | `apm_a99j09` | yes | 3 | 0 |  |  |
| a99J10 | `apm_a99j10` | no | 1 | 0 |  | cohomology |
| aunk01 | `apm_aunk01` | yes | 2 | 0 |  |  |
| aunk02 | `apm_aunk02` | yes | 1 | 0 |  |  |
| aunk03 | `apm_aunk03` | yes | 1 | 0 |  | orientation |
| aunk04 | `apm_aunk04` | no | 1 | 0 |  |  |
| aunk05 | `apm_aunk05` | yes | 1 | 0 |  |  |
| b00J01 | `apm_b00j01` | yes | 2 | 2 |  |  |
| b00J02 | `apm_b00j02` | no | 1 | 2 |  |  |
| b00J03 | `apm_b00j03` | yes | 1 | 0 |  |  |
| b00J04 | `apm_b00j04` | yes | 1 | 0 |  |  |
| b01A01 | `apm_b01a01` | yes | 2 | 1 |  | cohomology |
| b01A02 | `apm_b01a02` | no | 2 | 0 |  |  |
| b01A03 | `apm_b01a03` | yes | 3 | 0 |  |  |
| b01A04 | `apm_b01a04` | yes | 2 | 0 |  |  |
| b01J01 | `apm_b01j01` | no | 3 | 0 |  |  |
| b01J02 | `apm_b01j02` | no | 4 | 0 |  |  |
| b01J03 | `apm_b01j03` | no | 3 | 0 |  |  |
| b01J04 | `apm_b01j04` | yes | 2 | 1 |  |  |
| b03J01 | `apm_b03j01` | no | 2 | 0 |  |  |
| b03J02 | `apm_b03j02` | yes | 2 | 1 |  |  |
| b03J03 | `apm_b03j03` | yes | 2 | 0 |  |  |
| b03J04 | `apm_b03j04` | yes | 3 | 0 |  |  |
| b90A01 | `apm_b90a01` | no | 1 | 2 |  |  |
| b90A02 | `apm_b90a02` | yes | 1 | 0 |  |  |
| b90A03 | `apm_b90a03` | no | 1 | 0 |  |  |
| b90A04 | `apm_b90a04` | yes | 5 | 1 |  |  |
| b93A01 | `apm_b93a01` | no | 2 | 2 |  |  |
| b93A02 | `apm_b93a02` | yes | 1 | 0 |  |  |
| b93A03 | `apm_b93a03` | yes | 2 | 0 |  |  |
| b93A04 | `apm_b93a04` | yes | 1 | 1 |  | singular-homology |
| b93J01 | `apm_b93j01` | no | 2 | 4 |  |  |
| b93J02 | `apm_b93j02` | yes | 1 | 0 |  |  |
| b93J03 | `apm_b93j03` | no | 1 | 1 |  |  |
| b93J04 | `apm_b93j04` | no | 2 | 1 |  |  |
| b94A01 | `apm_b94a01` | no | 1 | 1 |  |  |
| b94A02 | `apm_b94a02` | yes | 1 | 2 |  |  |
| b94J01 | `apm_b94j01` | no | 2 | 1 |  |  |
| b94J02 | `apm_b94j02` | yes | 1 | 1 |  |  |
| b94J03 | `apm_b94j03` | no | 2 | 2 |  |  |
| b94J04 | `apm_b94j04` | yes | 3 | 1 |  |  |
| b95J01 | `apm_b95j01` | yes | 3 | 3 |  |  |
| b95J02 | `apm_b95j02` | no | 3 | 0 |  | degree-theory |
| b95J03 | `apm_b95j03` | yes | 3 | 1 |  |  |
| b95J04 | `apm_b95j04` | no | 1 | 0 |  |  |
| b96A01 | `apm_b96a01` | no | 3 | 1 |  |  |
| b96A02 | `apm_b96a02` | no | 1 | 0 |  |  |
| b96A03 | `apm_b96a03` | no | 3 | 2 |  | cohomology |
| b96A04 | `apm_b96a04` | yes | 1 | 0 |  |  |
| b96J01 | `apm_b96j01` | yes | 1 | 2 |  |  |
| b96J02 | `apm_b96j02` | no | 9 | 0 |  |  |
| b96J03 | `apm_b96j03` | no | 8 | 1 |  |  |
| b96J04 | `apm_b96j04` | no | 1 | 0 |  |  |
| b97A01 | `apm_b97a01` | no | 8 | 2 |  |  |
| b97A02 | `apm_b97a02` | no | 3 | 0 |  |  |
| b97A03 | `apm_b97a03` | no | 4 | 2 |  |  |
| b97A04 | `apm_b97a04` | yes | 1 | 1 |  |  |
| b97J01 | `apm_b97j01` | no | 3 | 2 |  |  |
| b97J02 | `apm_b97j02` | yes | 4 | 2 |  |  |
| b97J03 | `apm_b97j03` | no | 3 | 0 |  |  |
| b97J04 | `apm_b97j04` | no | 5 | 2 |  |  |
| b98A01 | `apm_b98a01` | no | 1 | 2 |  |  |
| b98A02 | `apm_b98a02` | no | 2 | 0 |  |  |
| b98A03 | `apm_b98a03` | yes | 2 | 0 |  |  |
| b98A04 | `apm_b98a04` | no | 1 | 2 |  |  |
| b98J01 | `apm_b98j01` | no | 1 | 1 |  |  |
| b98J02 | `apm_b98j02` | yes | 1 | 0 |  |  |
| b98J03 | `apm_b98j03` | yes | 1 | 0 |  |  |
| b98J04 | `apm_b98j04` | no | 4 | 2 |  |  |
| b99A01 | `apm_b99a01` | yes | 1 | 1 |  |  |
| b99A02 | `apm_b99a02` | no | 1 | 0 |  |  |
| b99A03 | `apm_b99a03` | yes | 4 | 1 |  |  |
| b99A04 | `apm_b99a04` | yes | 2 | 2 |  |  |
| bpm-1-1-1 | `bpm_1_1_1` | yes | 1 | 0 |  |  |
| bpm-1-1-2 | `bpm_1_1_2` | yes | 1 | 0 |  |  |
| bpm-1-2-2 | `bpm_1_2_2` | yes | 1 | 0 |  |  |
| bpm-1-3-1 | `bpm_1_3_1` | yes | 1 | 1 |  |  |
| bpm-1-3-2 | `bpm_1_3_2` | yes | 1 | 0 |  |  |
| bpm-1-4-1 | `bpm_1_4_1` | yes | 1 | 0 |  |  |
| bpm-1-5-1 | `bpm_1_5_1` | yes | 1 | 0 |  |  |
| bpm-1-6-2 | `bpm_1_6_2` | yes | 1 | 0 |  |  |
| bpm-1-7-1 | `bpm_1_7_1` | yes | 1 | 0 |  |  |
| bpm-1-8-1 | `bpm_1_8_1` | no | 1 | 0 |  |  |
| m00A01 | `apm_m00a01` | yes | 4 | 0 |  | transversality |
| m00A02 | `apm_m00a02` | yes | 4 | 0 |  |  |
| m00A03 | `apm_m00a03` | yes | 1 | 0 |  |  |
| m00A04 | `apm_m00a04` | yes | 7 | 2 |  | cohomology |
| m00A05 | `apm_m00a05` | no | 2 | 0 |  |  |
| m00A06 | `apm_m00a06` | no | 4 | 2 |  |  |
| m01J01 | `apm_m01j01` | yes | 3 | 2 |  | fundamental-group |
| m01J02 | `apm_m01j02` | yes | 2 | 0 |  |  |
| m01J03 | `apm_m01j03` | yes | 4 | 0 |  |  |
| m01J04 | `apm_m01j04` | no | 12 | 6 |  | cohomology |
| m01J05 | `apm_m01j05` | no | 3 | 1 |  |  |
| m01J06 | `apm_m01j06` | no | 9 | 0 |  |  |
| m02A01 | `apm_m02a01` | yes | 4 | 0 |  |  |
| m02A02 | `apm_m02a02` | no | 19 | 3 |  | cohomology, degree-theory |
| m02A03 | `apm_m02a03` | no | 4 | 3 |  |  |
| m02A04 | `apm_m02a04` | yes | 3 | 0 |  |  |
| m02A05 | `apm_m02a05` | no | 4 | 0 |  |  |
| m02A06 | `apm_m02a06` | no | 2 | 1 |  |  |
| m02J01 | `apm_m02j01` | no | 2 | 0 |  |  |
| m02J02 | `apm_m02j02` | no | 8 | 1 |  | cohomology |
| m02J03 | `apm_m02j03` | no | 1 | 1 |  |  |
| m02J04 | `apm_m02j04` | no | 6 | 3 |  |  |
| m02J05 | `apm_m02j05` | no | 4 | 0 |  |  |
| m02J06 | `apm_m02j06` | no | 6 | 1 |  | cohomology |
| m03J01 | `apm_m03j01` | no | 9 | 4 |  | cohomology, singular-homology |
| m03J02 | `apm_m03j02` | no | 2 | 0 |  |  |
| m03J03 | `apm_m03j03` | no | 2 | 1 |  |  |
| m03J04 | `apm_m03j04` | no | 2 | 0 |  |  |
| m03J05 | `apm_m03j05` | no | 9 | 4 |  | cohomology |
| m93A01 | `apm_m93a01` | no | 7 | 0 |  | cohomology |
| m93A02 | `apm_m93a02` | no | 1 | 0 |  | cohomology, singular-homology, transversality |
| m93A03 | `apm_m93a03` | yes | 1 | 0 |  |  |
| m93A04 | `apm_m93a04` | no | 3 | 1 |  |  |
| m93J01 | `apm_m93j01` | no | 3 | 1 |  | cohomology |
| m93J02 | `apm_m93j02` | no | 10 | 1 |  | cohomology |
| m93J03 | `apm_m93j03` | no | 3 | 0 |  |  |
| m93J04 | `apm_m93j04` | yes | 3 | 1 |  |  |
| m93J05 | `apm_m93j05` | no | 5 | 0 |  |  |
| m93J06 | `apm_m93j06` | no | 3 | 0 |  |  |
| m93J07 | `apm_m93j07` | no | 5 | 1 |  |  |
| m94A01 | `apm_m94a01` | yes | 3 | 0 | cohomology | cohomology |
| m94A02 | `apm_m94a02` | no | 4 | 1 |  |  |
| m94A03 | `apm_m94a03` | no | 3 | 2 |  | cohomology |
| m94A04 | `apm_m94a04` | no | 3 | 0 |  | cohomology, degree-theory |
| m94A05 | `apm_m94a05` | no | 1 | 0 |  |  |
| m94J01 | `apm_m94j01` | no | 1 | 0 |  |  |
| m94J02 | `apm_m94j02` | no | 8 | 1 |  |  |
| m94J03 | `apm_m94j03` | yes | 1 | 0 |  |  |
| m94J04 | `apm_m94j04` | no | 7 | 1 |  |  |
| m94J05 | `apm_m94j05` | no | 2 | 0 |  |  |
| m94J06 | `apm_m94j06` | yes | 3 | 0 |  |  |
| m95A01 | `apm_m95a01` | yes | 2 | 0 |  |  |
| m95A02 | `apm_m95a02` | no | 5 | 0 |  | cohomology |
| m95A03 | `apm_m95a03` | no | 6 | 0 |  | cohomology |
| m95A04 | `apm_m95a04` | no | 7 | 1 |  |  |
| m95A05 | `apm_m95a05` | yes | 1 | 0 |  |  |
| m95J01 | `apm_m95j01` | no | 1 | 1 |  |  |
| m95J02 | `apm_m95j02` | no | 4 | 3 |  |  |
| m95J03 | `apm_m95j03` | no | 5 | 2 |  |  |
| m95J04 | `apm_m95j04` | no | 3 | 2 |  |  |
| m95J05 | `apm_m95j05` | yes | 5 | 1 |  |  |
| m95J06 | `apm_m95j06` | yes | 3 | 1 |  |  |
| m95J07 | `apm_m95j07` | no | 3 | 0 |  |  |
| m96A01 | `apm_m96a01` | yes | 1 | 0 |  |  |
| m96A02 | `apm_m96a02` | no | 3 | 0 |  |  |
| m96A03 | `apm_m96a03` | yes | 1 | 0 |  |  |
| m96A04 | `apm_m96a04` | yes | 1 | 0 |  |  |
| m96A05 | `apm_m96a05` | no | 6 | 1 |  | cohomology |
| m96A06 | `apm_m96a06` | no | 4 | 1 |  | cohomology |
| m96J01 | `projection_properties` | yes | 2 | 0 |  |  |
| m96J02 | `apm_m96j02` | no | 2 | 2 |  |  |
| m96J03 | `apm_m96j03` | no | 5 | 2 |  | orientation |
| m96J04 | `apm_m96j04` | no | 4 | 0 |  |  |
| m96J05 | `apm_m96j05` | no | 4 | 0 |  |  |
| m96J06 | `apm_m96j06` | no | 3 | 0 |  |  |
| m97A01 | `apm_m97a01` | no | 4 | 0 |  |  |
| m97A02 | `apm_m97a02` | no | 4 | 0 |  |  |
| m97A03 | `apm_m97a03` | no | 2 | 0 |  |  |
| m97A04 | `apm_m97a04` | no | 5 | 1 |  | cohomology |
| m97A06 | `apm_m97a06` | no | 6 | 0 |  | cohomology |
| m98A01 | `apm_m98a01` | yes | 2 | 2 |  |  |
| m98A02 | `apm_m98a02` | no | 1 | 0 |  |  |
| m98A03 | `apm_m98a03` | no | 3 | 0 |  |  |
| m98A04 | `apm_m98a04` | no | 4 | 1 |  |  |
| m98A05 | `apm_m98a05` | yes | 4 | 1 |  | cohomology |
| m98A06 | `apm_m98a06` | no | 6 | 1 |  | singular-homology |
| m98J02 | `apm_m98j02` | no | 10 | 1 |  |  |
| m98J03 | `apm_m98j03` | yes | 2 | 0 |  |  |
| m98J04 | `apm_m98j04` | no | 7 | 3 |  |  |
| m98J05 | `apm_m98j05` | no | 4 | 0 |  |  |
| m99A01 | `apm_m99a01` | no | 5 | 0 |  |  |
| m99A02 | `apm_m99a02` | no | 6 | 2 |  | cohomology |
| m99A03 | `apm_m99a03` | yes | 3 | 0 |  |  |
| m99A04 | `apm_m99a04` | yes | 1 | 0 |  |  |
| m99A05 | `apm_m99a05` | yes | 4 | 0 |  |  |
| m99A06 | `apm_m99a06` | no | 3 | 0 |  |  |
| m99J01 | `apm_m99j01` | no | 2 | 0 |  |  |
| m99J02 | `apm_m99j02` | no | 5 | 1 |  |  |
| m99J03 | `apm_m99j03` | no | 4 | 1 |  |  |
| m99J04 | `apm_m99j04` | no | 4 | 0 |  |  |
| m99J05 | `apm_m99j05` | yes | 3 | 0 |  |  |
| m99J06 | `apm_m99j06` | no | 8 | 2 |  | cohomology, singular-homology |
| t00A01 | `apm_t00a01` | no | 8 | 1 | fundamental-group, singular-homology | fundamental-group, mayer-vietoris, orientation, singular-homology, van-kampen |
| t00A02 | `apm_t00a02` | yes | 12 | 4 | covering-space, singular-homology | covering-space, fundamental-group, orientation, van-kampen |
| t00A03 | `apm_t00a03` | yes | 11 | 1 | singular-homology | orientation |
| t00A04 | `apm_t00a04` | yes | 2 | 0 |  | cohomology, differential-forms, orientation, singular-homology |
| t00A05 | `apm_t00a05` | yes | 7 | 6 |  | cohomology, differential-forms, orientation |
| t00J01 | `apm_t00j01` | no | 14 | 1 | singular-homology | orientation |
| t00J02 | `apm_t00j02` | yes | 12 | 1 | singular-homology | cohomology, intersection-theory, orientation, singular-homology, transversality |
| t00J03 | `apm_t00j03` | yes | 10 | 3 |  | cohomology, orientation |
| t00J04 | `apm_t00j04` | yes | 5 | 2 |  | cohomology, differential-forms |
| t00J06 | `apm_t00j06` | yes | 5 | 1 | covering-space, singular-homology | cohomology, fundamental-group, orientation |
| t00J07 | `apm_t00j07` | no | 8 | 1 | fundamental-group, singular-homology | cellular-homology, degree-theory, fundamental-group, singular-homology |
| t00J08 | `apm_t00j08` | no | 1 | 2 |  | cellular-homology, covering-space, fundamental-group |
| t01A01 | `apm_t01a01` | no | 2 | 1 | fundamental-group | covering-space, fundamental-group, singular-homology |
| t01A02 | `apm_t01a02` | no | 6 | 2 | covering-space, singular-homology | cellular-homology, covering-space, fundamental-group, singular-homology |
| t01A03 | `apm_t01a03` | no | 11 | 1 | fundamental-group, singular-homology | cellular-homology, fundamental-group, orientation, singular-homology |
| t01A04 | `apm_t01a04` | no | 11 | 1 | covering-space, fundamental-group | covering-space, fundamental-group, singular-homology, van-kampen |
| t01A05 | `apm_t01a05` | no | 11 | 3 | covering-space, singular-homology | covering-space, differential-forms, intersection-theory, orientation, transversality |
| t01A06 | `apm_t01a06` | yes | 9 | 1 |  | cohomology, orientation, stokes |
| t01A07 | `apm_t01a07` | yes | 9 | 1 |  | degree-theory, intersection-theory, orientation, singular-homology, transversality |
| t01A08 | `apm_t01a08` | no | 7 | 2 |  | intersection-theory, transversality |
| t01J01 | `apm_t01j01` | no | 10 | 1 | fundamental-group, singular-homology | orientation, singular-homology |
| t01J02 | `apm_t01j02` | no | 4 | 2 | covering-space | covering-space, fundamental-group, singular-homology |
| t01J03 | `apm_t01j03` | no | 12 | 5 | fundamental-group, singular-homology | cellular-homology, fundamental-group, kunneth, mayer-vietoris, orientation, singular-homology, van-kampen |
| t01J04 | `apm_t01j04` | no | 3 | 3 |  | cohomology, transversality |
| t01J05 | `apm_t01j05` | no | 7 | 2 | orientation, singular-homology | orientation |
| t01J06 | `apm_t01j06` | no | 17 | 3 |  | cohomology, differential-forms, fundamental-group, orientation, stokes |
| t02A01 | `apm_t02a01` | yes | 3 | 2 |  | fundamental-group |
| t02A02 | `apm_t02a02` | yes | 11 | 3 | orientation | orientation |
| t02A03 | `apm_t02a03` | no | 7 | 1 | fundamental-group, singular-homology | fundamental-group, singular-homology, van-kampen |
| t02A04 | `apm_t02a04` | no | 2 | 0 |  | cellular-homology, degree-theory, fundamental-group, orientation, singular-homology |
| t02A05 | `apm_t02a05` | no | 8 | 1 |  | orientation, stokes |
| t02A06 | `apm_t02a06` | no | 12 | 1 | singular-homology | cohomology, covering-space, degree-theory, intersection-theory, kunneth, orientation, singular-homology |
| t02A07 | `apm_t02a07` | no | 15 | 3 |  | transversality |
| t02A08 | `apm_t02a08` | no | 10 | 2 | orientation, singular-homology | degree-theory, fundamental-group, intersection-theory, orientation, singular-homology, transversality |
| t03J01 | `apm_t03j01` | no | 14 | 1 | orientation, singular-homology | cohomology, fundamental-group, orientation, singular-homology |
| t03J02 | `apm_t03j02` | no | 8 | 1 | fundamental-group, singular-homology | fundamental-group, mayer-vietoris, singular-homology, van-kampen |
| t03J03 | `apm_t03j03` | no | 13 | 1 | covering-space | covering-space, fundamental-group, orientation, singular-homology |
| t03J04 | `apm_t03j04` | no | 8 | 3 | singular-homology | covering-space, orientation |
| t03J05 | `apm_t03j05` | no | 7 | 3 |  | fundamental-group, intersection-theory, orientation, singular-homology, transversality |
| t03J06 | `apm_t03j06` | no | 12 | 3 |  | orientation |
| t91A01 | `apm_t91a01` | yes | 2 | 1 |  | degree-theory, orientation |
| t91A02 | `apm_t91a02` | yes | 3 | 3 | covering-space | cellular-homology, covering-space, fundamental-group, orientation |
| t91A03 | `isCompact_prod` | yes | 1 | 0 |  |  |
| t91A04 | `apm_t91a04` | yes | 1 | 0 |  |  |
| t91A05 | `apm_t91a05` | no | 4 | 0 |  | cohomology, differential-forms, fundamental-group, orientation, stokes |
| t91A06 | `apm_t91a06` | yes | 1 | 0 |  |  |
| t91A07 | `apm_t91a07` | yes | 1 | 0 |  | transversality |
| t91A08 | `apm_t91a08` | no | 11 | 3 |  | cohomology, degree-theory, differential-forms, orientation |
| t91J01 | `apm_t91j01` | yes | 3 | 0 |  |  |
| t91J02 | `apm_t91j02` | no | 3 | 1 |  | cohomology, fundamental-group, singular-homology |
| t91J03 | `apm_t91j03` | no | 6 | 1 | orientation, singular-homology | covering-space, fundamental-group, intersection-theory, orientation |
| t91J04 | `nonempty_nested_inter` | yes | 1 | 0 |  |  |
| t91J05 | `apm_t91j05` | no | 3 | 0 | covering-space | covering-space, fundamental-group, orientation, singular-homology |
| t91J06 | `apm_t91j06` | no | 3 | 1 |  | cohomology, singular-homology |
| t92J01 | `apm_t92j01` | yes | 1 | 0 |  |  |
| t92J02 | `image_of_compact_isCompact`, `homeomorph_of_compact_to_T2` | yes | 2 | 0 |  |  |
| t92J03 | `apm_t92j03` | yes | 1 | 0 |  |  |
| t92J04 | `apm_t92j04` | yes | 1 | 0 |  |  |
| t92J05 | `apm_t92j05` | no | 11 | 1 | fundamental-group, singular-homology | cellular-homology, covering-space, fundamental-group, orientation, singular-homology, van-kampen |
| t92J06 | `apm_t92j06` | no | 4 | 1 | covering-space | cellular-homology, covering-space, fundamental-group, orientation |
| t92J07 | `apm_t92j07` | no | 4 | 2 |  |  |
| t92J08 | `apm_t92j08` | no | 5 | 3 |  |  |
| t92J09 | `apm_t92j09` | yes | 9 | 1 |  | differential-forms, orientation, stokes |
| t93A01 | `apm_t93a01` | yes | 1 | 1 |  |  |
| t93A02 | `apm_t93a02` | yes | 3 | 1 |  |  |
| t93A03 | `apm_t93a03` | no | 8 | 3 | fundamental-group | fundamental-group, van-kampen |
| t93A04 | `apm_t93a04` | no | 6 | 2 |  | transversality |
| t93A05 | UNPARSEABLE | — | — | — |  | cohomology, covering-space, fundamental-group, intersection-theory, orientation, singular-homology, transversality |
| t93A06 | UNPARSEABLE | — | — | — |  | cohomology, differential-forms, orientation, stokes |
| t93J01 | UNPARSEABLE | — | — | — |  |  |
| t93J02 | `apm_t93j02` | yes | 1 | 0 |  |  |
| t93J03 | UNPARSEABLE | — | — | — |  | cellular-homology, covering-space, fundamental-group, orientation, van-kampen |
| t93J04 | UNPARSEABLE | — | — | — |  | intersection-theory, kunneth, orientation, singular-homology, transversality |
| t93J05 | UNPARSEABLE | — | — | — |  | orientation, stokes, transversality |
| t93J06 | UNPARSEABLE | — | — | — |  | degree-theory, singular-homology |
| t94A01 | UNPARSEABLE | — | — | — |  |  |
| t94A02 | `separate_closed_sets` | yes | 1 | 0 |  |  |
| t94A03 | UNPARSEABLE | — | — | — |  |  |
| t94A04 | UNPARSEABLE | — | — | — |  | fundamental-group, van-kampen |
| t94A05 | `connected_manifold_path_connected` | yes | 1 | 0 |  | van-kampen |
| t94A06 | `apm_t94a06` | no | 7 | 2 |  | transversality |
| t94A07 | `apm_t94a07` | no | 12 | 1 |  | orientation, singular-homology |
| t94A08 | `apm_t94a08` | no | 10 | 1 |  |  |
| t94A09 | `apm_t94a09` | no | 8 | 3 |  |  |
| t94A10 | `apm_t94a10` | no | 8 | 2 |  | cohomology, differential-forms, stokes |
| t94J01 | `connected_of_ladderConnected`, `ladderConnected_of_connected`, `connected_iff_ladderConnected` | yes | 5 | 1 |  |  |
| t94J02 | `apm_t94j02` | yes | 1 | 0 |  |  |
| t94J03 | `apm_t94j03` | yes | 3 | 2 |  |  |
| t94J04 | `apm_t94j04` | no | 4 | 1 | fundamental-group, singular-homology | fundamental-group, orientation |
| t94J05 | `apm_t94j05` | no | 5 | 1 |  | fundamental-group, singular-homology |
| t94J06 | `apm_t94j06` | no | 2 | 0 |  | degree-theory |
| t94J07 | `apm_t94j07` | no | 9 | 1 |  | cohomology, differential-forms, orientation, stokes |
| t94J08 | `apm_t94j08` | no | 9 | 2 | orientation, singular-homology | degree-theory, orientation |
| t94J09 | `apm_t94j09` | no | 14 | 4 | singular-homology | cellular-homology, orientation |
| t94J10 | UNPARSEABLE | — | — | — |  |  |
| t94J11 | UNPARSEABLE | — | — | — |  |  |
| t95A01 | UNPARSEABLE | — | — | — |  | fundamental-group, orientation |
| t95A02 | `apm_t95a02` | yes | 2 | 0 |  |  |
| t95A03 | `totally_bounded_complete_compact` | yes | 1 | 0 |  |  |
| t95A04 | UNPARSEABLE | — | — | — |  |  |
| t95A05 | UNPARSEABLE | — | — | — |  | orientation |
| t95J01 | `apm_t95j01` | yes | 1 | 0 |  |  |
| t95J02 | `apm_t95j02` | no | 9 | 0 |  | fundamental-group, orientation, singular-homology |
| t95J03 | `apm_t95j03` | yes | 5 | 5 | orientation | cellular-homology, fundamental-group, orientation |
| t95J04 | `apm_t95j04` | no | 8 | 2 |  | fundamental-group, kunneth, singular-homology |
| t95J05 | `apm_t95j05` | no | 9 | 4 |  | differential-forms, orientation |
| t95J06 | `apm_t95j06` | no | 11 | 4 | singular-homology | orientation |
| t96A01 | UNPARSEABLE | — | — | — |  | fundamental-group, orientation |
| t96A02 | UNPARSEABLE | — | — | — |  | cellular-homology, singular-homology |
| t96A03 | `apm_t96a03` | no | 6 | 2 | singular-homology | cellular-homology, mayer-vietoris, singular-homology |
| t96A04 | UNPARSEABLE | — | — | — |  |  |
| t96A05 | UNPARSEABLE | — | — | — |  | cohomology, singular-homology |
| t96A06 | UNPARSEABLE | — | — | — |  | degree-theory, orientation, singular-homology |
| t96A07 | UNPARSEABLE | — | — | — |  | transversality |
| t96A08 | `apm_t96a08` | no | 3 | 4 |  |  |
| t96J01 | UNPARSEABLE | — | — | — |  |  |
| t96J02 | UNPARSEABLE | — | — | — |  | cellular-homology, covering-space, fundamental-group, orientation |
| t96J03 | UNPARSEABLE | — | — | — |  |  |
| t96J04 | `apm_t96j04` | yes | 2 | 0 |  |  |
| t96J05 | `apm_t96j05` | no | 6 | 2 |  | transversality |
| t96J06 | `apm_t96j06` | no | 6 | 3 |  | intersection-theory, kunneth, orientation, singular-homology, transversality |
| t96J07 | `apm_t96j07` | no | 7 | 1 |  | orientation, singular-homology |
| t96J08 | `apm_t96j08` | no | 12 | 1 |  | differential-forms, orientation |
| t97A01 | `apm_t97a01` | no | 7 | 1 | fundamental-group, singular-homology | cellular-homology, fundamental-group, mayer-vietoris, orientation, singular-homology, van-kampen |
| t97A02 | `apm_t97a02` | no | 3 | 0 | singular-homology | cohomology, covering-space, fundamental-group, singular-homology |
| t97A03 | `apm_t97a03` | no | 14 | 2 | covering-space, fundamental-group, singular-homology | cellular-homology, fundamental-group, singular-homology |
| t97A04 | `apm_t97a04` | no | 8 | 3 | singular-homology | covering-space, degree-theory, fundamental-group |
| t97A05 | UNPARSEABLE | — | — | — |  | intersection-theory, orientation, singular-homology, transversality |
| t97A06 | UNPARSEABLE | — | — | — |  | cohomology, differential-forms, orientation, stokes |
| t97A07 | UNPARSEABLE | — | — | — |  |  |
| t97J01 | `apm_t97j01` | yes | 1 | 0 | covering-space | covering-space |
| t97J02 | `apm_t97j02` | no | 9 | 5 | covering-space, orientation | fundamental-group, orientation |
| t97J03 | `apm_t97j03` | no | 7 | 6 |  | fundamental-group |
| t97J04 | `apm_t97j04` | no | 7 | 1 | fundamental-group, singular-homology | fundamental-group, mayer-vietoris, singular-homology, van-kampen |
| t97J05 | `apm_t97j05` | no | 12 | 1 |  |  |
| t97J06 | `apm_t97j06` | no | 3 | 0 |  | covering-space, fundamental-group, singular-homology |
| t97J07 | `apm_t97j07` | no | 14 | 1 |  | singular-homology |
| t97J08 | `apm_t97j08` | no | 8 | 2 |  | cohomology, covering-space, degree-theory, differential-forms |
| t98A01 | `apm_t98a01` | no | 7 | 7 | covering-space | fundamental-group, orientation |
| t98A02 | `apm_t98a02` | no | 6 | 2 | singular-homology | cellular-homology, mayer-vietoris, orientation, singular-homology |
| t98A03 | `apm_t98a03` | no | 10 | 2 | covering-space, fundamental-group | fundamental-group, van-kampen |
| t98A04 | `apm_t98a04` | no | 12 | 4 |  | singular-homology |
| t98A05 | `apm_t98a05` | no | 19 | 1 |  | cohomology, differential-forms, orientation, stokes |
| t98J03 | `apm_t98j03` | no | 3 | 1 | singular-homology | cellular-homology, cohomology, mayer-vietoris, singular-homology |
| t99J03 | `apm_t99j03` | no | 7 | 5 | orientation | covering-space, fundamental-group, orientation |
| t99J04 | `apm_t99j04` | no | 3 | 2 |  | covering-space |

## Method limits

The extractor is lexical, not Lean's elaborator. A declaration basename found in
Mathlib or ConstructionTargets is reported as available even when namespace, typeclass,
or type mismatches would prevent its use. Conversely, notation and elaborator-generated
dependencies are invisible. `unresolved_declaration_like_references` is therefore an
audit queue, not proof that infrastructure is absent.

## Requirement layers

`object_requirements` records exact declarations reached from frozen statements,
including the problem-local definition chain and source expression. Its requirement
name combines the local semantic wrapper with the backing declaration, so distinct
instantiations do not collapse merely because both use `singularHomologyFunctor`.
`technique_requirements` records the first matching informal-solution line and remains
a separate, lower-confidence layer; it is never merged into object requirements.

## Singular-homology method reconciliation

The independent first-`apm_*`/whole-body pass reported 36 consumers; this
statement-rooted pass reports 33 after source adjudication.

| Problem | Adjudication | Reason |
|---|---|---|
| t01A04 | not statement-required | frozen statement names covering maps and FundamentalGroup; homology occurs only in later proof commentary |
| t01J05 | statement-required | conclusion uses apm_t01J05_eulerCharacteristic, whose definition sums finranks of apm_t01J05_H |
| t02A04 | not statement-required | frozen statement is the fixed-point property; rational homology occurs in bridge_1, not its object definitions |
| t03J02 | statement-required | frozen statement directly applies apm_t03J02_H in four conjuncts after two let binders |
| t94J08 | statement-required | t94J08HasDegree unfolds through t94J08TopHomologyMap to singularHomologyFunctor |
| t95J02 | not statement-required | frozen statement only asserts retractions; H1 occurs in proof bridge declarations |

## Obstruction coverage and provisional blocked-consumer ranking

Corpus coverage: 266/475 bundles. Non-complete
coverage: 197/319 bundles. The ranking is
unweighted by cost and is not a funding recommendation.

| Area | Blocked consumers | Structured | Legacy text | Object-consumer coverage | Overall obstruction coverage |
|---|---:|---:|---:|---:|---:|
| singular-homology | 24/197 obstruction-covered non-complete bundles | 24/24 | 0/24 | 32/32 | 197/319 |
| fundamental-group | 15/197 obstruction-covered non-complete bundles | 15/15 | 0/15 | 15/16 | 197/319 |
| covering-space | 14/197 obstruction-covered non-complete bundles | 14/14 | 0/14 | 13/14 | 197/319 |
| orientation | 9/197 obstruction-covered non-complete bundles | 9/9 | 0/9 | 8/9 | 197/319 |
| transversality | 7/197 obstruction-covered non-complete bundles | 7/7 | 0/7 | 0/0 | 197/319 |
| differential-forms | 6/197 obstruction-covered non-complete bundles | 6/6 | 0/6 | 0/0 | 197/319 |
| mayer-vietoris | 6/197 obstruction-covered non-complete bundles | 6/6 | 0/6 | 0/0 | 197/319 |
| van-kampen | 6/197 obstruction-covered non-complete bundles | 6/6 | 0/6 | 0/0 | 197/319 |
| cellular-homology | 3/197 obstruction-covered non-complete bundles | 3/3 | 0/3 | 0/0 | 197/319 |
| cohomology | 2/197 obstruction-covered non-complete bundles | 2/2 | 0/2 | 1/1 | 197/319 |
| intersection-theory | 2/197 obstruction-covered non-complete bundles | 2/2 | 0/2 | 0/0 | 197/319 |
| stokes | 2/197 obstruction-covered non-complete bundles | 2/2 | 0/2 | 0/0 | 197/319 |
| complex-analysis | 1/197 obstruction-covered non-complete bundles | 1/1 | 0/1 | 0/0 | 197/319 |
| degree-theory | 1/197 obstruction-covered non-complete bundles | 1/1 | 0/1 | 0/0 | 197/319 |
| excision | 1/197 obstruction-covered non-complete bundles | 1/1 | 0/1 | 0/0 | 197/319 |
| fourier-analysis | 1/197 obstruction-covered non-complete bundles | 1/1 | 0/1 | 0/0 | 197/319 |
| kunneth | 1/197 obstruction-covered non-complete bundles | 1/1 | 0/1 | 0/0 | 197/319 |
| measure-integral | 1/197 obstruction-covered non-complete bundles | 1/1 | 0/1 | 0/0 | 197/319 |

### Necessary-only blocked consumers

| Area | Necessary blocked consumers |
|---|---:|
| singular-homology | 24/197 |
| fundamental-group | 15/197 |
| covering-space | 14/197 |
| orientation | 9/197 |
| transversality | 7/197 |
| differential-forms | 6/197 |
| mayer-vietoris | 6/197 |
| van-kampen | 6/197 |
| cellular-homology | 3/197 |
| cohomology | 2/197 |
| intersection-theory | 2/197 |
| stokes | 2/197 |
| degree-theory | 1/197 |
| excision | 1/197 |
| kunneth | 1/197 |
| complex-analysis | 0/197 |
| fourier-analysis | 0/197 |
| measure-integral | 0/197 |

Bundles with an explicit structured `areas: []`: 77.
Structured and legacy sources remain separate in JSON; their union is used only for
the explicitly provisional ranking above.
