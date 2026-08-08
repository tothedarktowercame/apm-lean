# Helper-lemma index (generated — do not hand-edit)

2098 lemmas already proved in this repo, outside the problems'
own statements. GREP THIS BEFORE RE-DERIVING ANYTHING.

`LIB:` rows are importable today (182 lemmas across 17 modules,
e.g. `import ConstructionTargets.Rouche`). The rest live inside one problem
file: read the proof there and reuse the argument, or ask for the lemma to be
promoted into ConstructionTargets.

A lemma is listed when its own proof body has no `sorry`, so a problem that is
still open can still contribute helpers here.

| lemma | where | signature |
|---|---|---|
| `a_def` | a96J01 | `(n : ℕ) : a n = 1 - (2 : ℝ)⁻¹ ^ n` |
| `a_le_mid` | a96J01 | `(n : ℕ) : a n ≤ mid n` |
| `a_le_one` | a96J01 | `(n : ℕ) : a n ≤ 1` |
| `a_lt_b` | a96J01 | `(n : ℕ) : a n < b n` |
| `a_mono` | a96J01 | `(n : ℕ) : a n ≤ a (n + 1)` |
| `a_monotone` | a96J01 | `{j k : ℕ} (hjk : j ≤ k) : a j ≤ a k` |
| `a_nonneg` | a96J01 | `(n : ℕ) : 0 ≤ a n` |
| `a_zero` | a96J01 | `: a 0 = 0` |
| `abs_arctan_eq_arctan_abs` | a95J05 | `(t : ℝ) : \|arctan t\| = arctan \|t\|` |
| `abs_arctan_lt` | a95J05 | `(t : ℝ) : \|arctan t\| < π / 2` |
| `abs_exp_mul_real` | a01A09 | `(z : ℂ) (t : ℝ) : ‖Complex.exp (z * (t : ℂ))‖ = Real.exp (z.re * t)` |
| `abs_integral_exp_neg_mul_sinc_Ioi_le_four_div` | LIB: ConstructionTargets.Sinc | `{a A : ℝ} (ha : 0 < a) (hA : 0 < A) : \|∫ x in Set.Ioi A, Real.exp (-a * x) * Real.sinc x\| ≤ 4 / A` |
| `abs_integral_exp_neg_mul_sinc_le_four_div` | LIB: ConstructionTargets.Sinc | `{a A B : ℝ} (ha : 0 < a) (hA : 0 < A) (hAB : A ≤ B) : \|∫ x in A..B, Real.exp (-a * x) * Real.sinc x\| ≤ 4 / A` |
| `abs_integral_sinc_le_two_div` | LIB: ConstructionTargets.Sinc | `{a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : \|∫ x in a..b, Real.sinc x\| ≤ 2 / a` |
| `abs_laplace_kernel` | a01A09 | `(z : ℂ) (t : ℝ) : ‖Complex.exp (-(t : ℂ) * z)‖ = Real.exp (-z.re * t)` |
| `abs_polynomial_eval_le_absCoeff` | a96A04 | `(p : Polynomial ℝ) (x : ℝ) : \|p.eval x\| ≤ (polynomialAbsCoeff p).eval \|x\|` |
| `abs_sq` | a02J06 | `(z : ℂ) : ‖z ^ 2‖ = ‖z‖ ^ 2` |
| `abs_sub_pow_le` | a02J02 | `{p : ℕ} (a b : ℝ) : \|a - b\| ^ p ≤ 2 ^ p * (\|a\| ^ p + \|b\| ^ p)` |
| `absolute_continuity_integral` | a94J01 | `{f : (Fin n → ℝ) → ℝ} (hf : Integrable f volume) {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ (E : Set (Fin n → ℝ)), MeasurableSet E → volume E < ENNReal.ofReal δ → ‖∫ x in E, f x ∂volume‖ < ε` |
| `absolute_continuity_integral_norm` | a94J01 | `{f : (Fin n → ℝ) → ℝ} (hf : Integrable f volume) {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ (E : Set (Fin n → ℝ)), MeasurableSet E → volume E < ENNReal.ofReal δ → ∫ x in E, ‖f x‖ ∂volume < ε` |
| `absolutelyContinuousOnInterval_maps_null_to_null` | LIB: ConstructionTargets.LusinN | `{f : ℝ → ℝ} {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b) (hac : AbsolutelyContinuousOnInterval f a b) {E : Set ℝ} (hE : E ⊆ Icc a b) (hE0 : volume E = 0) : volume (f '' E) = 0` |
| `ac_continuousOn` | LIB: ConstructionTargets.LusinN | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) : ContinuousOn f (Icc (0:ℝ) 1)` |
| `ac_continuousOn` | a95A02 | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) : ContinuousOn f (Icc (0:ℝ) 1)` |
| `ac_dist_le_integral_norm_deriv` | LIB: ConstructionTargets.LusinN | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (hxy : x ≤ y) : dist (f x) (f y) ≤ ∫ t in x..y, ‖deriv f t‖` |
| `ac_dist_le_integral_norm_deriv` | a95A02 | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (hxy : x ≤ y) : dist (f x) (f y) ≤ ∫ t in x..y, ‖deriv f t‖` |
| `ac_iff_lipschitz_V_approx` | a93A04 | `(f : ℝ → ℝ) : AbsolutelyContinuousOnInterval f 0 1 ↔ ∃ fₙ : ℕ → ℝ → ℝ, (∀ n, LipschitzOn01 (fₙ n)) ∧ Tendsto (fun n => totalVariation (fun x => fₙ n x - f x)) atTop (𝓝 0)` |
| `ac_image_compact_is_compact` | LIB: ConstructionTargets.LusinN | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {K : Set ℝ} (hK : IsCompact K) (hK_sub : K ⊆ Icc (0:ℝ) 1) : IsCompact (f '' K)` |
| `ac_image_compact_is_compact` | a95A02 | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {K : Set ℝ} (hK : IsCompact K) (hK_sub : K ⊆ Icc (0:ℝ) 1) : IsCompact (f '' K)` |
| `ac_implies_lipschitz_V_approx` | a93A04 | `{f : ℝ → ℝ} (hac : AbsolutelyContinuousOnInterval f 0 1) : ∃ fₙ : ℕ → ℝ → ℝ, (∀ n, LipschitzOn01 (fₙ n)) ∧ Tendsto (fun n => totalVariation (fun x => fₙ n x - f x)) atTop (𝓝 0)` |
| `ac_integral_deriv_eq_sub` | LIB: ConstructionTargets.LusinN | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) : ∫ t in x..y, deriv f t = f y - f x` |
| `ac_integral_deriv_eq_sub` | a95A02 | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) : ∫ t in x..y, deriv f t = f y - f x` |
| `ac_intervalIntegrable_deriv` | LIB: ConstructionTargets.LusinN | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) : IntervalIntegrable (deriv f) volume 0 1` |
| `ac_intervalIntegrable_deriv` | a95A02 | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) : IntervalIntegrable (deriv f) volume 0 1` |
| `ac_lusin_condition_N` | LIB: ConstructionTargets.LusinN | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ E ⊆ Icc (0:ℝ) 1, volume.toOuterMeasure E ≤ ENNReal.ofReal δ → volume.toOuterMeasure (f '' E) ≤ ENNReal.ofReal ε` |
| `ac_lusin_condition_N` | a95A02 | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ E ⊆ Icc (0:ℝ) 1, volume.toOuterMeasure E ≤ ENNReal.ofReal δ → volume.toOuterMeasure (f '' E) ≤ ENNReal.ofReal ε` |
| `ac_lusin_condition_N_lt_aux` | LIB: ConstructionTargets.LusinN | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ E ⊆ Icc (0:ℝ) 1, volume.toOuterMeasure E < ENNReal.ofReal δ → volume.toOuterMeasure (f '' E) ≤ ENNReal.ofReal ε` |
| `ac_lusin_condition_N_lt_aux` | a95A02 | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ E ⊆ Icc (0:ℝ) 1, volume.toOuterMeasure E < ENNReal.ofReal δ → volume.toOuterMeasure (f '' E) ≤ ENNReal.ofReal ε` |
| `ac_maps_measurable_to_measurable` | a95A02 | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {E : Set ℝ} (hE : E ⊆ Icc (0:ℝ) 1) (hE_meas : NullMeasurableSet E volume) : NullMeasurableSet (f '' E) volume` |
| `ac_maps_null_to_null` | LIB: ConstructionTargets.LusinN | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {E : Set ℝ} (hE : E ⊆ Icc (0:ℝ) 1) (hE_null : volume E = 0) : volume (f '' E) = 0` |
| `ac_maps_null_to_null` | a95A02 | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {E : Set ℝ} (hE : E ⊆ Icc (0:ℝ) 1) (hE_null : volume E = 0) : volume (f '' E) = 0` |
| `ac_monotone_maps_null_to_null` | a96J04 | `(f : ℝ → ℝ) (hf_mono : MonotoneOn f (Icc 0 1)) (hf_ac : ∀ ε > 0, ∃ δ > 0, ∀ (s : Finset (ℝ × ℝ)), (∀ p ∈ s, p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc 0 1 ∧ p.1 ≤ p.2) → (∀ p q, p ∈ s → q ∈ s → p ≠ q → Disjoint (Ioo p.1 p.2) (Ioo q.1 q.2)) → (∑ p ∈ s, (p.2 - p.1)) < δ → (∑ p ∈ s, ‖f p.2 - f p.1‖) < ε) (E : Set ℝ) (hE : E ⊆ Icc 0 1) (hE_null : volume E = 0) : volume (f '' E) = 0` |
| `ac_of_bv_continuous_conditionN` | a95J06 | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0:ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0:ℝ) 1)) (hf_N : LusinConditionN f (Icc (0:ℝ) 1)) : AbsolutelyContinuousOnInterval f 0 1` |
| `ac_on_01_of_continuous_bv_ac_from_a` | a93J01 | `{f : ℝ → ℝ} (hcont : ContinuousOn f (Icc (0:ℝ) 1)) (hBV : BoundedVariationOn f (Icc (0:ℝ) 1)) (hAC : ∀ a : ℝ, 0 < a → a < 1 → AbsolutelyContinuousOnInterval f a 1) : AbsolutelyContinuousOnInterval f 0 1` |
| `ac_on_01_of_homeo_fixing_cantor` | a95J06 | `{f : ℝ → ℝ} (hf_bij : BijOn f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)) (hf_cont : ContinuousOn f (Icc (0:ℝ) 1)) (hf_fix : ∀ x ∈ cantorSet, f x = x) (hf_ac_compl : ∀ a b : ℝ, Icc a b ⊆ Icc (0 : ℝ) 1 → Icc a b ⊆ cantorSetᶜ → AbsolutelyContinuousOnInterval f a b) : AbsolutelyContinuousOnInterval f 0 1` |
| `ac_volume_image_component_le_lintegral_enorm_deriv` | LIB: ConstructionTargets.LusinN | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {U : Set ℝ} (x : ℝ) : volume (f '' (ordConnectedComponent U x ∩ Icc (0 : ℝ) 1)) ≤ ∫⁻ t in ordConnectedComponent U x ∩ Icc (0 : ℝ) 1, ‖deriv f t‖ₑ` |
| `ac_volume_image_component_le_lintegral_enorm_deriv` | a95A02 | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {U : Set ℝ} (x : ℝ) : volume (f '' (ordConnectedComponent U x ∩ Icc (0 : ℝ) 1)) ≤ ∫⁻ t in ordConnectedComponent U x ∩ Icc (0 : ℝ) 1, ‖deriv f t‖ₑ` |
| `ac_volume_image_subset_Icc_le_integral_norm_deriv` | LIB: ConstructionTargets.LusinN | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) {S : Set ℝ} (hS : S ⊆ Icc a b) : volume (f '' S) ≤ ENNReal.ofReal (∫ t in a..b, ‖deriv f t‖)` |
| `ac_volume_image_subset_Icc_le_integral_norm_deriv` | a95A02 | `{f : ℝ → ℝ} (hac : ACOnUnitInterval f) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) {S : Set ℝ} (hS : S ⊆ Icc a b) : volume (f '' S) ≤ ENNReal.ofReal (∫ t in a..b, ‖deriv f t‖)` |
| `accPt_closedBall_of_mem_sphere` | LIB: ConstructionTargets.Rouche | `{c z : ℂ} {R : ℝ} (hR : 0 < R) (hz : z ∈ sphere c R) : AccPt z (𝓟 (closedBall c R))` |
| `acOnUnitInterval_iff` | LIB: ConstructionTargets.LusinN | `(f : ℝ → ℝ) : ACOnUnitInterval f ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ E, E ∈ AbsolutelyContinuousOnInterval.disjWithin 0 1 → ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ → ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) < ε` |
| `acOnUnitInterval_iff` | a95A02 | `(f : ℝ → ℝ) : ACOnUnitInterval f ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ E, E ∈ AbsolutelyContinuousOnInterval.disjWithin 0 1 → ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ → ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) < ε` |
| `add_pow_le_two_pow_mul` | a02J02 | `{p : ℕ} (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) : (s + t) ^ p ≤ 2 ^ p * (s ^ p + t ^ p)` |
| `add_smul_ne_zero_of_norm_le_one` | LIB: ConstructionTargets.Rouche | `{f g : ℂ → ℂ} {z t : ℂ} (ht : ‖t‖ ≤ 1) (hfg : ‖g z‖ < ‖f z‖) : f z + t * g z ≠ 0` |
| `ae_abs_le_of_interval_integral_bound` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ) (hφloc : LocallyIntegrable φ volume) (hφ : ∀ (a b : ℝ), a < b → \|∫ x in Set.Icc a b, φ x\| ≤ M * (b - a) / (1 + (b - a))) : ∀ᵐ x ∂volume, \|φ x\| ≤ M` |
| `ae_limit_indicator_eq_indicator` | a94A01 | `{Eₙ : ℕ → Set ℝ} (hm : ∀ n, MeasurableSet (Eₙ n)) {f : ℝ → ℝ} (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => (Eₙ n).indicator (fun _ => (1 : ℝ)) x) atTop (nhds (f x))) : ∃ E : Set ℝ, MeasurableSet E ∧ f =ᵐ[volume] E.indicator (fun _ => (1 : ℝ))` |
| `ae_pos_of_limit_pos` | a96A01 | `{f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 1) volume) {L : ℝ} (hL : 0 < L) (hLim : Tendsto (quasiNorm f) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) : ∀ᵐ x ∂(volume.restrict (Icc 0 1)), 0 < ‖f x‖` |
| `ae_tendsto_radialLaverage` | LIB: ConstructionTargets.RadialMajorantAE | `{f : ℝ → ℝ} (hf : LocallyIntegrable f volume) : ∀ᵐ x ∂volume, Tendsto (radialLaverage f x) (𝓝[>] 0) (𝓝 0)` |
| `aeval_g` | a92J05 | `(z : ℂ) : aeval z g = 5 * z ^ 3` |
| `aeval_h` | a92J05 | `(z : ℂ) : aeval z h = z ^ 10 + 2 * z + 1` |
| `aeval_p` | a92J05 | `(z : ℂ) : aeval z p = z ^ 10 + 5 * z ^ 3 + 2 * z + 1` |
| `affine_of_entire_of_linear_growth` | LIB: ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f) {C : ℝ} (hC : 0 ≤ C) (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖)) : ∃ A B : ℂ, ∀ z : ℂ, f z = A * z + B` |
| `affine_of_entire_pick` | LIB: ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f) (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (hpos : ∀ z : ℂ, 0 < z.im → 0 < (f z).im) : ∃ a b : ℝ, 0 ≤ a ∧ ∀ z : ℂ, f z = (a : ℂ) * z + (b : ℂ)` |
| `affine_of_entire_pick_neg` | LIB: ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f) (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (hneg : ∀ z : ℂ, 0 < z.im → (f z).im < 0) : ∃ a b : ℝ, a ≤ 0 ∧ ∀ z : ℂ, f z = (a : ℂ) * z + (b : ℂ)` |
| `alg_G_deriv` | a94A06 | `(x : ℝ) : 4 * x^3 / (x^4 + 1) * (-(1:ℝ)/12) + (8*x^7 - 4*x^3) / (x^8 - x^4 + 1) * ((1:ℝ)/24) + (1 / (1 + ((2*x^4 - 1) / Real.sqrt 3)^2) * ((2 * (4 * x^3)) / Real.sqrt 3)) * (Real.sqrt 3 / 12) = x^7 / (1 + x^12)` |
| `alg_h3` | a94A06 | `(u : ℝ) : Real.sqrt 3 / 3 * (1 / (1 + ((2*u - 1) / Real.sqrt 3)^2) * (2 / Real.sqrt 3)) = 1 / (2 * (u^2 - u + 1))` |
| `alg_sum` | a94A06 | `(u : ℝ) (hu : 0 ≤ u) : u / ((u + 1) * (u^2 - u + 1)) = 1 / (u + 1) * (-(1:ℝ)/3) + (2*u - 1) / (u^2 - u + 1) * ((1:ℝ)/6) + 1 / (2 * (u^2 - u + 1))` |
| `almostEqualVolume_comm` | a01J02 | `{A B : Set ℝ} : AlmostEqualVolume A B ↔ AlmostEqualVolume B A` |
| `alternating_harmonic_eq_log_two` | a93J02 | `: Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (↑i + 1)) atTop (𝓝 (log 2))` |
| `analytic_blowup_surjective` | a03J08 | `{F : Finset ℂ} {f : ℂ → ℂ} (hf_holo : DifferentiableOn ℂ f (↑F : Set ℂ)ᶜ) (hf_infty : Tendsto (fun z => ‖f z‖) (cocompact ℂ) atTop) (hf_poles : ∀ zα ∈ F, Tendsto (fun z => ‖f z‖) (𝓝[≠] zα) atTop) : f '' (↑F : Set ℂ)ᶜ = univ` |
| `analytic_compactSupport_eq_zero` | a01A03 | `(f : ℝ → ℝ) (hf : ContDiff ℝ ω f) (hfc : HasCompactSupport f) : f = 0` |
| `analyticOrderAt_sub_self_ne_top_of_injOn` | LIB: ConstructionTargets.UnivalentDeriv | `{U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ} (hinj : InjOn g U) {z : ℂ} (hz : z ∈ U) : analyticOrderAt (fun w => g w - g z) z ≠ ⊤` |
| `apm_a01A01_index_lt_stage_sq` | a01A01 | `(k : ℕ) (_hk : 1 ≤ k) : k < apm_a01A01_stage k ^ 2` |
| `apm_a01A01_integral_typewriter1d` | a01A01 | `(k : ℕ) : ∫ x in Icc (0 : ℝ) 1, apm_a01A01_typewriter1d k x ∂volume = Real.sqrt (apm_a01A01_stage k) / apm_a01A01_stage k` |
| `apm_a01A01_integral_typewriter1d_tendsto` | a01A01 | `: Tendsto (fun k => ∫ x in Icc (0 : ℝ) 1, apm_a01A01_typewriter1d k x ∂volume) atTop (nhds 0)` |
| `apm_a01A01_position_lt_stage` | a01A01 | `(k : ℕ) : apm_a01A01_position k < apm_a01A01_stage k` |
| `apm_a01A01_stage_tendsto_atTop` | a01A01 | `: Tendsto apm_a01A01_stage atTop atTop` |
| `apm_a01A01_typewriter1d_nonneg` | a01A01 | `(k : ℕ) (x : ℝ) : 0 ≤ apm_a01A01_typewriter1d k x` |
| `apm_a01A05_counterexample_norm_of_two_le` | a01A05 | `{n : ℕ} (hn : 2 ≤ n) : ‖apm_a01A05_counterexample n‖ = 1` |
| `apm_a01A05_counterexample_norm_one` | a01A05 | `: ‖apm_a01A05_counterexample 1‖ = 1` |
| `apm_a01A05_counterexample_norm_one_all` | a01A05 | `(n : ℕ) : ‖apm_a01A05_counterexample n‖ = 1` |
| `apm_a01A05_counterexample_norm_zero` | a01A05 | `: ‖apm_a01A05_counterexample 0‖ = 1` |
| `apm_a01A05_counterexample_of_two_le` | a01A05 | `{n : ℕ} (hn : 2 ≤ n) : apm_a01A05_counterexample n = lp.single 2 n 1` |
| `apm_a01A05_counterexample_one` | a01A05 | `: apm_a01A05_counterexample 1 = (1 / 2 : ℝ) • lp.single 2 0 1 + (Real.sqrt 3 / 2) • lp.single 2 1 1` |
| `apm_a01A05_counterexample_zero` | a01A05 | `: apm_a01A05_counterexample 0 = lp.single 2 0 1` |
| `apm_a01A05_geometric_decay_tendsto_zero` | a01A05 | `: Tendsto (fun m : ℕ => (2 : ℝ) ^ (-(m : ℝ))) atTop (nhds 0)` |
| `apm_a01A05_gramSchmidt_one` | a01A05 | `{H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : ℕ → H) (h0 : ‖f 0‖ = 1) : InnerProductSpace.gramSchmidt ℝ f 1 = f 1 - inner ℝ (f 0) (f 1) • f 0` |
| `apm_a01A05_gramSchmidtNormed_one` | a01A05 | `{H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : ℕ → H) (h0 : ‖f 0‖ = 1) : InnerProductSpace.gramSchmidtNormed ℝ f 1 = ‖f 1 - inner ℝ (f 0) (f 1) • f 0‖⁻¹ • (f 1 - inner ℝ (f 0) (f 1) • f 0)` |
| `apm_a01A05_inner_tendsto_zero` | a01A05 | `{H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (seq : apm_a01A05_NearOrthogonalSeq H) (g : H) : Tendsto (fun m => inner ℝ g (seq.f m)) atTop (nhds 0)` |
| `apm_a01A05_inner_tendsto_zero_of_mem_closure_span` | a01A05 | `{H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (seq : apm_a01A05_NearOrthogonalSeq H) {v : H} (hv : v ∈ (Submodule.span ℝ (Set.range seq.f)).topologicalClosure) : Tendsto (fun m => inner ℝ v (seq.f m)) atTop (nhds 0)` |
| `apm_a01A05_inner_tendsto_zero_of_mem_span` | a01A05 | `{H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (seq : apm_a01A05_NearOrthogonalSeq H) {v : H} (hv : v ∈ Submodule.span ℝ (Set.range seq.f)) : Tendsto (fun m => inner ℝ v (seq.f m)) atTop (nhds 0)` |
| `apm_a01A12_conformalMap_fderiv_ne_zero` | a01A12 | `{z : ℂ} (hz : z ∈ apm_a01A12_H) : fderiv ℂ apm_a01A12_conformalMap z ≠ 0` |
| `apm_a01A12_conformalMap_hasDerivAt` | a01A12 | `{z : ℂ} (hz : z ∈ apm_a01A12_H) : HasDerivAt apm_a01A12_conformalMap ((1 / 4 : ℂ) * (1 - z ^ 2) ^ ((1 / 4 : ℂ) - 1) * (-2 * z)) z` |
| `apm_a01A12_conformalMap_injOn` | a01A12 | `: Set.InjOn apm_a01A12_conformalMap apm_a01A12_H` |
| `apm_a01A12_conformalMap_ne_zero` | a01A12 | `{z : ℂ} (hz : z ∈ apm_a01A12_H) : apm_a01A12_conformalMap z ≠ 0` |
| `apm_a01A12_conformalMap_pow_four` | a01A12 | `(z : ℂ) : apm_a01A12_conformalMap z ^ 4 = 1 - z ^ 2` |
| `apm_a01A12_identity_parameters_positive` | a01A12 | `: (0 : ℝ) < 1 * 1 - 0 * 0` |
| `apm_a01A12_mobius_one_zero_zero_one` | a01A12 | `(z : ℂ) : apm_a01A12_mobius 1 0 0 1 z = z` |
| `apm_a01A12_one_sub_sq_mem_slitPlane` | a01A12 | `{z : ℂ} (hz : z ∈ apm_a01A12_H) : 1 - z ^ 2 ∈ Complex.slitPlane` |
| `apm_a01A12_one_sub_sq_ne_zero` | a01A12 | `{z : ℂ} (hz : z ∈ apm_a01A12_H) : 1 - z ^ 2 ≠ 0` |
| `apm_a01A12_sq_mem_slitPlane` | a01A12 | `{w : ℂ} (hw : 0 < w.re) : 0 < (w ^ 2).re ∨ (w ^ 2).im ≠ 0` |
| `apm_a01J04_entire_coeff_superexp` | a01J04 | `(g : ℂ → ℂ) (hg : Differentiable ℂ g) (T : ℝ) (hT : 0 < T) : Tendsto (fun n : ℕ => T ^ n * ‖iteratedDeriv n g 2 / (n.factorial : ℂ)‖) atTop (nhds 0)` |
| `apm_a01J04_error_eq_entire` | a01J04 | `(f g : ℂ → ℂ) (lam : ℂ) (hg : Differentiable ℂ g) (hf : ∀ z : ℂ, f z = lam / (z - 1) + g z) (n : ℕ) : (-1 : ℂ) ^ n * iteratedDeriv n f 2 / (Nat.factorial n : ℂ) - lam = (-1 : ℂ) ^ n * (iteratedDeriv n g 2 / (Nat.factorial n : ℂ))` |
| `apm_a01J04_geom_iteratedDeriv` | a01J04 | `(n : ℕ) : iteratedDeriv n (fun z : ℂ => (1 - z)⁻¹) 0 = (n.factorial : ℂ)` |
| `apm_a01J04_pole_iteratedDeriv` | a01J04 | `(lam : ℂ) (n : ℕ) : iteratedDeriv n (fun z : ℂ => lam / (z - 1)) 2 = lam * ((-1 : ℂ) ^ n * (n.factorial : ℂ))` |
| `apm_a01J05_analyticAt_of_closedBall` | a01J05 | `{f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε) (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε))) {z : ℂ} (hz : z ∈ apm_a01J05_disk) : AnalyticAt ℂ f z` |
| `apm_a01J05_deriv_analyticAt_of_closedBall` | a01J05 | `{f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε) (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε))) {z : ℂ} (hz : z ∈ apm_a01J05_disk) : AnalyticAt ℂ (deriv f) z` |
| `apm_a01J05_exists_finiteDivisor_factorization` | a01J05 | `{f : ℂ → ℂ} (hf_analytic : ∃ ε > 0, DifferentiableOn ℂ f (closedBall 0 (1 + ε))) (hf_boundary : ∀ z ∈ apm_a01J05_circle, ‖f z‖ = 1) : ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall 0 1) ∧ (∀ z : closedBall (0 : ℂ) 1, h z ≠ 0) ∧ f =ᶠ[codiscreteWithin (closedBall 0 1)] (∏ᶠ u, (· - u) ^ divisor f (closedBall 0 1) u) * h` |
| `apm_a01J05_order_deriv_add_one` | a01J05 | `{f : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε) (hf : DifferentiableOn ℂ f (closedBall 0 (1 + ε))) {z : ℂ} (hz : z ∈ apm_a01J05_disk) : analyticOrderAt (deriv f) z + 1 = analyticOrderAt (fun w => f w - f z) z` |
| `apm_a01J06_apply_eq_zero_of_enumeratesZeros` | a01J06 | `{f : ℂ → ℂ} {ω : ℕ → ℂ} (hω : apm_a01J06_EnumeratesZeros f ω) (n : ℕ) : f (ω n) = 0` |
| `apm_a01J06_card_preimage_eq_finsum_analyticOrder` | a01J06 | `{f : ℂ → ℂ} {ω : ℕ → ℂ} (hω : apm_a01J06_EnumeratesZeros f ω) {s : Set ℂ} (hs : s.Finite) : Nat.card {n : ℕ // ω n ∈ s} = ∑ᶠ z ∈ s, analyticOrderNatAt f z` |
| `apm_a01J06_finite_preimage_of_enumeratesZeros` | a01J06 | `{f : ℂ → ℂ} {ω : ℕ → ℂ} (hω : apm_a01J06_EnumeratesZeros f ω) {s : Set ℂ} (hs : s.Finite) : {n : ℕ \| ω n ∈ s}.Finite` |
| `apm_a02J04_lintegral_g_right` | a02J04 | `(x : ℝ) : (∫⁻ y : ℝ, apm_a02J04_g (x, y) ∂volume) = ENNReal.ofReal (apm_a02J04_tauDensity x)` |
| `apm_a02J04_measurable_g` | a02J04 | `: Measurable apm_a02J04_g` |
| `apm_a02J04_measurable_P` | a02J04 | `: Measurable apm_a02J04_P` |
| `apm_a02J04_measurable_tauDensity` | a02J04 | `: Measurable fun x : ℝ ↦ ENNReal.ofReal (apm_a02J04_tauDensity x)` |
| `apm_a02J04_tau_eq_withDensity` | a02J04 | `: apm_a02J04_tau = volume.withDensity (fun x ↦ ENNReal.ofReal (apm_a02J04_tauDensity x))` |
| `apm_a02J04_tauDensity_ne_zero` | a02J04 | `{x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hx0 : x ≠ 0) : ENNReal.ofReal (apm_a02J04_tauDensity x) ≠ 0` |
| `apm_a02J04_volume_verticalSection` | a02J04 | `(x : ℝ) : volume {y : ℝ \| 0 ≤ y ∧ y ≤ x} = ENNReal.ofReal x` |
| `apm_a03J05_integrable` | a03J05 | `(t : ℝ) : Integrable (apm_a03J05_integrand t) volume` |
| `apm_a03J05_integral_neg` | a03J05 | `(t : ℝ) : (∫ x in Ioi (0 : ℝ), apm_a03J05_integrand (-t) x ∂volume) = ∫ x in Ioi (0 : ℝ), apm_a03J05_integrand t x ∂volume` |
| `apm_a03J05_integral_zero` | a03J05 | `: ∫ x in Ioi (0 : ℝ), apm_a03J05_integrand 0 x ∂volume = Real.pi / 2` |
| `apm_a03J05_integrand_neg` | a03J05 | `(t x : ℝ) : apm_a03J05_integrand (-t) x = apm_a03J05_integrand t x` |
| `apm_a03J06_growth_cauchy_bound` | a03J06 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f) (A : ℝ) (m k : ℕ) (hbound : ∀ z : ℂ, 1 < ‖z‖ → ‖f z‖ ≤ A * ‖z‖ ^ m) {R : ℝ} (hR : 1 < R) : ‖iteratedDeriv k f 0‖ ≤ k.factorial * (A * R ^ m) / R ^ k` |
| `apm_a03J06_iteratedDeriv_eq_zero_of_natDegree_lt` | a03J06 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f) (A : ℝ) (m k : ℕ) (hbound : ∀ z : ℂ, 1 < ‖z‖ → ‖f z‖ ≤ A * ‖z‖ ^ m) (hmk : m < k) : iteratedDeriv k f 0 = 0` |
| `apm_a92J01_discontinuousCounterexample_memLp` | a92J01 | `(p : ℝ) : MemLp apm_a92J01_discontinuousCounterexample (ENNReal.ofReal p) apm_a92J01_unitMeasure` |
| `apm_a92J01_discontinuousCounterexample_not_continuousOn` | a92J01 | `: ¬ContinuousOn apm_a92J01_discontinuousCounterexample (Icc 0 1)` |
| `apm_a92J01_memLp_mono_on_unitMeasure` | a92J01 | `(p q : ℝ) (hpq : q < p) (f : ℝ → ℝ) (hf : MemLp f (ENNReal.ofReal p) apm_a92J01_unitMeasure) : MemLp f (ENNReal.ofReal q) apm_a92J01_unitMeasure` |
| `apm_a92J01_neg_one_le_q_exponent` | a92J01 | `{p q : ℝ} (hq : 1 ≤ q) (hpq : q < p) : -1 ≤ -((1 / p + 1 / q) / 2) * q` |
| `apm_a92J01_p_exponent_lt_neg_one` | a92J01 | `{p q : ℝ} (hq : 1 ≤ q) (hpq : q < p) : -((1 / p + 1 / q) / 2) * p < -1` |
| `apm_a93A02_counterexample_ae_tendsto_zero` | a93A02 | `: ∀ᵐ x ∂apm_a93A02_measure, Tendsto (fun n : ℕ ↦ apm_a93A02_counterexample n x) atTop (nhds 0)` |
| `apm_a93A02_counterexample_eLpNorm_two` | a93A02 | `(n : ℕ) : eLpNorm (apm_a93A02_counterexample n) 2 apm_a93A02_measure = 1` |
| `apm_a93A02_counterexample_tendsto_zero_of_ne_zero` | a93A02 | `{x : ℝ} (hx : x ≠ 0) : Tendsto (fun n : ℕ ↦ apm_a93A02_counterexample n x) atTop (nhds 0)` |
| `apm_a93A02_measure_Icc_inv_succ` | a93A02 | `(n : ℕ) : apm_a93A02_measure (Icc (0 : ℝ) ((n.succ : ℝ)⁻¹)) = ENNReal.ofReal ((n.succ : ℝ)⁻¹)` |
| `apm_a93A02_tendsto_Lp_of_ae_tendsto_of_L2_bounded` | a93A02 | `{f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {μ : Measure ℝ} (hfm : ∀ n, AEStronglyMeasurable (f n) μ) (hgm : AEStronglyMeasurable g μ) (hf2 : ∀ n, MemLp (f n) 2 μ) (hbdd : ∃ C : NNReal, ∀ n, eLpNorm (f n) 2 μ ≤ C) (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p < 2) [IsFiniteMeasure μ] : Tendsto (fun n => eLpNorm (fun x => f n x - g x) p μ) atTop (𝓝 0)` |
| `apm_a93A02_unifIntegrable_of_L2_bounded` | a93A02 | `{f : ℕ → ℝ → ℝ} {μ : Measure ℝ} (hfm : ∀ n, AEStronglyMeasurable (f n) μ) (hf2 : ∀ n, MemLp (f n) 2 μ) (hbdd : ∃ C : NNReal, ∀ n, eLpNorm (f n) 2 μ ≤ C) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p < 2) : UnifIntegrable f p μ` |
| `apm_a93J07_eventually_nonvanishing_on_sphere` | a93J07 | `{Ω : Set ℂ} (hΩ : IsOpen Ω) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hFhol : ∀ n, DifferentiableOn ℂ (F n) Ω) (hconv : TendstoLocallyUniformlyOn F f atTop Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) {r : ℝ} (hr : 0 < r) (hclosed : Metric.closedBall z₀ r ⊆ Ω) (hboundary : ∀ z ∈ Metric.sphere z₀ r, f z ≠ 0) : ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere z₀ r, F n z ≠ 0` |
| `apm_a93J07_limit_differentiable` | a93J07 | `{Ω : Set ℂ} (hΩ : IsOpen Ω) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hFhol : ∀ n, DifferentiableOn ℂ (F n) Ω) (hconv : TendstoLocallyUniformlyOn F f atTop Ω) : DifferentiableOn ℂ f Ω` |
| `apm_a93J07_zero_persistence` | a93J07 | `{Ω : Set ℂ} (hΩ : IsOpen Ω) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hFhol : ∀ n, DifferentiableOn ℂ (F n) Ω) (hconv : TendstoLocallyUniformlyOn F f atTop Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) {m : ℕ} (hm : analyticOrderAt f z₀ = m + 1) : ∃ r > 0, Metric.closedBall z₀ r ⊆ Ω ∧ ∀ᶠ n in atTop, ∃ z ∈ Metric.ball z₀ r, F n z = 0` |
| `apm_a94a02_ae_all_differentiable` | a94A02 | `(f : ℕ → ℝ → ℝ) (hf_ac : ∀ n, AbsolutelyContinuousOnInterval (f n) 0 1) : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ n, DifferentiableAt ℝ (f n) x` |
| `apm_a94a09_homotopy_ne_zero` | a94A09 | `{f : ℂ → ℂ} (hf_boundary : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ 1) (hf_no_boundary_fixed_point : ∀ z ∈ sphere (0 : ℂ) 1, f z ≠ z) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : ∀ z ∈ sphere (0 : ℂ) 1, z - (t : ℂ) * f z ≠ 0` |
| `apm_a94a09_mapsTo_closedBall` | a94A09 | `{f : ℂ → ℂ} (hf_continuous : ContinuousOn f (closedBall 0 1)) (hf_analytic : DifferentiableOn ℂ f (ball 0 1)) (hf_boundary : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ ≤ 1) : MapsTo f (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1)` |
| `apm_a94J02_ae_deriv_zero_on` | a94J02 | `(C : Set ℝ) (hC : MeasurableSet C) : ∀ᵐ x ∂volume, x ∈ C → HasDerivAt (apm_a94J02_H C) 0 x` |
| `apm_a94J02_density_integrable` | a94J02 | `(C : Set ℝ) (hC : MeasurableSet C) : Integrable (apm_a94J02_density C) volume` |
| `apm_a94J02_density_nonneg` | a94J02 | `(C : Set ℝ) (t : ℝ) : 0 ≤ apm_a94J02_density C t` |
| `apm_a94J02_density_norm_le_one` | a94J02 | `(C : Set ℝ) (t : ℝ) : ‖apm_a94J02_density C t‖ ≤ 1` |
| `apm_a94J02_exists_fat_compact` | a94J02 | `: ∃ C : Set ℝ, IsClosed C ∧ C ⊆ Icc 0 1 ∧ interior C = ∅ ∧ 0 < volume C` |
| `apm_a94J02_H_lipschitz` | a94J02 | `(C : Set ℝ) (hC : MeasurableSet C) : LipschitzOnWith 1 (apm_a94J02_H C) (Icc (0 : ℝ) 1)` |
| `apm_a94J02_H_nonneg` | a94J02 | `(C : Set ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ apm_a94J02_H C x` |
| `apm_a94J02_H_strictMonoOn` | a94J02 | `(C : Set ℝ) (hC : IsClosed C) (hCint : interior C = ∅) : StrictMonoOn (apm_a94J02_H C) (Icc 0 1)` |
| `apm_a94J02_H_sub` | a94J02 | `(C : Set ℝ) (hC : MeasurableSet C) (x y : ℝ) : apm_a94J02_H C y - apm_a94J02_H C x = ∫ t in x..y, apm_a94J02_density C t` |
| `apm_a94J03_injective_of_continuous_isOpenMap` | a94J03 | `{f : ℝ → ℝ} (hf : Continuous f) (hopen : IsOpenMap f) : Function.Injective f` |
| `apm_a94J03_not_isMaxOn_of_isOpenMap` | a94J03 | `{f : ℝ → ℝ} (hf : IsOpenMap f) {s : Set ℝ} (hs : IsOpen s) {x : ℝ} (hx : x ∈ s) : ¬IsMaxOn f s x` |
| `apm_a94J03_not_isMinOn_of_isOpenMap` | a94J03 | `{f : ℝ → ℝ} (hf : IsOpenMap f) {s : Set ℝ} (hs : IsOpen s) {x : ℝ} (hx : x ∈ s) : ¬IsMinOn f s x` |
| `apm_a94J06_at_zero` | a94J06 | `: (∮ ζ in C(0, 1), starRingEnd ℂ ζ / (ζ - 0)) = 0` |
| `apm_a94J06_conj_eq_inv_on_circle` | a94J06 | `{ζ : ℂ} (hζ : ‖ζ‖ = 1) : starRingEnd ℂ ζ = ζ⁻¹` |
| `apm_a94J06_inside` | a94J06 | `{z : ℂ} (hz : ‖z‖ < 1) : (∮ ζ in C(0, 1), starRingEnd ℂ ζ / (ζ - z)) = 0` |
| `apm_a94J06_inside_nonzero` | a94J06 | `{z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) : (∮ ζ in C(0, 1), starRingEnd ℂ ζ / (ζ - z)) = 0` |
| `apm_a94J06_integral_eq_rational` | a94J06 | `{z : ℂ} : (∮ ζ in C(0, 1), apm_a94J06_integrand z ζ) = ∮ ζ in C(0, 1), ((ζ * (ζ - z))⁻¹ : ℂ)` |
| `apm_a94J06_integrand_eq_rational` | a94J06 | `{ζ z : ℂ} (hζ : ‖ζ‖ = 1) (hne : ζ ≠ z) : apm_a94J06_integrand z ζ = (ζ * (ζ - z))⁻¹` |
| `apm_a94J06_not_circleIntegrable_of_norm_eq_one` | a94J06 | `{z : ℂ} (hz : ‖z‖ = 1) : ¬CircleIntegrable (apm_a94J06_integrand z) 0 1` |
| `apm_a94J06_outside` | a94J06 | `{z : ℂ} (hz : 1 < ‖z‖) : (∮ ζ in C(0, 1), starRingEnd ℂ ζ / (ζ - z)) = -(2 * π * I) / z` |
| `apm_a95A08_curveLength_ge_two_pi` | a95A08 | `{f : ℂ → ℂ} (hf_holo : ∃ ε > 0, DifferentiableOn ℂ f (closedBall 0 (1 + ε))) (_hf_inj : Set.InjOn f (closedBall 0 1)) (_hf_zero : f 0 = 0) (hf_deriv : ‖deriv f 0‖ = 1) : 2 * Real.pi ≤ apm_a95A08_curveLength f` |
| `apm_a95A08_disk_not_subset_image_of_length_gt` | a95A08 | `{f : ℂ → ℂ} (hf_holo : ∃ ε > 0, DifferentiableOn ℂ f (closedBall 0 (1 + ε))) (hf_inj : InjOn f (closedBall 0 1)) (hf_zero : f 0 = 0) (hf_deriv : ‖deriv f 0‖ = 1) (hlen : 2 * Real.pi < apm_a95A08_curveLength f) : ¬(ball (0 : ℂ) 1 ⊆ f '' ball 0 1)` |
| `apm_a95A08_rotation_of_disk_subset_image` | a95A08 | `{f : ℂ → ℂ} (hf_holo : DifferentiableOn ℂ f (ball 0 1)) (hf_inj : InjOn f (ball 0 1)) (hf_zero : f 0 = 0) (hf_deriv : ‖deriv f 0‖ = 1) (h_subset : ball (0 : ℂ) 1 ⊆ f '' ball 0 1) : ∃ α : ℝ, ∀ z ∈ ball (0 : ℂ) 1, f z = exp (I * (α : ℂ)) * z` |
| `apm_a95J03_algPoly_degree_le` | a95J03 | `(a : ℤ → ℂ) (N : ℕ) : (apm_a95J03_algPoly a N).natDegree ≤ 2 * N` |
| `apm_a95J03_algPoly_eval_eq_mul_laurent` | a95J03 | `(a : ℤ → ℂ) (N : ℕ) (w : ℂ) (hw : w ≠ 0) : (apm_a95J03_algPoly a N).eval w = w ^ N * ((Finset.Icc (-(N : ℤ)) N).sum fun n => a n * w ^ n)` |
| `apm_a95J03_algPoly_sub_degree_le` | a95J03 | `(a : ℤ → ℂ) (N : ℕ) (z : ℂ) : (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).natDegree ≤ 2 * N` |
| `apm_a95J03_clearedPoly_eval_eq` | a95J03 | `(a : ℤ → ℂ) (N : ℕ) (z w : ℂ) (hw : w ≠ 0) : (apm_a95J03_algPoly a N - Polynomial.C z * Polynomial.X ^ N).eval w = w ^ N * (((Finset.Icc (-(N : ℤ)) N).sum fun n => a n * w ^ n) - z)` |
| `apm_a95J03_fderiv_apply_one` | a95J03 | `(a : ℤ → ℂ) (N : ℕ) (t : ℝ) : (fderiv ℝ (apm_a95J03_trigPoly a N) t) 1 = (Finset.Icc (-(N : ℤ)) N).sum (fun n ↦ a n * (Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)) * (Complex.I * (n : ℂ))))` |
| `apm_a95J03_trigPoly_eq_laurent` | a95J03 | `(a : ℤ → ℂ) (N : ℕ) (t : ℝ) : apm_a95J03_trigPoly a N t = (Finset.Icc (-(N : ℤ)) N).sum fun n ↦ a n * Complex.exp (Complex.I * (t : ℂ)) ^ n` |
| `apm_a95J03_trigPoly_hasDerivAt` | a95J03 | `(a : ℤ → ℂ) (N : ℕ) (t : ℝ) : HasDerivAt (apm_a95J03_trigPoly a N) ((Finset.Icc (-(N : ℤ)) N).sum fun n ↦ a n * (Complex.exp (Complex.I * (n : ℂ) * (t : ℂ)) * (Complex.I * (n : ℂ)))) t` |
| `apm_a95J04_boundary_poles_finite` | a95J04 | `{D : Set ℂ} (hDcontains : closedBall (0 : ℂ) 1 ⊆ D) {f : ℂ → ℂ} (hmero : MeromorphicOn f D) : {z : ℂ \| z ∈ sphere (0 : ℂ) 1 ∧ meromorphicOrderAt f z < 0}.Finite` |
| `apm_a95J04_pole_mem_sphere_of_mem_closedBall` | a95J04 | `{f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) (hz : z ∈ closedBall (0 : ℂ) 1) (hpole : meromorphicOrderAt f z < 0) : z ∈ sphere (0 : ℂ) 1` |
| `apm_a96A07_isBounded_image_disk` | a96A07 | `(g : ℂ → ℂ) (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε))) : Bornology.IsBounded (g '' apm_a96A07_disk)` |
| `apm_a96A07_isConnected_image_disk` | a96A07 | `(g : ℂ → ℂ) (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε))) : IsConnected (g '' apm_a96A07_disk)` |
| `apm_a96A07_isOpen_image_disk` | a96A07 | `(g : ℂ → ℂ) (hg : ∃ ε > 0, DifferentiableOn ℂ g (closedBall 0 (1 + ε))) (hg_inj_circle : Set.InjOn g apm_a96A07_circle) : IsOpen (g '' apm_a96A07_disk)` |
| `apm_a96J03_compact_core` | a96J03 | `(g : ℝ → ℝ) (hg : HasCompactSupport g) (hgc : Continuous g) : Tendsto (fun t : ℝ => ∫ x : ℝ, \|g (x - t) - g x\|) (nhds 0) (nhds 0)` |
| `apm_a96J03_exists_compact_continuous_approx` | a96J03 | `(f : ℝ → ℝ) (hf : Integrable f volume) {e : ℝ} (he : 0 < e) : ∃ g : ℝ → ℝ, HasCompactSupport g ∧ Continuous g ∧ Integrable g volume ∧ (∫ x : ℝ, \|f x - g x\|) ≤ e` |
| `apm_a96J03_integral_abs_sub_translate` | a96J03 | `(f g : ℝ → ℝ) (t : ℝ) : (∫ x : ℝ, \|f (x - t) - g (x - t)\|) = ∫ x : ℝ, \|f x - g x\|` |
| `apm_a96J05_antitone_norm_le` | a96J05 | `{p q : ℝ≥0∞} (hpq : p ≤ q) (h : Lp ℝ q apm_a96J05_measure) (h' : Lp ℝ p apm_a96J05_measure) (heq : (h' : AEEqFun ℝ ℝ apm_a96J05_measure) = h) : ‖h'‖ ≤ ‖h‖` |
| `apm_a96J05_mem_iff_exists_Lp` | a96J05 | `{p q : ℝ≥0∞} (hpq : p ≤ q) (f : AEEqFun ℝ ℝ apm_a96J05_measure) : apm_a96J05_mem p q f ↔ ∃ k : Lp ℝ p apm_a96J05_measure, (k : AEEqFun ℝ ℝ apm_a96J05_measure) = f` |
| `apm_a96J05_norm_eq_Lp_norm` | a96J05 | `{p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) (f : AEEqFun ℝ ℝ apm_a96J05_measure) (k : Lp ℝ p apm_a96J05_measure) (hk : (k : AEEqFun ℝ ℝ apm_a96J05_measure) = f) : apm_a96J05_norm p q f = ‖k‖` |
| `apm_a96J06_coeff_top` | a96J06 | `(N : ℕ) (hN : 2 ≤ N) (c : ℕ → ℂ) : (apm_a96J06_poly N c).coeff N = c N` |
| `apm_a96J06_eval_poly` | a96J06 | `(N : ℕ) (c : ℕ → ℂ) (z : ℂ) : (apm_a96J06_poly N c).eval z = apm_a96J06_polynomial N c z` |
| `apm_a96J06_hasDerivAt_zero` | a96J06 | `(N : ℕ) (c : ℕ → ℂ) : HasDerivAt (apm_a96J06_polynomial N c) 1 0` |
| `apm_a96J06_rescaled_hasDerivAt_zero` | a96J06 | `(N : ℕ) (c : ℕ → ℂ) {r : ℝ} (hr : 0 < r) : HasDerivAt (fun z : ℂ => (r : ℂ)⁻¹ * apm_a96J06_polynomial N c ((r : ℂ) * z)) 1 0` |
| `apm_a96J09_coeff_tendsto_zero_of_contains_closed_disk` | a96J09 | `(D : Set ℂ) (hD_open : IsOpen D) (f : ℂ → ℂ) (hf : AnalyticOn ℂ f D) (hclosed : Metric.closedBall (0 : ℂ) 1 ⊆ D) : Tendsto (fun n : ℕ => ‖iteratedDeriv n f 0‖ / n.factorial) atTop (𝓝 0)` |
| `apm_a96J09_main` | a96J09 | `(D : Set ℂ) (hD_open : IsOpen D) (_hD_zero : (0 : ℂ) ∈ D) (f : ℂ → ℂ) (hf : AnalyticOn ℂ f D) (hlimsup : 0 < limsup (fun n : ℕ => ‖iteratedDeriv n f 0‖ / n.factorial) atTop) : ¬ Metric.closedBall (0 : ℂ) 1 ⊆ D` |
| `apm_a96J10_even_factors` | a96J10 | `(h : ℂ → ℂ) (hh : AnalyticOn ℂ h (Metric.ball (0:ℂ) 1)) (heven : ∀ z, ‖z‖ < 1 → h (-z) = h z) : ∃ g : ℂ → ℂ, AnalyticOn ℂ g (Metric.ball (0:ℂ) 1) ∧ ∀ z, ‖z‖ < 1 → g (z ^ 2) = h z` |
| `apm_a96J10_f_analytic` | a96J10 | `: AnalyticOn ℂ apm_a96J10_f (Metric.ball (0:ℂ) 1)` |
| `apm_a96J10_f_even` | a96J10 | `(z : ℂ) (hz : ‖z‖ < 1) : apm_a96J10_f (-z) = apm_a96J10_f z` |
| `apm_a96J10_main` | a96J10 | `: ∃ g : ℂ → ℂ, AnalyticOn ℂ g (Metric.ball (0:ℂ) 1) ∧ ∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 → g (z ^ 2) = z / (Complex.exp (2 * Real.pi * z) - 1) + z / 2` |
| `apm_a96J10_q_analytic` | a96J10 | `: AnalyticOn ℂ apm_a96J10_q univ` |
| `apm_a96J10_q_nonzero_on_ball` | a96J10 | `{z : ℂ} (hz : ‖z‖ < 1) : apm_a96J10_q ((2 * Real.pi : ℂ) * z) ≠ 0` |
| `apm_a96J10_q_of_ne` | a96J10 | `(z : ℂ) (hz0 : z ≠ 0) : apm_a96J10_q z = (Complex.exp z - 1) / z` |
| `apm_a97A01_abs_rademacher` | a97A01 | `(n : ℕ) (t : ℝ) : \|apm_a97A01_rademacher n t\| = 1` |
| `apm_a97A01_integrable_mul_rademacher` | a97A01 | `(f : ℝ → ℝ) (hf : MemLp f ⊤ apm_a97A01_measure) (n : ℕ) : Integrable (fun t ↦ f t * apm_a97A01_rademacher n t) apm_a97A01_measure` |
| `apm_a97A01_norm_integral_mul_rademacher_le` | a97A01 | `(g : ℝ → ℝ) (n : ℕ) : ‖∫ t, g t * apm_a97A01_rademacher n t ∂apm_a97A01_measure‖ ≤ ∫ t, \|g t\| ∂apm_a97A01_measure` |
| `apm_a97A01_rademacher_eq_one_of_mem_odd_cell` | a97A01 | `{n k : ℕ} {t : ℝ} (hn : n ≠ 1) (ht : t ≠ 1) (hk₀ : 1 ≤ k) (hk₁ : k ≤ 2 ^ n) (hkodd : Odd k) (htk : t ∈ Ico (((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ)) ((k : ℝ) / (2 ^ n : ℕ))) : apm_a97A01_rademacher n t = 1` |
| `apm_a97A01_rademacher_measurable` | a97A01 | `(n : ℕ) : Measurable (apm_a97A01_rademacher n)` |
| `apm_a97A02_continuousOn_average` | a97A02 | `(f : ℝ → ℂ) (hf : Integrable f apm_a97A02_measure) (h : ℝ) (hh : 0 < h) : ContinuousOn (apm_a97A02_average f h) (Set.Icc (0 : ℝ) 1)` |
| `apm_a97A02_integrable_of_memLp` | a97A02 | `{p : ENNReal} (hp : 1 ≤ p) {f : ℝ → ℂ} (hf : MemLp f p apm_a97A02_measure) : Integrable f apm_a97A02_measure` |
| `apm_a97A02_measure_Icc_le` | a97A02 | `(h t : ℝ) (_hh : 0 < h) : apm_a97A02_measure (Set.Icc (t - h) (t + h)) ≤ ENNReal.ofReal (2 * h)` |
| `apm_a97A05_cayley_maps_RHP_to_disk` | a97A05 | `(w : ℂ) (hw : 0 < w.re) : ‖(w - 1) / (w + 1)‖ < 1` |
| `apm_a97A05_main` | a97A05 | `(f : ℂ → ℂ) (hf : AnalyticOn ℂ f UHP) (M : ℝ) (hM : 0 ≤ M) (hbdd : ∀ z ∈ UHP, \|(f z).re\| ≤ M) : ∃ (g h : ℂ → ℂ) (Cg Ch : ℝ), AnalyticOn ℂ g UHP ∧ AnalyticOn ℂ h UHP ∧ (∀ z ∈ UHP, ‖g z‖ ≤ Cg) ∧ (∀ z ∈ UHP, ‖h z‖ ≤ Ch) ∧ (∀ z ∈ UHP, h z ≠ 0) ∧ (∀ z ∈ UHP, f z = g z / h z)` |
| `apm_a97A05_psi_analytic` | a97A05 | `(f : ℂ → ℂ) (hf : AnalyticOn ℂ f UHP) (M : ℝ) (hM : 0 ≤ M) (hbdd : ∀ z ∈ UHP, \|(f z).re\| ≤ M) : AnalyticOn ℂ (apm_a97A05_psi f M) UHP` |
| `apm_a97A05_psi_bdd` | a97A05 | `(f : ℂ → ℂ) (hf : AnalyticOn ℂ f UHP) (M : ℝ) (hM : 0 ≤ M) (hbdd : ∀ z ∈ UHP, \|(f z).re\| ≤ M) : ∀ z ∈ UHP, ‖apm_a97A05_psi f M z‖ < 1` |
| `apm_a97A05_shift_to_RHP` | a97A05 | `(f : ℂ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hbdd : ∀ z ∈ UHP, \|(f z).re\| ≤ M) : ∀ z ∈ UHP, 0 < ((f z) + (M + 1)).re` |
| `apm_a97A06_arc_exp_vanishes` | a97A06 | `: Tendsto (fun R : ℝ => ‖∫ θ in (0:ℝ)..π, (Complex.exp (2 * I * (R * Complex.exp (I * θ))) / (R * Complex.exp (I * θ)) ^ 2) * (I * R * Complex.exp (I * θ))‖) atTop (nhds 0)` |
| `apm_a97A06_arc_inv_eq_iPi` | a97A06 | `(R : ℝ) (hR : 0 < R) : ∫ θ in (0:ℝ)..π, (1 / (R * Complex.exp (I * θ))) * (I * R * Complex.exp (I * θ)) = I * π` |
| `apm_a97A06_arc_inv_sq_vanishes` | a97A06 | `: Tendsto (fun R : ℝ => ‖∫ θ in (0:ℝ)..π, (1 / (R * Complex.exp (I * θ)) ^ 2) * (I * R * Complex.exp (I * θ))‖) atTop (nhds 0)` |
| `apm_a97A06_F_analytic` | a97A06 | `: AnalyticOn ℂ apm_a97A06_F univ` |
| `apm_a97A06_F_continuousAt_zero` | a97A06 | `: ContinuousAt apm_a97A06_F 0` |
| `apm_a97A06_finite_identity` | a97A06 | `(R : ℝ) : (∫ x in (0 : ℝ)..R, Real.sinc x ^ 2) = (∫ x in (0 : ℝ)..(2 * R), Real.sinc x) - R * Real.sinc R ^ 2` |
| `apm_a97A06_integrable` | a97A06 | `: IntegrableOn (fun x : ℝ => (Real.sin x) ^ 2 / x ^ 2) (Set.Ioi 0) volume` |
| `apm_a97A06_main` | a97A06 | `: ∫ x in Set.Ioi (0:ℝ), (Real.sin x) ^ 2 / x ^ 2 = π / 2` |
| `apm_a97A06_q_deriv` | a97A06 | `(x : ℝ) : deriv apm_a97A06_q x = apm_a97A06_d x` |
| `apm_a97A06_q_hasDerivAt` | a97A06 | `(x : ℝ) : HasDerivAt apm_a97A06_q (apm_a97A06_d x) x` |
| `apm_a97A06_real_part` | a97A06 | `(x : ℝ) (hx : x ≠ 0) : (apm_a97A06_F (x : ℂ)).re = -2 * (Real.sin x) ^ 2 / x ^ 2` |
| `apm_a97A06_tendsto_finite_identity` | a97A06 | `: Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sinc x ^ 2) atTop (𝓝 (π / 2))` |
| `apm_a97A06_tendsto_q_atTop` | a97A06 | `: Tendsto apm_a97A06_q atTop (𝓝 0)` |
| `apm_a97A07_interpolates` | a97A07 | `(n : ℕ) (hn : 0 < n) (zs : Fin n → ℂ) (zs_distinct : Function.Injective zs) (f : ℂ → ℂ) (hf : AnalyticOn ℂ f univ) (R : ℝ) (hR : 0 < R) (hzs_in : ∀ k, ‖zs k‖ < R) (k : Fin n) : apm_a97A07_P n zs f (fun t => R * Complex.exp (2 * π * I * t)) (zs k) = f (zs k)` |
| `apm_a97A07_main` | a97A07 | `(n : ℕ) (hn : 0 < n) (zs : Fin n → ℂ) (zs_distinct : Function.Injective zs) (f : ℂ → ℂ) (hf : AnalyticOn ℂ f univ) (R : ℝ) (hR : 0 < R) (hzs_in : ∀ k, ‖zs k‖ < R) : ∃ P_poly : Polynomial ℂ, P_poly.natDegree ≤ n - 1 ∧ (∀ z : ℂ, apm_a97A07_P n zs f (fun t => R * Complex.exp (2 * π * I * t)) z = P_poly.aeval z) ∧ (∀ k : Fin n, P_poly.aeval (zs k) = f (zs k))` |
| `apm_a97A07_P_polynomial` | a97A07 | `(n : ℕ) (hn : 0 < n) (zs : Fin n → ℂ) (zs_distinct : Function.Injective zs) (f : ℂ → ℂ) (hf : AnalyticOn ℂ f univ) (R : ℝ) (hR : 0 < R) (hzs_in : ∀ k, ‖zs k‖ < R) : ∃ P_poly : Polynomial ℂ, P_poly.natDegree ≤ n - 1 ∧ ∀ z : ℂ, apm_a97A07_P n zs f (fun t => R * Complex.exp (2 * π * I * t)) z = P_poly.aeval z` |
| `apm_a97A07_Q_eval_zs` | a97A07 | `(zs : Fin n → ℂ) (k : Fin n) (zeta : ℂ) (hzeta : zeta ≠ zs k) : apm_a97A07_Q zs zeta (zs k) = (apm_a97A07_p zs).aeval zeta / (zeta - zs k)` |
| `apm_a97A07_Q_polynomial_in_z` | a97A07 | `(n : ℕ) (hn : 0 < n) (zs : Fin n → ℂ) (ζ : ℂ) : ∃ q : Polynomial ℂ, q.natDegree ≤ n - 1 ∧ ∀ z : ℂ, z ≠ ζ → q.aeval z = apm_a97A07_Q zs ζ z` |
| `apm_a97A08_count_inner` | a97A08 | `: (apm_a97A08_f.roots.filter (fun z => ‖z‖ < 3/2)).card = 1` |
| `apm_a97A08_count_outer` | a97A08 | `: (apm_a97A08_f.roots.filter (fun z => ‖z‖ < 2)).card = 5` |
| `apm_a97A08_main` | a97A08 | `: (apm_a97A08_f.roots.filter (fun z => ‖z‖ < 2)).card = 5 ∧ (apm_a97A08_f.roots.filter (fun z => 3/2 < ‖z‖ ∧ ‖z‖ < 2)).card = 4` |
| `apm_a97A08_no_zeros_inner` | a97A08 | `(z : ℂ) (hz : ‖z‖ = 3/2) : apm_a97A08_f.aeval z ≠ 0` |
| `apm_a97A08_no_zeros_outer` | a97A08 | `(z : ℂ) (hz : ‖z‖ = 2) : apm_a97A08_f.aeval z ≠ 0` |
| `apm_a97A08_rouche_inner` | a97A08 | `(z : ℂ) (hz : ‖z‖ = 3/2) : ‖z ^ 5 + 1‖ < ‖15 * z‖` |
| `apm_a97A08_rouche_outer` | a97A08 | `(z : ℂ) (hz : ‖z‖ = 2) : ‖15 * z + 1‖ < ‖z ^ 5‖` |
| `apm_a97J03_convolution_continuous` | a97J03 | `{p q : ℝ} (hpq : p.HolderConjugate q) {f g : ℝ → ℂ} (hf : MemLp f (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal q) volume) : Continuous (fun x ↦ ∫ y, f (x - y) * g y)` |
| `apm_a97J03_convolution_tendsto_zero` | a97J03 | `{p q : ℝ} (hpq : p.HolderConjugate q) {f g : ℝ → ℂ} (hf : MemLp f (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal q) volume) : Tendsto (fun x ↦ ∫ y, f (x - y) * g y) (cocompact ℝ) (nhds 0)` |
| `apm_a97J05_hasFPowerSeriesAt_div_sub_one` | a97J05 | `(A : ℂ) : HasFPowerSeriesAt (fun z : ℂ => A / (z - 1)) (FormalMultilinearSeries.ofScalars ℂ (fun _ => -A)) 0` |
| `apm_a97J05_remainder_update_continuousAt` | a97J05 | `(f g : ℂ → ℂ) (z₀ A : ℂ) (hg : AnalyticAt ℂ g z₀) (heq : ∀ᶠ z in 𝓝[≠] z₀, f z = A / (z - z₀) + g z) : ContinuousAt (Function.update (fun z => f z - A / (z - z₀)) z₀ (g z₀)) z₀` |
| `apm_a97J06_integrable` | a97J06 | `(t : ℝ) : Integrable (apm_a97J06_integrand t) volume` |
| `apm_a97J06_integral_eq_half_standard` | a97J06 | `(t : ℝ) : (∫ x in Ioi (0 : ℝ), apm_a97J06_integrand t x ∂volume) = (1 / 2 : ℝ) * ∫ u in Ioi (0 : ℝ), Real.cos (u * (2 * t)) / (1 + u ^ 2) ∂volume` |
| `apm_a97J06_integral_neg` | a97J06 | `(t : ℝ) : (∫ x in Ioi (0 : ℝ), apm_a97J06_integrand (-t) x ∂volume) = ∫ x in Ioi (0 : ℝ), apm_a97J06_integrand t x ∂volume` |
| `apm_a97J06_integral_zero` | a97J06 | `: ∫ x in Ioi (0 : ℝ), apm_a97J06_integrand 0 x ∂volume = Real.pi / 4` |
| `apm_a97j08_curveImage_compact` | a97J08 | `{γ : ℝ → ℂ} (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1)) : IsCompact (apm_a97j08_curveImage γ)` |
| `apm_a97j08_eventually_boundary_rouche` | a97J08 | `{D : Set ℂ} {γ : ℝ → ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hD_open : IsOpen D) (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1)) (hγD : apm_a97j08_curveImage γ ⊆ D) (hF_analytic : ∀ n, DifferentiableOn ℂ (F n) D) (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D) (hg_ne : ∀ z ∈ apm_a97j08_curveImage γ, g z ≠ 0) : ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ apm_a97j08_curveImage γ, ‖F n z - g z‖ < ‖g z‖` |
| `apm_a97j08_exists_boundary_margin` | a97J08 | `{γ : ℝ → ℂ} {g : ℂ → ℂ} (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1)) (hg_cont : ContinuousOn g (apm_a97j08_curveImage γ)) (hg_ne : ∀ z ∈ apm_a97j08_curveImage γ, g z ≠ 0) : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ apm_a97j08_curveImage γ, ε ≤ ‖g z‖` |
| `apm_a97j08_limit_continuousOn_curve` | a97J08 | `{D : Set ℂ} {γ : ℝ → ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hγD : apm_a97j08_curveImage γ ⊆ D) (hF_analytic : ∀ n, DifferentiableOn ℂ (F n) D) (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D) : ContinuousOn g (apm_a97j08_curveImage γ)` |
| `apm_a97j08_limit_differentiableOn` | a97J08 | `{D : Set ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hD_open : IsOpen D) (hF_analytic : ∀ n, DifferentiableOn ℂ (F n) D) (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D) : DifferentiableOn ℂ g D` |
| `apm_a98A02_inner_products_summable` | a98A02 | `{E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ℕ → E) (hv : Orthonormal ℝ v) (f : E) : Summable (fun n => ‖@inner ℝ E _ (v n) f‖ ^ 2)` |
| `apm_a98A02_inner_toLp_eq_integral` | a98A02 | `(g : ℕ → ℝ → ℝ) (M : ℝ) (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n))) (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → \|g n x\| ≤ M) (h : ℝ → ℝ) (hh : MemLp h 2 (volume.restrict (Icc (0 : ℝ) 1))) (n : ℕ) : @inner ℝ (Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1))) _ ((apm_a98A02_memLp_two g M hg_meas hg_bound n).toLp (g n)) (hh.toLp h) = ∫ x in Icc (0 : ℝ) 1, g n x * h x ∂volume` |
| `apm_a98A02_integral_tendsto_zero_of_memLp_two` | a98A02 | `(g : ℕ → ℝ → ℝ) (M : ℝ) (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n))) (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → \|g n x\| ≤ M) (hg_orthonormal : ∀ n m, (∫ x in Icc (0 : ℝ) 1, g n x * g m x ∂volume) = if n = m then 1 else 0) (h : ℝ → ℝ) (hh : MemLp h 2 (volume.restrict (Icc (0 : ℝ) 1))) : Tendsto (fun n => ∫ x in Icc (0 : ℝ) 1, g n x * h x ∂volume) atTop (𝓝 0)` |
| `apm_a98A02_memLp_two` | a98A02 | `(g : ℕ → ℝ → ℝ) (M : ℝ) (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n))) (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → \|g n x\| ≤ M) (n : ℕ) : MemLp (g n) 2 (volume.restrict (Icc (0 : ℝ) 1))` |
| `apm_a98A02_orthonormal_toLp` | a98A02 | `(g : ℕ → ℝ → ℝ) (M : ℝ) (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n))) (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → \|g n x\| ≤ M) (hg_orthonormal : ∀ n m, (∫ x in Icc (0 : ℝ) 1, g n x * g m x ∂volume) = if n = m then 1 else 0) : Orthonormal ℝ (fun n => (apm_a98A02_memLp_two g M hg_meas hg_bound n).toLp (g n))` |
| `apm_a98a03_exists_fine_uniform_partition` | a98A03 | `{δ : ℝ} (hδ : 0 < δ) : ∃ (n : ℕ) (hn : 0 < n) (x : Fin (n + 1) → ℝ), x 0 = 0 ∧ x (Fin.last n) = 1 ∧ StrictMono x ∧ ∀ i : Fin n, x i.succ - x i.castSucc < δ` |
| `apm_a98a03_exists_mvt_tag` | a98A03 | `{f f' : ℝ → ℝ} {a b : ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_deriv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b) : ∃ t ∈ Ioo a b, f b - f a = f' t * (b - a)` |
| `apm_a98a03_sum_adjacent_sub` | a98A03 | `{G : Type*} [AddCommGroup G] (n : ℕ) (f : ℝ → G) (x : Fin (n + 1) → ℝ) : (∑ i : Fin n, (f (x i.succ) - f (x i.castSucc))) = f (x (Fin.last n)) - f (x 0)` |
| `apm_a98a04_spike_eq_zero_of_not_mem` | a98A04 | `{a b x : ℝ} (hx : x ∉ Ioo a b) : apm_a98a04_spike a b x = 0` |
| `apm_a98a04_spike_measurable` | a98A04 | `(a b : ℝ) : Measurable (apm_a98a04_spike a b)` |
| `apm_a98a04_spike_nonneg` | a98A04 | `(a b x : ℝ) : 0 ≤ apm_a98a04_spike a b x` |
| `apm_a98a04_spike_pos_iff` | a98A04 | `{a b x : ℝ} (hab : a < b) : 0 < apm_a98a04_spike a b x ↔ x ∈ Ioo a b` |
| `apm_a98a04_spike_pos_set` | a98A04 | `{a b : ℝ} (hab : a < b) : {x : ℝ \| 0 < apm_a98a04_spike a b x} = Ioo a b` |
| `apm_a98a04_spike_pos_set_measure_pos` | a98A04 | `{a b : ℝ} (hab : a < b) : 0 < volume {x : ℝ \| 0 < apm_a98a04_spike a b x}` |
| `apm_a98a05_hasDerivAt_primitive` | a98A05 | `{x : ℝ} (hx : 0 ≤ x) : HasDerivAt apm_a98a05_primitive (1 / (1 + x ^ 3)) x` |
| `apm_a98a05_partial_fractions` | a98A05 | `{x : ℝ} (hx : 0 ≤ x) : 0 < x + 1 ∧ 0 < x ^ 2 - x + 1 ∧ 1 / (1 + x ^ 3) = (1 / 3 : ℝ) / (x + 1) + (2 - x) / (3 * (x ^ 2 - x + 1))` |
| `apm_a98a05_tendsto_primitive` | a98A05 | `: Tendsto apm_a98a05_primitive atTop (nhds (Real.sqrt 3 * Real.pi / 6))` |
| `apm_a98A07_differentiableOn_of_locallyUniform` | a98A07 | `{f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hf : ∀ n, DifferentiableOn ℂ (f n) (ball 0 1)) (hconv : TendstoLocallyUniformlyOn f g atTop (ball 0 1)) : DifferentiableOn ℂ g (ball 0 1)` |
| `apm_a98A07_log_ratio_neg` | a98A07 | `{t : ℝ} (ht : 0 < t) (htop : t < 2 * Real.pi) : Real.log (t / (4 * Real.pi)) < 0` |
| `apm_a98A07_majorant_measurable` | a98A07 | `: Measurable apm_a98A07_majorant` |
| `apm_a98A07_majorant_pos` | a98A07 | `{t : ℝ} (ht : 0 < t) (htop : t < 2 * Real.pi) : 0 < apm_a98A07_majorant t` |
| `apm_a98j01_homeomorph_of_compact_to_T2` | a98J01 | `{X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {g : X → Y} (hcompact : IsCompact (Set.univ : Set X)) (hg : Continuous g) (hbij : Function.Bijective g) : ∃ h : X ≃ₜ Y, (h : X → Y) = g` |
| `apm_a98j01_polish_refinement` | a98J01 | `{f : ℝ → ℝ} (hf : Measurable f) : ∃ t' : TopologicalSpace ℝ, t' ≤ (PseudoMetricSpace.toUniformSpace.toTopologicalSpace : TopologicalSpace ℝ) ∧ @Continuous ℝ ℝ t' (PseudoMetricSpace.toUniformSpace.toTopologicalSpace : TopologicalSpace ℝ) f ∧ @PolishSpace ℝ t' ∧ @borel ℝ t' = @borel ℝ (PseudoMetricSpace.toUniformSpace.toTopologicalSpace : TopologicalSpace ℝ)` |
| `apm_a98J02_deriv_eq_derivWithin_ae` | a98J02 | `(f : ℝ → ℝ) : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1), deriv f t = derivWithin f (Set.Icc 0 1) t` |
| `apm_a98J02_integrableOn_deriv_sq` | a98J02 | `(f : ℝ → ℝ) (hderiv : IntegrableOn (fun x : ℝ => \|derivWithin f (Set.Icc 0 1) x\| ^ 2) (Set.Icc 0 1)) : IntegrableOn (fun x : ℝ => \|deriv f x\| ^ 2) (Set.Icc 0 1)` |
| `apm_a98J02_sub_eq_integral_deriv` | a98J02 | `(f : ℝ → ℝ) (hf : AbsolutelyContinuousOnInterval f 0 1) {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x ≤ 1) : f x - f y = ∫ t in y..x, deriv f t` |
| `apm_a98J02_tendsto_integral_deriv_sq_symmetric` | a98J02 | `(f : ℝ → ℝ) (hderiv : IntegrableOn (fun x : ℝ => \|derivWithin f (Set.Icc 0 1) x\| ^ 2) (Set.Icc 0 1)) (b : ℝ) : Filter.Tendsto (fun δ : ℝ => ∫ x in Set.Icc (b - δ) (b + δ), \|deriv f x\| ^ 2 ∂volume.restrict (Set.Icc (0 : ℝ) 1)) (nhds 0) (nhds 0)` |
| `apm_a99J03_counterexample_integrableOn` | a99J03 | `: IntegrableOn apm_a99J03_counterexample (Ioi 0)` |
| `apm_a99J03_endpoint_kernel_not_integrable` | a99J03 | `: ¬ IntegrableOn (fun x : ℝ => 1 / (x * (x + 1))) (Ioo 0 1) volume` |
| `apm_a99J03_hasDerivAt_kernel` | a99J03 | `(f : ℝ → ℝ) {x y : ℝ} (hxy : x + y ≠ 0) : HasDerivAt (fun z : ℝ ↦ f y / (z + y)) (-f y / (x + y) ^ 2) x` |
| `apm_a99J03_kernel_deriv_bound` | a99J03 | `(f : ℝ → ℝ) {x z y : ℝ} (hx : 0 < x) (hz : z ∈ Ioo (x / 2) (3 * x / 2)) (hy : 0 < y) : \|(-f y) / (z + y) ^ 2\| ≤ \|f y\| / (x / 2) ^ 2` |
| `apm_a99J04_mu1_eq_ac13` | a99J04 | `: apm_a99J04_mu1 = apm_a99J04_acPart apm_a99J04_mu3 apm_a99J04_f13` |
| `apm_a99J04_mu1_split` | a99J04 | `: apm_a99J04_mu1 = apm_a99J04_acPart apm_a99J04_mu2 apm_a99J04_f12 + apm_a99J04_nu12` |
| `apm_a99J04_mu2_eq_ac21` | a99J04 | `: apm_a99J04_mu2 = apm_a99J04_acPart apm_a99J04_mu1 apm_a99J04_f21` |
| `apm_a99J04_mu2_eq_ac23` | a99J04 | `: apm_a99J04_mu2 = apm_a99J04_acPart apm_a99J04_mu3 apm_a99J04_f23` |
| `apm_a99J04_mu2_eq_mu1_restrict` | a99J04 | `: apm_a99J04_mu2 = apm_a99J04_mu1.restrict (Ioo 0 1)` |
| `apm_a99J04_mu3_eq_ac31` | a99J04 | `: apm_a99J04_mu3 = apm_a99J04_acPart apm_a99J04_mu1 apm_a99J04_f31` |
| `apm_a99J04_mu3_restrict_eq_ac32` | a99J04 | `: apm_a99J04_mu3.restrict (Ioo 0 1) = apm_a99J04_acPart apm_a99J04_mu2 apm_a99J04_f32` |
| `apm_a99J04_mu3_split` | a99J04 | `: apm_a99J04_mu3 = apm_a99J04_acPart apm_a99J04_mu2 apm_a99J04_f32 + apm_a99J04_nu32` |
| `apm_a99J04_restrict_compl_mutuallySingular` | a99J04 | `(s : Set ℝ) (hs : MeasurableSet s) (mu nu : Measure ℝ) : mu.restrict sᶜ ⟂ₘ nu.restrict s` |
| `apm_a99J04_zero_mutuallySingular` | a99J04 | `(μ : Measure ℝ) : (0 : Measure ℝ) ⟂ₘ μ` |
| `apm_a99J05_ae_tendsto_zero_of_summable_l1Norm` | a99J05 | `(f : ℕ → ℝ → ℝ) (hint : ∀ n, Integrable (f n) apm_a99J05_measure) (hsum : Summable (fun n ↦ apm_a99J05_l1Norm (f n))) : ∀ᵐ x ∂apm_a99J05_measure, Tendsto (fun n ↦ f n x) atTop (𝓝 0)` |
| `apm_a99J05_index_lt_stage_sq` | a99J05 | `(k : ℕ) (_hk : 1 ≤ k) : k < apm_a99J05_stage k ^ 2` |
| `apm_a99J05_integral_typewriter1d` | a99J05 | `(k : ℕ) : ∫ x in Icc (0 : ℝ) 1, apm_a99J05_typewriter1d k x ∂volume = Real.sqrt (apm_a99J05_stage k) / apm_a99J05_stage k` |
| `apm_a99J05_integral_typewriter1d_tendsto` | a99J05 | `: Tendsto (fun k => ∫ x in Icc (0 : ℝ) 1, apm_a99J05_typewriter1d k x ∂volume) atTop (nhds 0)` |
| `apm_a99J05_position_lt_stage` | a99J05 | `(k : ℕ) : apm_a99J05_position k < apm_a99J05_stage k` |
| `apm_a99J05_stage_tendsto_atTop` | a99J05 | `: Tendsto apm_a99J05_stage atTop atTop` |
| `apm_a99J05_summable_l1Norm_of_geometric_bound` | a99J05 | `(f : ℕ → ℝ → ℝ) (hbound : ∀ n, apm_a99J05_l1Norm (f n) ≤ (2 : ℝ)⁻¹ ^ n) : Summable (fun n ↦ apm_a99J05_l1Norm (f n))` |
| `apm_a99J05_typewriter1d_integrable` | a99J05 | `(k : ℕ) : IntegrableOn (apm_a99J05_typewriter1d k) (Icc (0 : ℝ) 1) volume` |
| `apm_a99J05_typewriter1d_nonneg` | a99J05 | `(k : ℕ) (x : ℝ) : 0 ≤ apm_a99J05_typewriter1d k x` |
| `apm_a99j06_exists_continuous_log` | a99J06 | `{Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩnonempty : Ω.Nonempty) (hΩsc : IsSimplyConnected Ω) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) (hf0 : ∀ z ∈ Ω, f z ≠ 0) : ∃ G : C(Ω, ℂ), ∀ z : Ω, f z = Complex.exp (G z)` |
| `apm_a99j06_exists_log_of_logDeriv_exact` | a99J06 | `{Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩnonempty : Ω.Nonempty) (hΩsc : IsSimplyConnected Ω) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) (hf0 : ∀ z ∈ Ω, f z ≠ 0) (hexact : Complex.IsExactOn (fun z ↦ deriv f z / f z) Ω) : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ Ω, f z = Complex.exp (g z)` |
| `apm_a99j06_logDeriv_differentiableOn` | a99J06 | `{Ω : Set ℂ} (hΩopen : IsOpen Ω) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) (hf0 : ∀ z ∈ Ω, f z ≠ 0) : DifferentiableOn ℂ (fun z ↦ deriv f z / f z) Ω` |
| `apm_a99J07_eval_le_supNorm` | a99J07 | `(p : Polynomial ℂ) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖p.eval z‖ ≤ a99J07SupNormUnitDisk p` |
| `apm_a99J07_poly_le_boundary` | a99J07 | `(q : Polynomial ℂ) {u : ℂ} (hu : ‖u‖ ≤ 1) : ∃ v : ℂ, ‖v‖ = 1 ∧ ‖q.eval u‖ ≤ ‖q.eval v‖` |
| `apm_a99J07_reflect_boundary` | a99J07 | `(p : Polynomial ℂ) (N : ℕ) (hd : p.natDegree ≤ N) {v : ℂ} (hv : ‖v‖ = 1) : ‖(p.reflect N).eval v‖ ≤ a99J07SupNormUnitDisk p` |
| `apm_a99J07_supNorm_bddAbove` | a99J07 | `(p : Polynomial ℂ) : BddAbove {r : ℝ \| ∃ z : ℂ, ‖z‖ ≤ 1 ∧ r = ‖p.eval z‖}` |
| `apm_a99J08_corner_zero` | a99J08 | `(g : ℂ → ℂ) (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk)) (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0) (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0) : g 0 = 0` |
| `apm_a99J08_real_mem_closure_upperHalfDisk` | a99J08 | `{x : ℝ} (hx : \|x\| < 1) : (x : ℂ) ∈ closure apm_a99J08_upperHalfDisk` |
| `apm_a99J08_sq_im_eq_zero_of_im_eq_zero` | a99J08 | `(z : ℂ) (hz : z.im = 0) : (z ^ 2).im = 0` |
| `apm_a99J08_sq_im_eq_zero_of_re_eq_zero` | a99J08 | `(z : ℂ) (hz : z.re = 0) : (z ^ 2).im = 0` |
| `apm_a99J08_sq_real_on_diameter` | a99J08 | `(g : ℂ → ℂ) (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk)) (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0) (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0) {x : ℝ} (hx₁ : -1 < x) (hx₂ : x < 1) : ((g x) ^ 2).im = 0` |
| `apm_a99J08_sq_real_on_punctured_diameter` | a99J08 | `(g : ℂ → ℂ) (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0) (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0) {x : ℝ} (hx₁ : -1 < x) (hx₂ : x < 1) (hx₀ : x ≠ 0) : ((g x) ^ 2).im = 0` |
| `apm_a99J08_sq_regular` | a99J08 | `(g : ℂ → ℂ) (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk)) (hgholo : DifferentiableOn ℂ g apm_a99J08_upperHalfDisk) : ContinuousOn (fun z => g z ^ 2) (closure apm_a99J08_upperHalfDisk) ∧ DifferentiableOn ℂ (fun z => g z ^ 2) apm_a99J08_upperHalfDisk` |
| `apm_a99j09_deriv_bound_integrable` | a99J09 | `(f : ℝ → ℂ) (p : ℝ) (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Ici (0 : ℝ)))) {a : ℝ} (ha : 0 < a) : Integrable (fun t : ℝ => ‖f t‖ * (t * Real.exp (-a * t))) (volume.restrict (Ici (0 : ℝ)))` |
| `apm_a99j09_integrand_integrable` | a99J09 | `(f : ℝ → ℂ) (p : ℝ) (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Ici (0 : ℝ)))) {z : ℂ} (hz : 0 < z.re) : Integrable (fun t => f t * Complex.exp (-(t : ℂ) * z)) (volume.restrict (Ici (0 : ℝ)))` |
| `apm_a99j09_norm_kernel` | a99J09 | `(z : ℂ) (t : ℝ) : ‖Complex.exp (-(t : ℂ) * z)‖ = Real.exp (-z.re * t)` |
| `apm_a99J10_integrable_rpow_neg_half` | a99J10 | `: IntegrableOn (fun x : ℝ => x ^ (-(1 : ℝ) / 2)) (Ioo 0 (Real.pi / 2))` |
| `apm_a99J10_polar_bound` | a99J10 | `(f : ℂ → ℂ) (hbound : ∀ z ∈ ball (0 : ℂ) 1, z.im ≠ 0 → ‖f z‖ ≤ Real.rpow \|z.im\| (-(1 : ℝ) / 2)) {r θ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hsin : Real.sin θ ≠ 0) : ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ Real.rpow \|r * Real.sin θ\| (-(1 : ℝ) / 2)` |
| `apm_a99J10_polar_bound_uniform` | a99J10 | `(f : ℂ → ℂ) (hbound : ∀ z ∈ ball (0 : ℂ) 1, z.im ≠ 0 → ‖f z‖ ≤ Real.rpow \|z.im\| (-(1 : ℝ) / 2)) {r θ : ℝ} (hr : (1 : ℝ) / 2 ≤ r) (hr1 : r < 1) (hsin : Real.sin θ ≠ 0) : ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ Real.rpow ((1 : ℝ) / 2) (-(1 : ℝ) / 2) * Real.rpow \|Real.sin θ\| (-(1 : ℝ) / 2)` |
| `apm_a99J10_polar_im` | a99J10 | `(r θ : ℝ) : (((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im) = r * Real.sin θ` |
| `apm_a99J10_polar_mem_ball` | a99J10 | `{r θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ ball (0 : ℂ) 1` |
| `apm_a99J10_sin_rpow_le_first_quadrant` | a99J10 | `{x : ℝ} (hx0 : 0 < x) (hxpi : x ≤ Real.pi / 2) : Real.rpow \|Real.sin x\| (-(1 : ℝ) / 2) ≤ Real.rpow (2 / Real.pi * x) (-(1 : ℝ) / 2)` |
| `apm_aunk04_growth_cauchy_bound` | aunk04 | `(f : ℂ → ℂ) (A B m : ℝ) (hf : Differentiable ℂ f) (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ A + B * Real.rpow ‖z‖ m) (k : ℕ) {R : ℝ} (hR : 0 < R) : ‖iteratedDeriv k f 0‖ ≤ k.factorial * (A + B * Real.rpow R m) / R ^ k` |
| `apm_aunk04_no_roots_in_unitDisk` | aunk04 | `: (apm_aunk04_polynomial.roots.filter (fun z => ‖z‖ < 1)).card = 0` |
| `apm_aunk04_rouche_bound` | aunk04 | `(z : ℂ) (hz : ‖z‖ = 1) : ‖Polynomial.eval z apm_aunk04_remainder‖ < ‖Polynomial.eval z (Polynomial.C 6 : ℂ[X])‖` |
| `apm_b00j01_finiteField_card_aut` | b00J01 | `[Fact (Nat.Prime 13)] (M : Type*) [Field M] [Algebra (ZMod 13) M] [IsSplittingField (ZMod 13) M (apm_b00j01_poly (ZMod 13))] : Nat.card (M ≃ₐ[ZMod 13] M) = Module.finrank (ZMod 13) M` |
| `apm_b00j01_finiteField_isGalois` | b00J01 | `[Fact (Nat.Prime 13)] (M : Type*) [Field M] [Algebra (ZMod 13) M] [IsSplittingField (ZMod 13) M (apm_b00j01_poly (ZMod 13))] : IsGalois (ZMod 13) M` |
| `apm_b00j01_irreducible_mod13` | b00J01 | `: Irreducible (apm_b00j01_poly (ZMod 13))` |
| `apm_b00j01_not_isRoot_mod13` | b00J01 | `(x : ZMod 13) : ¬IsRoot (apm_b00j01_poly (ZMod 13)) x` |
| `apm_b00j01_separable_mod13` | b00J01 | `: (apm_b00j01_poly (ZMod 13)).Separable` |
| `apm_b00j01_seven_not_cube_mod13` | b00J01 | `: ∀ x : ZMod 13, x ^ 3 ≠ 7` |
| `apm_b00j01_three_dvd_finiteField_card_aut` | b00J01 | `[Fact (Nat.Prime 13)] (M : Type*) [Field M] [Algebra (ZMod 13) M] [IsSplittingField (ZMod 13) M (apm_b00j01_poly (ZMod 13))] : 3 ∣ Nat.card (M ≃ₐ[ZMod 13] M)` |
| `apm_b00j01_three_dvd_finiteField_finrank` | b00J01 | `[Fact (Nat.Prime 13)] (M : Type*) [Field M] [Algebra (ZMod 13) M] [IsSplittingField (ZMod 13) M (apm_b00j01_poly (ZMod 13))] : 3 ∣ Module.finrank (ZMod 13) M` |
| `apm_b00j03_commutator_ne_bot` | b00J03 | `{G : Type*} [Group G] (hG : ∃ x y : G, x * y ≠ y * x) : commutator G ≠ ⊥` |
| `apm_b00j03_eq_of_le_center_of_prime_card` | b00J03 | `{p : ℕ} {G : Type*} [Group G] [Finite G] (hp : Nat.Prime p) (hcard : Nat.card (Subgroup.center G) = p) (hle : commutator G ≤ Subgroup.center G) (hne : commutator G ≠ ⊥) : Subgroup.center G = commutator G` |
| `apm_b00J04_common_denom_of_fg_submodule` | b00J04 | `(R F : Type*) [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F] (M : Submodule R F) (hfg : M.FG) : ∃ r : R, r ≠ 0 ∧ ∀ m ∈ M, r • m ∈ Set.range (algebraMap R F)` |
| `apm_b00J04_common_denom_of_finite_subalgebra` | b00J04 | `(R F : Type*) [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F] (S : Subalgebra R F) (hfinite : Module.Finite R S) : ∃ r : R, r ≠ 0 ∧ ∀ s : S, r • (s : F) ∈ Set.range (algebraMap R F)` |
| `apm_b00J04_exists_reduced_fraction` | b00J04 | `(R F : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field F] [Algebra R F] [IsFractionRing R F] (x : F) : ∃ a b : R, b ≠ 0 ∧ x = algebraMap R F a / algebraMap R F b ∧ IsRelPrime a b` |
| `apm_b00J04_first_conjunct` | b00J04 | `(R F : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field F] [Algebra R F] [IsFractionRing R F] (S : Subalgebra R F) : ∀ alpha : S, ∃ a b : R, b ≠ 0 ∧ (alpha : F) = algebraMap R F a / algebraMap R F b ∧ (algebraMap R F b)⁻¹ ∈ S` |
| `apm_b00J04_inv_den_mem` | b00J04 | `(R F : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field F] [Algebra R F] [IsFractionRing R F] (S : Subalgebra R F) (alpha : S) (a b : R) (hb : b ≠ 0) (halpha : (alpha : F) = algebraMap R F a / algebraMap R F b) (hab : IsRelPrime a b) : (algebraMap R F b)⁻¹ ∈ S` |
| `apm_b01A02_exists_normal_card_85` | b01A02 | `(G : Type*) [Group G] [Fintype G] (hG : Nat.card G = 255) : ∃ H : Subgroup G, H.Normal ∧ Nat.card H = 85` |
| `apm_b01A02_normal_of_smallest_prime_index` | b01A02 | `(G : Type*) [Group G] [Fintype G] (p : ℕ) (H : Subgroup G) (hp : apmSmallestPrimeDivisor p (Fintype.card G)) (hindex : H.index = p) : H.Normal` |
| `apm_b01A02_sylow17_normal_of_card_255` | b01A02 | `(G : Type*) [Group G] [Fintype G] (hG : Nat.card G = 255) (S : Sylow 17 G) : S.toSubgroup.Normal ∧ Nat.card S = 17` |
| `apm_b01A04_aut_mulEquiv_zmod_three` | b01A04 | `(K : Type*) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] [IsGalois ℚ K] (hfin : Module.finrank ℚ K = 3) : Nonempty ((K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 3))` |
| `apm_b01A04_isGaloisGroup_multiplicative_prod_iff` | b01A04 | `(A B : Type) [AddGroup A] [AddGroup B] : apm_b01A04_isGaloisGroup (Multiplicative (A × B)) ↔ apm_b01A04_isGaloisGroup (Multiplicative A × Multiplicative B)` |
| `apm_b01A04_isGaloisGroup_of_mulEquiv` | b01A04 | `{G H : Type} [Group G] [Group H] (hG : apm_b01A04_isGaloisGroup G) (e : G ≃* H) : apm_b01A04_isGaloisGroup H` |
| `apm_b01j01_prime_dvd_abelianization` | b01J01 | `{G : Type} [Group G] [Finite G] (H : Subgroup G) {p : ℕ} (hp : p.Prime) (hpH : p ∣ Nat.card H) (hpHcomm : ¬ p ∣ Nat.card ↥(H ⊓ commutator G)) : p ∣ Nat.card (G ⧸ commutator G)` |
| `apm_b01j01_prime_dvd_quotient` | b01J01 | `{G : Type} [Group G] [Finite G] (H K : Subgroup G) [K.Normal] {p : ℕ} (hp : p.Prime) (hpH : p ∣ Nat.card H) (hpHK : ¬ p ∣ Nat.card ↑(H ⊓ K)) : p ∣ Nat.card (G ⧸ K)` |
| `apm_b01j01_sylowSubgroupsIn_subset_traces` | b01J01 | `{G : Type} [Group G] (p : ℕ) (K : Subgroup G) : apm_b01J01_sylowSubgroupsIn p K ⊆ apm_b01J01_sylowTraces p K` |
| `apm_b01J03_selfNormalizer_count` | b01J03 | `(G : Type*) [Group G] [Finite G] (p : ℕ) (hp : p.Prime) (P : Sylow p G) (hself : normalizer (P : Subgroup G) = (P : Subgroup G)) : Nat.card (Sylow p G) = P.index ∧ ¬p ∣ P.index` |
| `apm_b03J01_isZGroup_of_twinPrime_card` | b03J01 | `(G : Type*) [Group G] [Fintype G] (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (hcard : Fintype.card G = p * (p + 2)) : IsZGroup G` |
| `apm_b03J01_sylow_normal_of_not_dvd_card` | b03J01 | `(G : Type*) [Group G] [Fintype G] (q : ℕ) (hq : q.Prime) (hqdvd : ¬q ∣ Fintype.card G) (Q : Sylow q G) : (↑Q : Subgroup G).Normal` |
| `apm_b03J01_twinPrime_squarefree` | b03J01 | `(p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) : Squarefree (p * (p + 2))` |
| `apm_b90A01_exists_faithful_sylow_alternating` | b90A01 | `{G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (p k : ℕ) (hp : p.Prime) (hk : Nat.card (Sylow p G) = k) (hk1 : 1 < k) : ∃ ψ : G →* alternatingGroup (Fin k), Function.Injective ψ` |
| `apm_b90A01_exists_faithful_sylow_perm` | b90A01 | `{G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (p k : ℕ) (hp : p.Prime) (hk : Nat.card (Sylow p G) = k) (hk1 : 1 < k) : ∃ φ : G →* Equiv.Perm (Fin k), Function.Injective φ` |
| `apm_b90A01_factor_faithful_through_alternating` | b90A01 | `{G α : Type*} [Group G] [IsSimpleGroup G] [Fintype α] [DecidableEq α] (φ : G →* Equiv.Perm α) (hφ : Function.Injective φ) (hnc : ∃ a b : G, a * b ≠ b * a) : ∃ ψ : G →* alternatingGroup α, Function.Injective ψ` |
| `apm_b90A01_not_commutative_of_multiple_sylow` | b90A01 | `{G : Type*} [Group G] [Finite G] (p : ℕ) (hp : p.Prime) (hk1 : 1 < Nat.card (Sylow p G)) : ∃ a b : G, a * b ≠ b * a` |
| `apm_b90A01_perm_fin_of_card` | b90A01 | `{G α : Type*} [Group G] [Finite α] {k : ℕ} (hk : Nat.card α = k) (φ : G →* Equiv.Perm α) (hφ : Function.Injective φ) : ∃ ψ : G →* Equiv.Perm (Fin k), Function.Injective ψ` |
| `apm_b90A01_sylow_action_faithful` | b90A01 | `{G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (p : ℕ) (hp : p.Prime) (hk1 : 1 < Nat.card (Sylow p G)) : Function.Injective (MulAction.toPermHom G (Sylow p G))` |
| `apm_b90a02_rat_to_int_eq_zero` | b90A02 | `(f : ℚ →ₗ[ℤ] ℤ) (q : ℚ) : f q = 0` |
| `apm_b90a03_exists_intermediateField` | b90A03 | `(K F : Type) [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F] (p q n m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hn : 1 < n) (hm : 1 < m) (hdegree : Module.finrank K F = p ^ n * q ^ m) : ∃ L : IntermediateField K F, L ≠ ⊥ ∧ L ≠ ⊤ ∧ Module.finrank (↥L) F = p ^ n` |
| `apm_b90a03_factorization` | b90A03 | `(p q n m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : (p ^ n * q ^ m).factorization p = n` |
| `apm_b90a03_fixedField_eq_of_degree_singleton` | b90A03 | `(K F : Type) [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F] (p q n m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hdegree : Module.finrank K F = p ^ n * q ^ m) (L : IntermediateField K F) (hunique : ({L' : IntermediateField K F \| Module.finrank (↥L') F = p ^ n} : Set (IntermediateField K F)) = {L}) (P : Sylow p Gal(F/K)) : IntermediateField.fixedField (P : Subgroup Gal(F/K)) = L` |
| `apm_b90a03_sylow_card` | b90A03 | `(K F : Type) [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F] (p q n m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hdegree : Module.finrank K F = p ^ n * q ^ m) (P : Sylow p Gal(F/K)) : Nat.card P = p ^ n` |
| `apm_b93a01_abelian_of_normal_prime_factors` | b93A01 | `(G : Type) [Group G] [Fintype G] (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hcard : Fintype.card G = p * q) (P Q : Subgroup G) (hPn : P.Normal) (hQn : Q.Normal) (hPcard : Nat.card P = p) (hQcard : Nat.card Q = q) : ∀ a b : G, a * b = b * a` |
| `apm_b93a01_embeds_fin_of_faithful_action` | b93A01 | `(G α : Type) [Group G] [MulAction G α] [Fintype α] (n : ℕ) (hcard : Fintype.card α = n) (hinj : Function.Injective (MulAction.toPermHom G α)) : apm_b93a01_embeds G (Equiv.Perm (Fin n))` |
| `apm_b93a03_flat_addEquiv` | b93A03 | `{M N : Type} [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) : apm_b93a03_flat M ↔ apm_b93a03_flat N` |
| `apm_b93a03_flat_int` | b93A03 | `: apm_b93a03_flat ℤ` |
| `apm_b93a03_flat_of_addEquiv` | b93A03 | `{M N : Type} [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) : apm_b93a03_flat M → apm_b93a03_flat N` |
| `apm_b93J01_card_A4` | b93J01 | `: Fintype.card (alternatingGroup (Fin 4)) = 12` |
| `apm_b93J01_card_Q8` | b93J01 | `: Fintype.card (QuaternionGroup 2) = 8` |
| `apm_b93J01_card_S3` | b93J01 | `: Fintype.card (Equiv.Perm (Fin 3)) = 2 * 3` |
| `apm_b93J01_lagrange` | b93J01 | `(G : Type*) [Group G] [Fintype G] (H : Subgroup G) : Nat.card H ∣ Fintype.card G` |
| `apm_b93J01_not_isCyclic_S3` | b93J01 | `: ¬IsCyclic (Equiv.Perm (Fin 3))` |
| `apm_b93J01_Q8_not_commutative` | b93J01 | `: (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠ QuaternionGroup.xa 0 * QuaternionGroup.a 1` |
| `apm_b93J01_Q8_not_equiv_ZMod4_prod_ZMod2` | b93J01 | `: ¬Nonempty (QuaternionGroup 2 ≃* Multiplicative (ZMod 4 × ZMod 2))` |
| `apm_b93J01_Q8_not_equiv_ZMod8` | b93J01 | `: ¬Nonempty (QuaternionGroup 2 ≃* Multiplicative (ZMod 8))` |
| `apm_b93J01_Q8_not_mulEquiv_commutative` | b93J01 | `(A : Type*) [CommGroup A] : ¬Nonempty (QuaternionGroup 2 ≃* A)` |
| `apm_b93j02_intPolynomial_not_pid` | b93J02 | `: ¬IsPrincipalIdealRing (Polynomial ℤ)` |
| `apm_b93j02_norm_eq_two_impossible` | b93J02 | `(z : Zsqrtd (-5)) : z.norm ≠ 2` |
| `apm_b93j02_pid_implies_ufd` | b93J02 | `: ∀ (R : Type) [CommRing R] [IsDomain R], IsPrincipalIdealRing R → UniqueFactorizationMonoid R` |
| `apm_b93j02_two_irreducible` | b93J02 | `: Irreducible (2 : Zsqrtd (-5))` |
| `apm_b93j02_two_not_prime` | b93J02 | `: ¬Prime (2 : Zsqrtd (-5))` |
| `apm_b93j02_ufd_implies_integrallyClosed` | b93J02 | `: ∀ (R : Type) [CommRing R] [IsDomain R], UniqueFactorizationMonoid R → IsIntegrallyClosed R` |
| `apm_b93j02_zsqrtd_module_finite` | b93J02 | `(d : ℤ) : Module.Finite ℤ (Zsqrtd d)` |
| `apm_b93j02_zsqrtd_negFive_isDomain` | b93J02 | `: IsDomain (Zsqrtd (-5))` |
| `apm_b93j02_zsqrtd_negFive_isNoetherianRing` | b93J02 | `: IsNoetherianRing (Zsqrtd (-5))` |
| `apm_b93j02_zsqrtd_negFive_not_pid` | b93J02 | `: ¬IsPrincipalIdealRing (Zsqrtd (-5))` |
| `apm_b93j02_zsqrtd_negFive_not_ufd` | b93J02 | `: ¬UniqueFactorizationMonoid (Zsqrtd (-5))` |
| `apm_b93j02_zsqrtd_noZeroDivisors` | b93J02 | `(d : ℤ) (hd : d < 0) : NoZeroDivisors (Zsqrtd d) where eq_zero_or_eq_zero_of_mul_eq_zero` |
| `apm_b93J03_exists_nonzero_simultaneous_maxGenEigenspace` | b93J03 | `(k V ι : Type*) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V] (f : ι → Module.End k V) (hcomm : Pairwise fun i j : ι ↦ Commute (f i) (f j)) : ∃ χ : ι → k, (⨅ i, (f i).maxGenEigenspace (χ i)) ≠ ⊥` |
| `apm_b93j04_four_radical_roots` | b93J04 | `(K : Type*) [Field K] [Algebra ℚ K] (r₂ r₃ : K) (h₂ : r₂ ^ 2 = algebraMap ℚ K 2) (h₃ : r₃ ^ 2 = algebraMap ℚ K 3) : Polynomial.eval₂ (algebraMap ℚ K) (r₂ + r₃) apm_b93j04_poly = 0 ∧ Polynomial.eval₂ (algebraMap ℚ K) (r₂ - r₃) apm_b93j04_poly = 0 ∧ Polynomial.eval₂ (algebraMap ℚ K) (-r₂ + r₃) apm_b93j04_poly = 0 ∧ Polynomial.eval₂ (algebraMap ℚ K) (-r₂ - r₃) apm_b93j04_poly = 0` |
| `apm_b93j04_four_radical_roots_pairwise` | b93J04 | `(K : Type*) [Field K] [Algebra ℚ K] (r₂ r₃ : K) (h₂ : r₂ ^ 2 = algebraMap ℚ K 2) (h₃ : r₃ ^ 2 = algebraMap ℚ K 3) : r₂ + r₃ ≠ r₂ - r₃ ∧ r₂ + r₃ ≠ -r₂ + r₃ ∧ r₂ + r₃ ≠ -r₂ - r₃ ∧ r₂ - r₃ ≠ -r₂ + r₃ ∧ r₂ - r₃ ≠ -r₂ - r₃ ∧ -r₂ + r₃ ≠ -r₂ - r₃` |
| `apm_b93J04_mulEquiv_kleinFour_of_card_exponent` | b93J04 | `(G : Type*) [Group G] (hcard : Nat.card G = 4) (hexp : Monoid.exponent G = 2) : Nonempty (G ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))` |
| `apm_b93j04_radical_root` | b93J04 | `(K : Type*) [Field K] [Algebra ℚ K] (r₂ r₃ : K) (h₂ : r₂ ^ 2 = algebraMap ℚ K 2) (h₃ : r₃ ^ 2 = algebraMap ℚ K 3) : Polynomial.eval₂ (algebraMap ℚ K) (r₂ + r₃) apm_b93j04_poly = 0` |
| `apm_b94a01_complement` | b94A01 | `(G : Type*) [Group G] [Fintype G] (P Q : Subgroup G) [P.Normal] (hP : Nat.card P = 5) (hQ : Nat.card Q = 2) (hG : Fintype.card G = 10) : Disjoint P Q ∧ P ⊔ Q = ⊤ ∧ ∃ φ : Q →* MulAut P, Nonempty (G ≃* (P ⋊[φ] Q))` |
| `apm_b94a01_enumerate_mulAut` | b94A01 | `(P : Type*) [Group P] [Finite P] (hcard : Nat.card (MulAut P) = 4) : ∃ Ψ : Fin 4 → MulAut P, Function.Injective Ψ ∧ ∀ φ : MulAut P, ∃ n : Fin 4, φ = Ψ n` |
| `apm_b94a01_power_mulAut` | b94A01 | `(P : Type*) [Group P] [Finite P] (x : P) (hx : Subgroup.zpowers x = ⊤) (hcard : Nat.card P = 5) : ∃ Ψ : Fin 4 → MulAut P, ∀ (n : Fin 4) (i : ℕ), Ψ n (x ^ i) = x ^ (((n : ℕ) + 1) * i)` |
| `apm_b94A02_coefficient_mul_mk_eq` | b94A02 | `(R : Type*) [CommRing R] (I : Ideal R) (b : R) (hAnn : ∀ c : R, b * c = 0 → c ∈ I) {x r r' s : R} (hr : x = b * r) (hr' : x = b * r') : Ideal.Quotient.mk I (r * s) = Ideal.Quotient.mk I (r' * s)` |
| `apm_b94A02_coefficientLinearMap_apply` | b94A02 | `(R : Type*) [CommRing R] (I : Ideal R) (b : R) (hAnn : ∀ c : R, b * c = 0 → c ∈ I) (x : Ideal.span {b}) (r : R) (hr : (x : R) = b * r) : apm_b94A02_coefficientLinearMap R I b hAnn x = Ideal.Quotient.mk I r` |
| `apm_b94A02_exists_balancedMap` | b94A02 | `(R : Type*) [CommRing R] (I : Ideal R) (b : R) (hAnn : ∀ c : R, b * c = 0 → c ∈ I) : ∃ φ : (Ideal.span {b}) →ₗ[R] ((R ⧸ I) →ₗ[R] (R ⧸ I)), Function.Surjective (fun p : (Ideal.span {b}) × (R ⧸ I) ↦ φ p.1 p.2) ∧ ∀ (x : Ideal.span {b}) (r s : R), (x : R) = b * r → φ x (Ideal.Quotient.mk I s) = Ideal.Quotient.mk I (r * s)` |
| `apm_b94A02_exists_surjective_tensorLift` | b94A02 | `(R : Type*) [CommRing R] (I : Ideal R) (b : R) (hAnn : ∀ c : R, b * c = 0 → c ∈ I) : ∃ Φ : TensorProduct R (Ideal.span {b}) (R ⧸ I) →ₗ[R] (R ⧸ I), Function.Surjective Φ ∧ ∀ (x : Ideal.span {b}) (r s : R), (x : R) = b * r → Φ (x ⊗ₜ[R] Ideal.Quotient.mk I s) = Ideal.Quotient.mk I (r * s)` |
| `apm_b94J01_card_eq_prod_of_invariantFactors` | b94J01 | `(G : Type*) [Group G] (d : List ℕ) (hd : apm_b94J01_invariantFactors G d) : Nat.card G = d.prod` |
| `apm_b94J01_existsUnique_invariantFactors_of_card_eq_one` | b94J01 | `(G : Type*) [CommGroup G] (hcard : Nat.card G = 1) : ∃! d : List ℕ, apm_b94J01_invariantFactors G d` |
| `apm_b94J01_invariantFactors_eq_nil_of_card_eq_one` | b94J01 | `(G : Type*) [Group G] (d : List ℕ) (hd : apm_b94J01_invariantFactors G d) (hcard : Nat.card G = 1) : d = []` |
| `apm_b94J03_aut_card_of_finrank_three` | b94J03 | `[Fact (Nat.Prime 7)] (K : Type*) [Field K] [Algebra (ZMod 7) K] [Finite K] [FiniteDimensional (ZMod 7) K] (hfin : Module.finrank (ZMod 7) K = 3) : Nat.card (K ≃ₐ[ZMod 7] K) = 3` |
| `apm_b94J03_card_of_finrank_three` | b94J03 | `[Fact (Nat.Prime 7)] (K : Type*) [Field K] [Algebra (ZMod 7) K] [Finite K] [FiniteDimensional (ZMod 7) K] (hfin : Module.finrank (ZMod 7) K = 3) : Nat.card K = 343` |
| `apm_b94J03_finiteField_conclusion` | b94J03 | `[Fact (Nat.Prime 7)] (K : Type*) [Field K] [Algebra (ZMod 7) K] [IsSplittingField (ZMod 7) K (apm_b94J03_poly (ZMod 7))] : Module.finrank (ZMod 7) K = 3 ∧ Nat.card K = 343 ∧ Nonempty ((K ≃ₐ[ZMod 7] K) ≃* Multiplicative (ZMod 3))` |
| `apm_b94J03_noncube_mod7` | b94J03 | `: ∀ a : ZMod 7, a ^ 3 ≠ 3` |
| `apm_b94J03_primitiveRoot_two_mod7` | b94J03 | `: IsPrimitiveRoot (2 : ZMod 7) 3` |
| `apm_b95J02_aeval_eq_zero_of_cyclic_vector` | b95J02 | `{F V : Type*} [Field F] [AddCommGroup V] [Module F V] (T : Module.End F V) (v : V) (hv : Submodule.span F (Set.range fun i : ℕ => (T ^ i) v) = ⊤) (p : Polynomial F) (hp : (Polynomial.aeval (R` |
| `apm_b95J02_charpoly_eq_minpoly_of_finrank_eq` | b95J02 | `(F V : Type*) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V] (T : Module.End F V) (h : Module.finrank F V = (minpoly F T).natDegree) : T.charpoly = minpoly F T` |
| `apm_b95J04_eigenvector_is_radical_generator` | b95J04 | `(p : ℕ) [Fact p.Prime] (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] (z : F) (hz : IsPrimitiveRoot z p) (hz1 : z ≠ 1) (hcard : Nat.card (E ≃ₐ[F] E) = p) (σ : E ≃ₐ[F] E) (hσ : σ ≠ 1) (α : E) (hα : α ≠ 0) (heigen : σ α = algebraMap F E z * α) : α ∉ (algebraMap F E).range ∧ α ^ p ∈ (algebraMap F E).range ∧ IntermediateField.adjoin F {α} = ⊤` |
| `apm_b95J04_exists_eigenvector_of_nonidentity_prime_card` | b95J04 | `(p : ℕ) [Fact p.Prime] (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] (z : F) (hz : IsPrimitiveRoot z p) (hcard : Nat.card (E ≃ₐ[F] E) = p) (σ : E ≃ₐ[F] E) (hσ : σ ≠ 1) : ∃ α : E, α ≠ 0 ∧ σ α = algebraMap F E z * α` |
| `apm_b95J04_mem_zpowers_of_nonidentity_prime_card` | b95J04 | `(p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] (hcard : Nat.card G = p) (g : G) (hg : g ≠ 1) : ∀ x : G, x ∈ Subgroup.zpowers g` |
| `apm_b96a02_normal_of_card_fifteen` | b96A02 | `(G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 30) (H : Subgroup G) (hH : Nat.card H = 15) : H.Normal` |
| `apm_b96a02_normalCore_eq_bot_or_eq_self_of_prime_card` | b96A02 | `(G : Type*) [Group G] (H : Subgroup G) (hprime : (Nat.card H).Prime) : H.normalCore = ⊥ ∨ H.normalCore = H` |
| `apm_b96J02_finrank_eq_four` | b96J02 | `(M : Type*) [AddCommGroup M] [Module apm_b96J02_R M] [Finite M] (hcard : Nat.card M = 16) : let _` |
| `apm_b96J02_squareZero_rank_cases` | b96J02 | `(F V : Type*) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V] (T : V →ₗ[F] V) (hT : T.comp T = 0) (hdim : Module.finrank F V = 4) : Module.finrank F (LinearMap.range T) = 0 ∨ Module.finrank F (LinearMap.range T) = 1 ∨ Module.finrank F (LinearMap.range T) = 2` |
| `apm_b96J02_x_smul_x_smul` | b96J02 | `(M : Type*) [AddCommGroup M] [Module apm_b96J02_R M] (v : M) : apm_b96J02_x • apm_b96J02_x • v = 0` |
| `apm_b96J02_x_sq` | b96J02 | `: apm_b96J02_x ^ 2 = 0` |
| `apm_b96J02_xLinearMap_sq` | b96J02 | `(M : Type*) [AddCommGroup M] [Module apm_b96J02_R M] : (apm_b96J02_xLinearMap M).comp (apm_b96J02_xLinearMap M) = 0` |
| `apm_b96j03_b7_c7_mem_range` | b96J03 | `: apm_b96j03_b7 ∈ apm_b96j03_toA7.range ∧ apm_b96j03_c7 ∈ apm_b96j03_toA7.range` |
| `apm_b96j03_closure_b7_c7_le_range` | b96J03 | `: Subgroup.closure ({apm_b96j03_b7, apm_b96j03_c7} : Set (alternatingGroup (Fin 7))) ≤ apm_b96j03_toA7.range` |
| `apm_b96j03_nilpotent_implies_solvable` | b96J03 | `: ∀ (G : Type) [Group G], apm_b96j03_IsNilpotent G → apm_b96j03_IsSolvable G` |
| `apm_b96j03_S3_not_nilpotent` | b96J03 | `: ¬Group.IsNilpotent (Equiv.Perm (Fin 3))` |
| `apm_b96j03_S3_solvable` | b96J03 | `: IsSolvable (Equiv.Perm (Fin 3))` |
| `apm_b96j03_solvable_not_nilpotent_exists` | b96J03 | `: ∃ (G : Type) (_ : Group G), @apm_b96j03_IsSolvable G ‹Group G› ∧ ¬@apm_b96j03_IsNilpotent G ‹Group G›` |
| `apm_b96j03_toA7_relations` | b96J03 | `(r : FreeGroup (Fin 3)) (hr : r ∈ apm_b96j03_relations) : FreeGroup.lift apm_b96j03_toA7Generators r = 1` |
| `apm_b96j03_toA7_surjective_of_generate` | b96J03 | `(hgen : Subgroup.closure ({apm_b96j03_b7, apm_b96j03_c7} : Set (alternatingGroup (Fin 7))) = ⊤) : Function.Surjective apm_b96j03_toA7` |
| `apm_b96j03_transpositionSubgroup_ne_top` | b96J03 | `: apm_b96j03_transpositionSubgroup ≠ ⊤` |
| `apm_b96j03_transpositionSubgroup_normalizer` | b96J03 | `: Subgroup.normalizer (apm_b96j03_transpositionSubgroup : Set (Equiv.Perm (Fin 3))) = apm_b96j03_transpositionSubgroup` |
| `apm_b96J04_aut_equiv_units_of_isCyclotomic` | b96J04 | `(K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {16} ℚ K] : Nonempty ((K ≃ₐ[ℚ] K) ≃* (ZMod 16)ˣ) ∧ Nat.card (K ≃ₐ[ℚ] K) = 8` |
| `apm_b96J04_card_units_mod_16` | b96J04 | `: Nat.card (ZMod 16)ˣ = 8` |
| `apm_b96J04_f41_eq_cyclotomic` | b96J04 | `: apm_b96J04_f41 = cyclotomic 16 (ZMod 41)` |
| `apm_b96J04_fQ_eq_cyclotomic` | b96J04 | `: apm_b96J04_fQ = cyclotomic 16 ℚ` |
| `apm_b96J04_orderOf_41_mod_16` | b96J04 | `: orderOf (41 : ZMod 16) = 2` |
| `apm_b96J04_X_pow_eight_add_one_eq_cyclotomic` | b96J04 | `(F : Type*) [Field F] : (X ^ 8 + 1 : F[X]) = cyclotomic 16 F` |
| `apm_b97A01_complete_conjugacy_classification` | b97A01 | `: ∀ σ : apm_b97A01_S4, (IsConj 1 σ ↔ σ.cycleType = {}) ∧ (IsConj apm_b97A01_transposition σ ↔ σ.cycleType = {2}) ∧ (IsConj apm_b97A01_doubleTransposition σ ↔ σ.cycleType = {2, 2}) ∧ (IsConj apm_b97A01_threeCycle σ ↔ σ.cycleType = {3}) ∧ (IsConj apm_b97A01_fourCycle σ ↔ σ.cycleType = {4}) ∧ (IsConj 1 σ ∨ IsConj apm_b97A01_transposition σ ∨ IsConj apm_b97A01_doubleTransposition σ ∨ IsConj apm_b97A01_threeCycle σ ∨ IsConj apm_b97A01_fourCycle σ)` |
| `apm_b97A01_conjugacy_class_cards` | b97A01 | `: Nat.card {σ : apm_b97A01_S4 // IsConj 1 σ} = 1 ∧ Nat.card {σ : apm_b97A01_S4 // IsConj apm_b97A01_transposition σ} = 6 ∧ Nat.card {σ : apm_b97A01_S4 // IsConj apm_b97A01_doubleTransposition σ} = 3 ∧ Nat.card {σ : apm_b97A01_S4 // IsConj apm_b97A01_threeCycle σ} = 8 ∧ Nat.card {σ : apm_b97A01_S4 // IsConj apm_b97A01_fourCycle σ} = 6` |
| `apm_b97A01_conjugacy_classification` | b97A01 | `: ∀ σ : apm_b97A01_S4, (IsConj 1 σ ↔ σ.cycleType = {}) ∧ (IsConj apm_b97A01_transposition σ ↔ σ.cycleType = {2}) ∧ (IsConj apm_b97A01_doubleTransposition σ ↔ σ.cycleType = {2, 2}) ∧ (IsConj apm_b97A01_threeCycle σ ↔ σ.cycleType = {3}) ∧ (IsConj apm_b97A01_fourCycle σ ↔ σ.cycleType = {4})` |
| `apm_b97A01_conjugacy_exhaustive` | b97A01 | `: ∀ σ : apm_b97A01_S4, IsConj 1 σ ∨ IsConj apm_b97A01_transposition σ ∨ IsConj apm_b97A01_doubleTransposition σ ∨ IsConj apm_b97A01_threeCycle σ ∨ IsConj apm_b97A01_fourCycle σ` |
| `apm_b97A01_representative_cycleTypes` | b97A01 | `: apm_b97A01_transposition.cycleType = {2} ∧ apm_b97A01_doubleTransposition.cycleType = {2, 2} ∧ apm_b97A01_threeCycle.cycleType = {3} ∧ apm_b97A01_fourCycle.cycleType = {4}` |
| `apm_b97A01_SL23_card` | b97A01 | `: Nat.card apm_b97A01_SL23 = 24` |
| `apm_b97A02_algebraMap_pow_card` | b97A02 | `(F : Type*) [Field F] [Fintype F] (a : F) : (algebraMap F (RatFunc F) a) ^ Fintype.card F = algebraMap F (RatFunc F) a` |
| `apm_b97A02_algebraMap_pow_card_sub_one` | b97A02 | `(F : Type*) [Field F] [Fintype F] (a : F) (ha : a ≠ 0) : (algebraMap F (RatFunc F) a) ^ (Fintype.card F - 1) = 1` |
| `apm_b97A02_exists_affineAlgEquiv` | b97A02 | `(F : Type*) [Field F] (a b : F) (ha : a ≠ 0) : ∃ σ : RatFunc F ≃ₐ[F] RatFunc F, σ RatFunc.X = algebraMap F (RatFunc F) a * RatFunc.X + algebraMap F (RatFunc F) b` |
| `apm_b97A02_finite_over_nontrivial_intermediate` | b97A02 | `(F : Type*) [Field F] (K : IntermediateField F (RatFunc F)) (hK : K ≠ ⊥) : Module.Finite K (RatFunc F)` |
| `apm_b97a03_candidate_roots_injective` | b97A03 | `{α : ℂ} (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) : Function.Injective (fun k : Fin 6 => apm_b97a03_zeta α ^ (k : ℕ) * α)` |
| `apm_b97a03_root_pow_six` | b97A03 | `{α : ℂ} (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) : α ^ 6 = -3` |
| `apm_b97a03_root_pow_three_sq` | b97A03 | `{α : ℂ} (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) : (α ^ 3) ^ 2 = -3` |
| `apm_b97a03_zeta_mem_field` | b97A03 | `{α : ℂ} : apm_b97a03_zeta α ∈ apm_b97a03_field α` |
| `apm_b97a03_zeta_mul_root` | b97A03 | `{α : ℂ} (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) (k : ℕ) : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot (apm_b97a03_zeta α ^ k * α)` |
| `apm_b97a03_zeta_mul_root_mem_field` | b97A03 | `{α : ℂ} (k : ℕ) : apm_b97a03_zeta α ^ k * α ∈ apm_b97a03_field α` |
| `apm_b97a03_zeta_pow_six` | b97A03 | `{α : ℂ} (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) : apm_b97a03_zeta α ^ 6 = 1` |
| `apm_b97a03_zeta_pow_three` | b97A03 | `{α : ℂ} (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) : apm_b97a03_zeta α ^ 3 = -1` |
| `apm_b97a03_zeta_primitive` | b97A03 | `{α : ℂ} (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) : IsPrimitiveRoot (apm_b97a03_zeta α) 6` |
| `apm_b97a03_zeta_relation` | b97A03 | `{α : ℂ} (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) : apm_b97a03_zeta α ^ 2 - apm_b97a03_zeta α + 1 = 0` |
| `apm_b97a04_burnside` | b97A04 | `(R V : Type) [Ring R] [AddCommGroup V] [Algebra ℂ R] [Module ℂ V] [Module R V] [IsScalarTower ℂ R V] [SMulCommClass ℂ R V] [FiniteDimensional ℂ R] [IsSimpleModule R V] (hfaithful : ∀ r : R, (∀ v : V, r • v = 0) → r = 0) : Nonempty (R ≃ₐ[ℂ] Module.End ℂ V)` |
| `apm_b97a04_module_finite` | b97A04 | `(R V : Type) [Ring R] [AddCommGroup V] [Algebra ℂ R] [Module ℂ V] [Module R V] [IsScalarTower ℂ R V] [FiniteDimensional ℂ R] [IsSimpleModule R V] : Module.Finite ℂ V` |
| `apm_b97a04_modules_are_copies` | b97A04 | `(R V : Type) [Ring R] [AddCommGroup V] [Algebra ℂ R] [Module ℂ V] [Module R V] [IsScalarTower ℂ R V] [SMulCommClass ℂ R V] [FiniteDimensional ℂ R] [IsSimpleModule R V] (e : R ≃ₐ[ℂ] Module.End ℂ V) (W : Type) [AddCommGroup W] [Module R W] : ∃ (ι : Type), Nonempty (W ≃ₗ[R] (ι →₀ V))` |
| `apm_b97a04_schur_and_scalars` | b97A04 | `(R V : Type) [Ring R] [AddCommGroup V] [Algebra ℂ R] [Module ℂ V] [Module R V] [IsScalarTower ℂ R V] [SMulCommClass ℂ R V] [FiniteDimensional ℂ R] [IsSimpleModule R V] : (∀ φ : Module.End R V, φ ≠ 0 → IsUnit φ) ∧ Module.Finite ℂ (Module.End R V) ∧ (∀ φ : Module.End R V, ∃ c : ℂ, φ = c • LinearMap.id)` |
| `apm_b97j02_isMaximal_of_zeroDimensional` | b97J02 | `(R : Type*) [CommRing R] (hR : APMZeroDimensional R) (P : APMSpectrum R) : P.1.IsMaximal` |
| `apm_b97j02_pi_idempotent_span` | b97J02 | `(I : Type*) (F : I → Type*) [∀ i, Field (F i)] (a : ∀ i, F i) : ∃ e : ∀ i, F i, e ^ 2 = e ∧ Ideal.span ({a} : Set (∀ i, F i)) = Ideal.span ({e} : Set (∀ i, F i))` |
| `apm_b97j02_quotient_field` | b97J02 | `(R : Type*) [CommRing R] (hR : APMZeroDimensional R) (P : APMSpectrum R) : Nonempty (Field (R ⧸ P.1))` |
| `apm_b97j02_toPiQuotient_apply` | b97J02 | `(R : Type*) [CommRing R] (a : R) (P : APMSpectrum R) : apm_b97j02_toPiQuotient R a P = Ideal.Quotient.mk P.1 a` |
| `apm_b97j02_toPiQuotient_bijective_of_finite` | b97J02 | `(R : Type*) [CommRing R] (hzero : APMZeroDimensional R) (hred : APMReduced R) [Finite (APMSpectrum R)] : Function.Bijective (apm_b97j02_toPiQuotient R)` |
| `apm_b97j02_toPiQuotient_injective` | b97J02 | `(R : Type*) [CommRing R] (hR : APMReduced R) : Function.Injective (apm_b97j02_toPiQuotient R)` |
| `apm_b97j02_zeroDimensional_reduced_of_idempotent_span` | b97J02 | `(R : Type*) [CommRing R] (h : ∀ a : R, ∃ e : R, e ^ 2 = e ∧ Ideal.span ({a} : Set R) = Ideal.span ({e} : Set R)) : APMZeroDimensional R ∧ APMReduced R` |
| `apm_b97j03_rootCount_le_natDegree` | b97J03 | `(P : Polynomial ℚ) (α : ℂ) (hP : P ≠ 0) : apm_b97j03_rootCount P α ≤ P.natDegree` |
| `apm_b97j03_special_factorization` | b97J03 | `{α : ℂ} (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) : apm_b97j03_special.map (algebraMap ℚ ℂ) = ∏ i ∈ Finset.range 6, (X - C (apm_b97j03_zeta6 ^ i * α))` |
| `apm_b97j03_special_natDegree` | b97J03 | `: apm_b97j03_special.natDegree = 6` |
| `apm_b97j03_special_neg_root` | b97J03 | `{α : ℂ} (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot (-α)` |
| `apm_b97j03_special_root_ne_zero` | b97J03 | `{α : ℂ} (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) : α ≠ 0` |
| `apm_b97j03_special_root_pow_six` | b97J03 | `{α : ℂ} (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) : α ^ 6 = 2` |
| `apm_b97j03_special_rootCount_le_six` | b97J03 | `(α : ℂ) : apm_b97j03_rootCount apm_b97j03_special α ≤ 6` |
| `apm_b97j03_special_roots_mem_adjoin` | b97J03 | `{α : ℂ} : α ∈ IntermediateField.adjoin ℚ ({α} : Set ℂ) ∧ -α ∈ IntermediateField.adjoin ℚ ({α} : Set ℂ)` |
| `apm_b97j03_two_le_special_rootCount` | b97J03 | `{α : ℂ} (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) : 2 ≤ apm_b97j03_rootCount apm_b97j03_special α` |
| `apm_b97j03_zeta6_primitive` | b97J03 | `: IsPrimitiveRoot apm_b97j03_zeta6 6` |
| `apm_b97j04_additive_exists` | b97J04 | `(F V : Type*) [Field F] [IsAlgClosed F] [AddCommGroup V] [Module F V] [FiniteDimensional F V] (T : Module.End F V) : ∃ S N : Module.End F V, APMAdditiveJC T S N` |
| `apm_b97j04_additive_unique` | b97J04 | `(F V : Type*) [Field F] [IsAlgClosed F] [AddCommGroup V] [Module F V] [FiniteDimensional F V] (T : Module.End F V) (S N S' N' : Module.End F V) (h : APMAdditiveJC T S N) (h' : APMAdditiveJC T S' N') : S = S' ∧ N = N'` |
| `apm_b97j04_eigenspace_subset_generalized` | b97J04 | `(F V : Type*) [Field F] [AddCommGroup V] [Module F V] (T S N : Module.End F V) (h : APMAdditiveJC T S N) (lam : F) : APMEigenspace S lam ⊆ APMGeneralizedEigenspace T lam` |
| `apm_b97j04_mapsTo_generalizedEigenspace` | b97J04 | `(F V : Type*) [Field F] [AddCommGroup V] [Module F V] (T S N : Module.End F V) (h : APMAdditiveJC T S N) (lam : F) : Set.MapsTo S (APMGeneralizedEigenspace T lam) (APMGeneralizedEigenspace T lam) ∧ Set.MapsTo N (APMGeneralizedEigenspace T lam) (APMGeneralizedEigenspace T lam)` |
| `apm_b98a01_coset_core_action` | b98A01 | `(G : Type*) [Group G] [Fintype G] (H : Subgroup G) (n : ℕ) (hn : H.index = n) : ∃ ψ : G →* Equiv.Perm (Fin n), MonoidHom.ker ψ ≤ H ∧ ∀ N : Subgroup G, N.Normal → N ≤ H → N ≤ MonoidHom.ker ψ` |
| `apm_b98a01_normalizer_card_arithmetic` | b98A01 | `(s c : ℕ) (hprod : s * c = 210) (hs : s = 6 ∨ s = 21) : c = 10 ∨ c = 35` |
| `apm_b98a01_orderFive_index` | b98A01 | `(G : Type*) [Group G] [Fintype G] (B : Subgroup G) (hG : Fintype.card G = 210) (hB : Nat.card B = 5) : B.index = 42` |
| `apm_b98a01_orderFive_normalizer_card` | b98A01 | `(G : Type*) [Group G] [Fintype G] (B : Subgroup G) (hG : Fintype.card G = 210) (hB : Nat.card B = 5) (hnormal : ¬B.Normal) : Nat.card (Subgroup.normalizer (B : Set G)) = 10 ∨ Nat.card (Subgroup.normalizer (B : Set G)) = 35` |
| `apm_b98a01_sylow5_count_arithmetic` | b98A01 | `(s : ℕ) (hdvd : s ∣ 42) (hmod : s % 5 = 1) (hne : s ≠ 1) : s = 6 ∨ s = 21` |
| `apm_b98a02_intersection_maximal_eq` | b98A02 | `(F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (E L A_E A_L A_EL : IntermediateField F Ω) [FiniteDimensional F E] [FiniteDimensional F L] (hAE : apm_b98A02_IsMaximalAbelian F Ω E A_E) (hAL : apm_b98A02_IsMaximalAbelian F Ω L A_L) (hAEL : apm_b98A02_IsMaximalAbelian F Ω (E ⊓ L) A_EL) : A_EL = (A_E ⊓ A_L : IntermediateField F Ω)` |
| `apm_b98a02_intersection_maximal_le` | b98A02 | `(F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] (E L A_E A_L A_EL : IntermediateField F Ω) (hE : apm_b98A02_IsMaximalAbelian F Ω E A_E) (hL : apm_b98A02_IsMaximalAbelian F Ω L A_L) (hEL : apm_b98A02_IsMaximalAbelian F Ω (E ⊓ L) A_EL) : A_EL ≤ A_E ⊓ A_L` |
| `apm_b98a02_isGalois_inf` | b98A02 | `(F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (E L : IntermediateField F Ω) [FiniteDimensional F E] [FiniteDimensional F L] (hE : IsGalois F E) (hL : IsGalois F L) : IsGalois F (E ⊓ L : IntermediateField F Ω)` |
| `apm_b98a02_le_of_isMaximalAbelian` | b98A02 | `(F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] (E A K : IntermediateField F Ω) (hA : apm_b98A02_IsMaximalAbelian F Ω E A) (hKE : K ≤ E) (hK : IsGalois F K) (hKab : ∀ σ τ : K ≃ₐ[F] K, σ * τ = τ * σ) : K ≤ A` |
| `apm_b98a02_map_comap_subtype` | b98A02 | `(F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] (E K : IntermediateField F Ω) (hKE : K ≤ E) : (K.comap E.val).map E.val = K` |
| `apm_b98a02_map_subtype_le` | b98A02 | `(F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] (E : IntermediateField F Ω) (A : IntermediateField F E) : A.map E.val ≤ E` |
| `apm_b98a02_map_subtype_top` | b98A02 | `(F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] (E : IntermediateField F Ω) : (⊤ : IntermediateField F E).map E.val = E` |
| `apm_b98a02_maximal_iff` | b98A02 | `(F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] (E A K : IntermediateField F Ω) (hA : apm_b98A02_IsMaximalAbelian F Ω E A) (hKE : K ≤ E) : (IsGalois F K ∧ (∀ σ τ : K ≃ₐ[F] K, σ * τ = τ * σ) ↔ K ≤ A)` |
| `apm_b98a02_maximalAbelian_unique` | b98A02 | `(F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] (E A B : IntermediateField F Ω) (hA : apm_b98A02_IsMaximalAbelian F Ω E A) (hB : apm_b98A02_IsMaximalAbelian F Ω E B) : A = B` |
| `apm_b98A03_comap_adjoin_singleton_eq` | b98A03 | `(R T : Type*) [CommRing R] [CommRing T] [Algebra R T] (P : Ideal R) (Q₁ Q₂ : Ideal T) (hcomap₁ : Ideal.comap (algebraMap R T) Q₁ = P) (hcomap₂ : Ideal.comap (algebraMap R T) Q₂ = P) {u : T} (hu : u ∈ Q₁ ⊓ Q₂) : Ideal.comap (Algebra.adjoin R {u}).val Q₁ = Ideal.comap (Algebra.adjoin R {u}).val Q₂` |
| `apm_b98A03_conductor_eq_elementwise` | b98A03 | `(R T : Type*) [CommRing R] [CommRing T] [Algebra R T] : apm_b98A03_conductor R T = apm_b98A03_elementwiseConductor R T` |
| `apm_b98A03_eq_of_conductor_not_mem` | b98A03 | `(R T : Type*) [CommRing R] [CommRing T] [Algebra R T] (P : Ideal R) (Q₁ Q₂ : Ideal T) (hQ₁ : Q₁.IsPrime) (hQ₂ : Q₂.IsPrime) (hcomap₁ : Ideal.comap (algebraMap R T) Q₁ = P) (hcomap₂ : Ideal.comap (algebraMap R T) Q₂ = P) {r : R} (hrI : algebraMap R T r ∈ apm_b98A03_conductor R T) (hrP : r ∉ P) : Q₁ = Q₂` |
| `apm_b98A03_intersection_eq` | b98A03 | `(R T : Type*) [CommRing R] [CommRing T] [Algebra R T] (P : Ideal R) (Q₁ Q₂ : Ideal T) (hcomap₁ : Ideal.comap (algebraMap R T) Q₁ = P) (hcomap₂ : Ideal.comap (algebraMap R T) Q₂ = P) (hsmall : ∀ S : Subalgebra R T, Ideal.comap S.val Q₁ = Ideal.comap S.val Q₂ → S = ⊥) : Ideal.map (algebraMap R T) P = Q₁ ⊓ Q₂` |
| `apm_b98A03_intersection_eq_conductor` | b98A03 | `(R T : Type*) [CommRing R] [CommRing T] [Algebra R T] (P : Ideal R) (Q₁ Q₂ : Ideal T) (hne : Q₁ ≠ Q₂) (hQ₁ : Q₁.IsPrime) (hQ₂ : Q₂.IsPrime) (hcomap₁ : Ideal.comap (algebraMap R T) Q₁ = P) (hcomap₂ : Ideal.comap (algebraMap R T) Q₂ = P) (hsmall : ∀ S : Subalgebra R T, Ideal.comap S.val Q₁ = Ideal.comap S.val Q₂ → S = ⊥) (hmap : Ideal.map (algebraMap R T) P = Q₁ ⊓ Q₂) : Q₁ ⊓ Q₂ = apm_b98A03_conductor R T` |
| `apm_b98A03_intersection_subset_range` | b98A03 | `(R T : Type*) [CommRing R] [CommRing T] [Algebra R T] (P : Ideal R) (Q₁ Q₂ : Ideal T) (hcomap₁ : Ideal.comap (algebraMap R T) Q₁ = P) (hcomap₂ : Ideal.comap (algebraMap R T) Q₂ = P) (hsmall : ∀ S : Subalgebra R T, Ideal.comap S.val Q₁ = Ideal.comap S.val Q₂ → S = ⊥) : (Q₁ ⊓ Q₂ : Set T) ⊆ Set.range (algebraMap R T)` |
| `apm_b98A03_le_conductor` | b98A03 | `(R T : Type*) [CommRing R] [CommRing T] [Algebra R T] (J : Ideal T) (hJ : (J : Set T) ⊆ Set.range (algebraMap R T)) : J ≤ apm_b98A03_conductor R T` |
| `apm_b98a04_actionMap_injective` | b98A04 | `(R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (s : ℕ) (m : Fin s → M) (h : {r : R \| ∀ i, r • m i = 0} = {0}) : Function.Injective (apm_b98a04_actionMap R M s m)` |
| `apm_b98a04_commonAnnihilator` | b98A04 | `(R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (k : ℕ) (m : Fin k → M) : ∃ I : Submodule R R, (I : Set R) = {r \| ∀ i, r • m i = 0}` |
| `apm_b98a04_exists_faithful_tuple` | b98A04 | `(R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [FaithfulSMul R M] [IsArtinian R R] : ∃ (s : ℕ) (m : Fin s → M), {r : R \| ∀ i, r • m i = 0} = {0}` |
| `apm_b98a04_simple_quotient_of_embedded_regular` | b98A04 | `(R M V : Type*) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V] [IsSimpleModule R V] (s : ℕ) (f : R →ₗ[R] (Fin s → M)) (hf : Function.Injective f) : ∃ (S : Submodule R (Fin s → M)) (g : S →ₗ[R] V), Function.Surjective g` |
| `apm_b98J01_card_comap_of_surjective` | b98J01 | `{G Q : Type*} [Group G] [Group Q] (φ : G →* Q) (hφ : Function.Surjective φ) (V : Subgroup Q) : Nat.card (V.comap φ) = Nat.card φ.ker * Nat.card V` |
| `apm_b98J01_kleinFour_comap_card` | b98J01 | `{G : Type*} [Group G] (φ : G →* alternatingGroup (Fin 4)) (hφ : Function.Surjective φ) (hker : Nat.card φ.ker = 3) : Nat.card ((alternatingGroup.kleinFour (Fin 4)).comap φ) = 12` |
| `apm_b98J01_kleinFour_comap_normal_and_ker_le` | b98J01 | `{G : Type*} [Group G] (φ : G →* alternatingGroup (Fin 4)) : ((alternatingGroup.kleinFour (Fin 4)).comap φ).Normal ∧ φ.ker ≤ (alternatingGroup.kleinFour (Fin 4)).comap φ` |
| `apm_b99A02_card_comap_mk` | b99A02 | `{G : Type*} [Group G] (N : Subgroup G) [N.Normal] (S : Subgroup (G ⧸ N)) : Nat.card (S.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card S` |
| `apm_b99A02_normal_comap_mk_and_le` | b99A02 | `{G : Type*} [Group G] (N : Subgroup G) [N.Normal] (S : Subgroup (G ⧸ N)) (hS : S.Normal) : (S.comap (QuotientGroup.mk' N)).Normal ∧ N ≤ S.comap (QuotientGroup.mk' N)` |
| `apm_b99A02_sylow29_normal_of_card_203` | b99A02 | `(X : Type*) [Group X] [Fintype X] (hX : Nat.card X = 203) (S : Sylow 29 X) : S.toSubgroup.Normal` |
| `apm_b99A02_sylow29_unique_of_card_203` | b99A02 | `(X : Type*) [Group X] [Fintype X] (hX : Nat.card X = 203) : Nat.card (Sylow 29 X) = 1` |
| `apm_continuous_convolution_indicator` | a99J02 | `(A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) (hAfin : volume A ≠ ⊤) (hBfin : volume B ≠ ⊤) : Continuous ((indicator A (1 : ℝ → ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (indicator B (1 : ℝ → ℝ)))` |
| `apm_continuous_overlapMeasure` | a99J02 | `(A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) (hBfin : volume B ≠ ⊤) : Continuous (fun x => volume (A ∩ (apmSubtractionMap x) ⁻¹' B))` |
| `apm_continuous_overlapSet` | a99J02 | `(A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) (hBfin : volume B ≠ ⊤) : Continuous (apmOverlapSet A B hA hB)` |
| `apm_continuous_subtractionMap` | a99J02 | `: Continuous apmSubtractionMap` |
| `apm_convolution_eq_overlapReal` | a99J02 | `(A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) (x : ℝ) : ((indicator A (1 : ℝ → ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (indicator B (1 : ℝ → ℝ))) x = volume.real (A ∩ (apmSubtractionMap x) ⁻¹' B)` |
| `apm_exists_ball_subset_sub` | a99J02 | `{E : Set ℝ} (hE : MeasurableSet E) (hEpos : 0 < volume E) : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, \|t\| < ε → t ∈ E - E` |
| `apm_log_abs_le_tangent` | a99J01 | `{m x : ℝ} (hm : 0 < m) (hx : x ≠ 0) : Real.log \|x\| ≤ m * \|x\| - Real.log m - 1` |
| `apm_m00A02_counterexample_hasDerivAt` | m00A02 | `(x : ℝ) : HasDerivAt apm_m00A02_counterexample (Real.cos (Real.exp x) - Real.exp (-x) * Real.sin (Real.exp x)) x` |
| `apm_m00A02_expansion_coefficients_unique` | m00A02 | `{f : ℝ → ℝ} {a c : ℕ → ℝ} (ha : apm_m00A02_hasExpansion f a) (hc : apm_m00A02_hasExpansion f c) : a = c` |
| `apm_m00A03_derivedSet_subset_zero_of_annular_finite` | m00A03 | `(s : Set ℂ) (h : ∀ ε : ℝ, 0 < ε → {z ∈ s \| ε ≤ ‖z‖}.Finite) : derivedSet s ⊆ {0}` |
| `apm_m00A03_finite_norm_ge_of_finite_norm_gt` | m00A03 | `(s : Set ℂ) (h : ∀ ε : ℝ, 0 < ε → {z ∈ s \| ε < ‖z‖}.Finite) (ε : ℝ) (hε : 0 < ε) : {z ∈ s \| ε ≤ ‖z‖}.Finite` |
| `apm_m00A04_zero_memH10WithGradient` | m00A04 | `{n : ℕ} (U : Set (Fin n → ℝ)) : apm_m00A04_memH10WithGradient U 0 0` |
| `apm_m00A04_zero_weak_solution` | m00A04 | `{n : ℕ} (U : Set (Fin n → ℝ)) : ∃ (u : (Fin n → ℝ) → ℝ) (g : Fin n → (Fin n → ℝ) → ℝ), apm_m00A04_memH10WithGradient U u g ∧ ∀ (v : (Fin n → ℝ) → ℝ) (h : Fin n → (Fin n → ℝ) → ℝ), apm_m00A04_memH10WithGradient U v h → (∫ x in U, (∑ i : Fin n, g i x * h i x) + u x * v x) = ∫ x in U, (0 : ℝ) * v x` |
| `apm_m00A05_hasDerivAt_of_isSolution` | m00A05 | `{u₀ : ℝ} {u : ℝ → ℝ} (hu : apm_m00A05_isSolution u₀ u) {t : ℝ} (ht : 0 < t) : HasDerivAt u (Real.cos (u t) - u t) t` |
| `apm_m00A05_lipschitz_vectorField` | m00A05 | `: LipschitzWith 2 (fun x : ℝ => Real.cos x - x)` |
| `apm_m00a06_continuous_dslope_zero` | m00A06 | `{φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) : Continuous (dslope φ 0)` |
| `apm_m00a06_kernel_mul_eq_sign_mul_dslope` | m00A06 | `{φ : ℝ → ℝ} (hφ0 : φ 0 = 0) {x : ℝ} (hx : x ≠ 0) : apm_m00a06_singularKernel x * φ x = (\|x\|⁻¹ * x) * dslope φ 0 x` |
| `apm_m01j03_tendsto_powers_of_gap` | m01J03 | `{A : Type*} [NormedRing A] (a p : A) (hp : p * p = p) (hap : a * p = p) (hpa : p * a = p) (hgap : ‖a - p‖ < 1) : Filter.Tendsto (fun n : ℕ => a ^ n) Filter.atTop (nhds p)` |
| `apm_m01J06_critical_mode_exists` | m01J06 | `(K : ℝ) (m : ℕ) : ∃ φ : ℝ → ℝ, apm_m01J06_linearMode (apm_m01J06_criticalLoad K m) K φ ∧ apm_m01J06_nontrivial φ` |
| `apm_m01J06_derivWithin_smul_variation` | m01J06 | `(ε : ℝ) (η : ℝ → ℝ) (s : ℝ) : derivWithin (fun t ↦ ε * η t) (Icc 0 1) s = ε * derivWithin η (Icc 0 1) s` |
| `apm_m01J06_mode_hasDerivAt` | m01J06 | `(w s : ℝ) : HasDerivAt (fun t : ℝ ↦ Real.sin (w * t)) (w * Real.cos (w * s)) s` |
| `apm_m01J06_mode_hasSecondDerivAt` | m01J06 | `(w s : ℝ) : HasDerivAt (fun t : ℝ ↦ w * Real.cos (w * t)) (-(w ^ 2) * Real.sin (w * s)) s` |
| `apm_m01J06_mode_iteratedDerivWithin_two` | m01J06 | `(w s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : iteratedDerivWithin 2 (fun t : ℝ ↦ Real.sin (w * t)) (Icc 0 1) s = -(w ^ 2) * Real.sin (w * s)` |
| `apm_m02a04_sqrt_div_pow_three` | m02A04 | `{t : ℝ} (ht : 0 < t) : Real.sqrt (Real.pi / t ^ 3) = Real.sqrt Real.pi * Real.rpow t (-(3 : ℝ) / 2)` |
| `apm_m02a06_contraction_constant_lt_one` | m02A06 | `(C ε : ℝ) (hC : 0 ≤ C) (hε_small : ε < 1 / (4 * (1 + C))) : 4 * ε * (1 + C) < 1` |
| `apm_m02a06_greenKernel_comm` | m02A06 | `(x y : ℝ) : apm_m02a06_greenKernel x y = apm_m02a06_greenKernel y x` |
| `apm_m02a06_greenKernel_le_exp` | m02A06 | `{x y : ℝ} : apm_m02a06_greenKernel x y ≤ (1 / 2 : ℝ) * Real.exp (-\|x - y\|)` |
| `apm_m02a06_greenKernel_le_half` | m02A06 | `{x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : apm_m02a06_greenKernel x y ≤ 1 / 2` |
| `apm_m02a06_greenKernel_nonneg` | m02A06 | `{x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ apm_m02a06_greenKernel x y` |
| `apm_m02a06_greenKernel_of_ge` | m02A06 | `{x y : ℝ} (hxy : x ≤ y) : apm_m02a06_greenKernel x y = (1 / 2 : ℝ) * (Real.exp (-(y - x)) - Real.exp (-(x + y)))` |
| `apm_m02a06_greenKernel_of_le` | m02A06 | `{x y : ℝ} (hyx : y ≤ x) : apm_m02a06_greenKernel x y = (1 / 2 : ℝ) * (Real.exp (-(x - y)) - Real.exp (-(x + y)))` |
| `apm_m02a06_greenKernel_zero_left` | m02A06 | `{y : ℝ} (hy : 0 ≤ y) : apm_m02a06_greenKernel 0 y = 0` |
| `apm_m02a06_greenKernel_zero_right` | m02A06 | `{x : ℝ} (hx : 0 ≤ x) : apm_m02a06_greenKernel x 0 = 0` |
| `apm_m02a06_quadratic_lipschitz` | m02A06 | `(C ε u v : ℝ) (hε : 0 ≤ ε) (hu : \|u\| ≤ 2 * (1 + C)) (hv : \|v\| ≤ 2 * (1 + C)) : \|ε * u ^ 2 - ε * v ^ 2\| ≤ (4 * ε * (1 + C)) * \|u - v\|` |
| `apm_m02a06_radius_pos` | m02A06 | `(C : ℝ) (hC : 0 ≤ C) : 0 < 2 * (1 + C)` |
| `apm_m02j01_integral_deriv_testFunction_eq_zero` | m02J01 | `(ψ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) : ∫ x : ℝ, deriv (ψ : ℝ → ℝ) x = 0` |
| `apm_m02j01_integral_eq_zero_of_eq_deriv` | m02J01 | `(φ ψ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) (h : ∀ x : ℝ, φ x = deriv (ψ : ℝ → ℝ) x) : ∫ x : ℝ, φ x = 0` |
| `apm_m02j01_primitive_hasCompactSupport` | m02J01 | `(φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) (a b : ℝ) (hsupp : Function.support (φ : ℝ → ℝ) ⊆ Ioc a b) (hzero : ∫ x : ℝ, φ x = 0) : HasCompactSupport (fun x => ∫ t in a..x, φ t)` |
| `apm_m02j01_primitive_smooth` | m02J01 | `(φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) : let P : ℝ → ℝ` |
| `apm_m02j01_primitive_support` | m02J01 | `(φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) (a b : ℝ) (hsupp : Function.support (φ : ℝ → ℝ) ⊆ Ioc a b) (hzero : ∫ x : ℝ, φ x = 0) : Function.support (fun x => ∫ t in a..x, φ t) ⊆ Icc a b` |
| `apm_m02j02_deriv_hermiteFunction` | m02J02 | `(n : ℕ) (x : ℝ) : deriv (apm_m02j02_hermiteFunction n) x = apm_m02j02_hermiteFunctionDeriv n x` |
| `apm_m02j02_deriv_sine` | m02J02 | `(n : ℕ) (x : ℝ) : deriv (apm_m02j02_sine n) x = apm_m02j02_sineDeriv n x` |
| `apm_m02j02_hasDerivAt_sine` | m02J02 | `(n : ℕ) (x : ℝ) : HasDerivAt (apm_m02j02_sine n) (apm_m02j02_sineDeriv n x) x` |
| `apm_m02j02_hermiteFunction_contDiff` | m02J02 | `(n : ℕ) : ContDiff ℝ ∞ (apm_m02j02_hermiteFunction n)` |
| `apm_m02j02_hermiteFunction_hasDerivAt` | m02J02 | `(n : ℕ) (x : ℝ) : HasDerivAt (apm_m02j02_hermiteFunction n) (apm_m02j02_hermiteFunctionDeriv n x) x` |
| `apm_m02j02_hermiteFunction_odd_zero` | m02J02 | `(n : ℕ) : apm_m02j02_hermiteFunction (2 * n + 1) 0 = 0` |
| `apm_m02j02_sine_contDiff` | m02J02 | `(n : ℕ) : ContDiff ℝ ∞ (apm_m02j02_sine n)` |
| `apm_m02j02_sine_one` | m02J02 | `(n : ℕ) : apm_m02j02_sine n 1 = 0` |
| `apm_m02j02_sine_zero` | m02J02 | `(n : ℕ) : apm_m02j02_sine n 0 = 0` |
| `apm_m02j02_sineDeriv_contDiff` | m02J02 | `(n : ℕ) : ContDiff ℝ ∞ (apm_m02j02_sineDeriv n)` |
| `apm_m02j03_norm_tendsto_of_tendsto` | m02J03 | `{H : Type*} [NormedAddCommGroup H] {x : ℕ → H} {x₀ : H} (h : Tendsto x atTop (nhds x₀)) : Tendsto (fun n ↦ ‖x n‖) atTop (nhds ‖x₀‖)` |
| `apm_m02j03_tendsto_of_weak_and_norm` | m02J03 | `{H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {x : ℕ → H} {x₀ : H} (hweak : ∀ y : H, Tendsto (fun n ↦ inner ℂ (x n) y) atTop (nhds (inner ℂ x₀ y))) (hnorm : Tendsto (fun n ↦ ‖x n‖) atTop (nhds ‖x₀‖)) : Tendsto x atTop (nhds x₀)` |
| `apm_m02J05_young_mono` | m02J05 | `{α : ℝ → ℝ} (hc : ContinuousOn α (Ici 0)) (hα : ∀ t, 0 ≤ t → 0 ≤ α t) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : apm_m02J05_young α s ≤ apm_m02J05_young α t` |
| `apm_m02J05_young_nonneg` | m02J05 | `{α : ℝ → ℝ} (hα : ∀ t, 0 ≤ t → 0 ≤ α t) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ apm_m02J05_young α t` |
| `apm_m02J05_young_zero` | m02J05 | `(α : ℝ → ℝ) : apm_m02J05_young α 0 = 0` |
| `apm_m02J05_zero_mem_K` | m02J05 | `(α : ℝ → ℝ) : (0 : ℝ →ₘ[volume] ℝ) ∈ apm_m02J05_K α` |
| `apm_m02J05_zero_mem_L` | m02J05 | `(α : ℝ → ℝ) : (0 : ℝ →ₘ[volume] ℝ) ∈ apm_m02J05_L α` |
| `apm_m02J06_convolution_eq_zero` | m02J06 | `{φ f : ℝ → ℝ} (hφ : ∀ x, 1 ≤ \|x\| → φ x = 0) {ε : ℝ} (hε : 0 < ε) (hf : f ∈ apm_m02J06_K) {x : ℝ} (hx : 1 + ε ≤ \|x\|) : apm_m02J06_convolution f (apm_m02J06_mollifier φ ε) x = 0` |
| `apm_m02J06_mollifier_eq_zero` | m02J06 | `{φ : ℝ → ℝ} (hφ : ∀ x, 1 ≤ \|x\| → φ x = 0) {ε x : ℝ} (hε : 0 < ε) (hx : ε ≤ \|x\|) : apm_m02J06_mollifier φ ε x = 0` |
| `apm_m02J06_mollifier_integral_one` | m02J06 | `{φ : ℝ → ℝ} (hφ : ∫ x, φ x ∂volume = 1) {ε : ℝ} (hε : 0 < ε) : ∫ x, apm_m02J06_mollifier φ ε x ∂volume = 1` |
| `apm_m02J06_mollifier_nonneg` | m02J06 | `{φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) {ε : ℝ} (hε : 0 < ε) (x : ℝ) : 0 ≤ apm_m02J06_mollifier φ ε x` |
| `apm_m02J06_toL1_congr_ae` | m02J06 | `{f g : ℝ → ℝ} (hf : Integrable f volume) (hg : Integrable g volume) (hfg : f =ᵐ[volume] g) : apm_m02J06_toL1 f hf = apm_m02J06_toL1 g hg` |
| `apm_m02J06_translation_estimate` | m02J06 | `{f : ℝ → ℝ} (hf : f ∈ apm_m02J06_K) (h : ℝ) : ∫ x, \|f (x + h) - f x\| ∂volume ≤ Real.sqrt \|h\|` |
| `apm_m03J01_abstract_variational` | m03J01 | `: ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V], ∃ T : (V →L[ℝ] ℝ) →L[ℝ] V, ∀ f : V →L[ℝ] ℝ, (∃ C : ℝ, ∀ v : V, C ≤ (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v) ∧ (∀ v : V, (2 : ℝ)⁻¹ * ‖T f‖ ^ 2 - f (T f) ≤ (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v) ∧ (∀ u : V, (∀ v : V, (2 : ℝ)⁻¹ * ‖u‖ ^ 2 - f u ≤ (2 : ℝ)⁻¹ * ‖v‖ ^ 2 - f v) → u = T f) ∧ (∀ v : V, inner ℝ (T f) v = f v)` |
| `apm_m03J01_inner_riesz` | m03J01 | `{V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] (f : V →L[ℝ] ℝ) (v : V) : inner ℝ (apm_m03J01_riesz V f) v = f v` |
| `apm_m03J01_weakSolution_zero_iff` | m03J01 | `{n : ℕ} {Ω : Set (apm_m03J01_E n)} (F : apm_m03J01_E n → ℝ) : apm_m03J01_weakSolution F (apm_m03J01_zeroH01 n Ω) ↔ ∀ v : apm_m03J01_H01 n Ω, ∫ x, F x * v.val x ∂volume = 0` |
| `apm_m03J01_zero_H2size` | m03J01 | `(n : ℕ) (Ω : Set (apm_m03J01_E n)) : apm_m03J01_H2size (apm_m03J01_zeroH01 n Ω) (0 : apm_m03J01_E n → Fin n → Fin n → ℝ) = 0` |
| `apm_m03J01_zero_weakHessian` | m03J01 | `(n : ℕ) (Ω : Set (apm_m03J01_E n)) : apm_m03J01_weakHessian (apm_m03J01_zeroH01 n Ω).grad (0 : apm_m03J01_E n → Fin n → Fin n → ℝ)` |
| `apm_m03J04_closure_range_subset_dualAnnihilator` | m03J04 | `{V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] (B : V →L[ℝ] W →L[ℝ] ℝ) : closure (B.range : Set (W →L[ℝ] ℝ)) ⊆ (dualAnnihilator ((dualAdjoint B).ker : Set W) : Set (W →L[ℝ] ℝ))` |
| `apm_m03J04_range_subset_dualAnnihilator` | m03J04 | `{V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] (B : V →L[ℝ] W →L[ℝ] ℝ) : (B.range : Set (W →L[ℝ] ℝ)) ⊆ (dualAnnihilator ((dualAdjoint B).ker : Set W) : Set (W →L[ℝ] ℝ))` |
| `apm_m93A01_circleDerivH1_not_compact` | m93A01 | `(D1 : apm_m93A01_l2Z →L[ℂ] apm_m93A01_l2Z) (hD1 : ∀ (f : apm_m93A01_l2Z) (n : ℤ), D1 f n = apm_m93A01_circleDerivH1Coeff n * f n) : ¬ IsCompactOperator D1` |
| `apm_m93A01_circleDerivH1Coeff_lower` | m93A01 | `(n : ℕ) : (1 / 2 : ℝ) ≤ ‖apm_m93A01_circleDerivH1Coeff (n + 1)‖` |
| `apm_m93A01_diagonal_single` | m93A01 | `(A : apm_m93A01_l2Z →L[ℂ] apm_m93A01_l2Z) (c : ℤ → ℂ) (hA : ∀ (f : apm_m93A01_l2Z) (n : ℤ), A f n = c n * f n) (n : ℤ) : A (lp.single 2 n (1 : ℂ)) = c n • lp.single 2 n (1 : ℂ)` |
| `apm_m93A01_norm_diagonal_single` | m93A01 | `(A : apm_m93A01_l2Z →L[ℂ] apm_m93A01_l2Z) (c : ℤ → ℂ) (hA : ∀ (f : apm_m93A01_l2Z) (n : ℤ), A f n = c n * f n) (n : ℤ) : ‖A (lp.single 2 n (1 : ℂ))‖ = ‖c n‖` |
| `apm_m93A01_norm_single` | m93A01 | `(n : ℤ) : ‖(lp.single 2 n (1 : ℂ) : apm_m93A01_l2Z)‖ = 1` |
| `apm_m93A01_not_compact_of_pos_separated_unit` | m93A01 | `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (A : E →L[ℂ] E) (u : ℕ → E) {δ : ℝ} (hδ : 0 < δ) (hu : ∀ n, ‖u n‖ ≤ 1) (hsep : ∀ n m, n ≠ m → δ ≤ dist (A (u n)) (A (u m))) : ¬ IsCompactOperator A` |
| `apm_m93A01_not_compact_of_separated_unit` | m93A01 | `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (A : E →L[ℂ] E) (u : ℕ → E) (hu : ∀ n, ‖u n‖ ≤ 1) (hsep : ∀ n m, n ≠ m → 1 ≤ dist (A (u n)) (A (u m))) : ¬ IsCompactOperator A` |
| `apm_m93a02_contraction_constants` | m93A02 | `{δ M q : ℝ} (hδ : 0 < δ) (hM : 0 < M) (hq : 0 ≤ q) (hqsmall : q < δ ^ 2 / (8 * M)) : δ⁻¹ * (q + M * (2 * q / δ) ^ 2) ≤ 2 * q / δ ∧ δ⁻¹ * M * (2 * (2 * q / δ)) < 1 / 2` |
| `apm_m93a02_quadratic_sub_bound` | m93A02 | `{H K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup K] [NormedSpace ℝ K] (Q : H →ₗ[ℝ] H →ₗ[ℝ] K) (M : ℝ) (hQ : ∀ h₁ h₂ : H, ‖Q h₁ h₂‖ ≤ M * ‖h₁‖ * ‖h₂‖) (x y : H) : ‖Q x x - Q y y‖ ≤ M * (‖x‖ + ‖y‖) * ‖x - y‖` |
| `apm_m93A04_bijective_D` | m93A04 | `(K₂ : ℝ → ℝ → ℝ) (hK₂ : Continuous (Function.uncurry K₂)) (c : ℝ) (hc_nonneg : 0 ≤ c) (hc : c < 1) (hsmall : ∀ t u : ℝ, \|K₂ t u\| ≤ c) (D : apm_m93A04_C → apm_m93A04_C →L[ℝ] apm_m93A04_C) (hD : ∀ (x h : apm_m93A04_C) (t : apm_m93A04_I), D x h t = h t - ∫ s : apm_m93A04_I, K₂ t.1 (x s) * h s) (x : apm_m93A04_C) : Function.Bijective (D x)` |
| `apm_m93A04_bijective_one_sub_of_norm_lt_one` | m93A04 | `(T : apm_m93A04_C →L[ℝ] apm_m93A04_C) (hT : ‖T‖ < 1) : Function.Bijective ((1 : apm_m93A04_C →L[ℝ] apm_m93A04_C) - T)` |
| `apm_m93A04_norm_D_le` | m93A04 | `(K₂ : ℝ → ℝ → ℝ) (hK₂ : Continuous (Function.uncurry K₂)) (c : ℝ) (hc_nonneg : 0 ≤ c) (hsmall : ∀ t u : ℝ, \|K₂ t u\| ≤ c) (D : apm_m93A04_C → apm_m93A04_C →L[ℝ] apm_m93A04_C) (hD : ∀ (x h : apm_m93A04_C) (t : apm_m93A04_I), D x h t = h t - ∫ s : apm_m93A04_I, K₂ t.1 (x s) * h s) (x : apm_m93A04_C) : ‖D x‖ ≤ 1 + c` |
| `apm_m93A04_norm_one_sub_D_le` | m93A04 | `(K₂ : ℝ → ℝ → ℝ) (hK₂ : Continuous (Function.uncurry K₂)) (c : ℝ) (hc_nonneg : 0 ≤ c) (hsmall : ∀ t u : ℝ, \|K₂ t u\| ≤ c) (D : apm_m93A04_C → apm_m93A04_C →L[ℝ] apm_m93A04_C) (hD : ∀ (x h : apm_m93A04_C) (t : apm_m93A04_I), D x h t = h t - ∫ s : apm_m93A04_I, K₂ t.1 (x s) * h s) (x : apm_m93A04_C) : ‖(1 : apm_m93A04_C →L[ℝ] apm_m93A04_C) - D x‖ ≤ c` |
| `apm_m93J01_centered6_isBigO` | m93J01 | `(y : ℝ → ℝ) (hy : ContDiff ℝ 6 y) (x : ℝ) : (fun h : ℝ ↦ y (x + h) + y (x - h) - 2 * y x - (h ^ 2 * iteratedDeriv 2 y x + apm_m93J01_kappa * h ^ 4 * iteratedDeriv 4 y x)) =O[nhds 0] (fun h : ℝ ↦ h ^ 6)` |
| `apm_m93J01_schrodinger_residual_eq` | m93J01 | `(y V : ℝ → ℝ) (x h : ℝ) : h ^ 2 * apm_m93J01_schrodinger V y x - (-y (x + h) - y (x - h) + (2 + h ^ 2 * V x) * y x + apm_m93J01_kappa * h ^ 4 * iteratedDeriv 4 y x) = y (x + h) + y (x - h) - 2 * y x - (h ^ 2 * iteratedDeriv 2 y x + apm_m93J01_kappa * h ^ 4 * iteratedDeriv 4 y x)` |
| `apm_m93J01_taylor6_isLittleO` | m93J01 | `(y : ℝ → ℝ) (hy : ContDiff ℝ 6 y) (x : ℝ) : (fun h : ℝ ↦ y (x + h) - (y x + h * iteratedDeriv 1 y x + h ^ 2 / 2 * iteratedDeriv 2 y x + h ^ 3 / 6 * iteratedDeriv 3 y x + h ^ 4 / 24 * iteratedDeriv 4 y x + h ^ 5 / 120 * iteratedDeriv 5 y x + h ^ 6 / 720 * iteratedDeriv 6 y x)) =o[nhds 0] (fun h : ℝ ↦ h ^ 6)` |
| `apm_m93J02_eq_zero_of_supNorm_eq_zero` | m93J02 | `{n : ℕ} {U : Set (Fin n → ℝ)} {f : U → ℝ} (hf : apm_m93J02_supNorm f = 0) : f = 0` |
| `apm_m93J02_eq_zero_of_toReal_add_eq_zero` | m93J02 | `{n : ℕ} {U : Set (Fin n → ℝ)} {f : U → ℝ} {s : ℝ≥0∞} (hfinite : s + apm_m93J02_supNorm f ≠ ⊤) (hzero : (s + apm_m93J02_supNorm f).toReal = 0) : f = 0` |
| `apm_m93J03_isSmall_mono` | m93J03 | `{x : ℝ → ℝ} {η η' : ℝ} (hx : apm_m93J03_isSmall x η) (hη : η ≤ η') : apm_m93J03_isSmall x η'` |
| `apm_m93J03_isSolution_affineTrig_of_residual_eq_zero` | m93J03 | `{ε a b : ℝ} (hres : apm_m93J03_residual ε (a, b) = 0) : apm_m93J03_isSolution ε (apm_m93J03_affineTrig ε a b)` |
| `apm_m93J03_solution_eq_affine_trig` | m93J03 | `{ε : ℝ} {x : ℝ → ℝ} (hx : apm_m93J03_isSolution ε x) : ∃ a b : ℝ, ∀ t ∈ Icc (-Real.pi) Real.pi, x t = ε + a * Real.sin t + b * Real.cos t` |
| `apm_m93J03_zero_isSmall` | m93J03 | `{η : ℝ} (hη : 0 < η) : apm_m93J03_isSmall (fun _ ↦ 0) η` |
| `apm_m93J04_branch_intervalIntegrable` | m93J04 | `(y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ⊤ φ) : IntervalIntegrable (fun x ↦ apm_m93J04_kernel x y * apm_m93J04_formalAdjoint φ x) volume 0 y ∧ IntervalIntegrable (fun x ↦ apm_m93J04_kernel x y * apm_m93J04_formalAdjoint φ x) volume y 1` |
| `apm_m93J04_formalAdjoint_continuous` | m93J04 | `(φ : ℝ → ℝ) (hφ : ContDiff ℝ ⊤ φ) : Continuous (apm_m93J04_formalAdjoint φ)` |
| `apm_m93J04_formalAdjoint_eq` | m93J04 | `(φ : ℝ → ℝ) (x : ℝ) : apm_m93J04_formalAdjoint φ x = x ^ 2 * deriv (deriv φ) x + 5 * x * deriv φ x + 4 * φ x` |
| `apm_m93J04_integral_Ioo_split` | m93J04 | `(f : ℝ → ℝ) {y : ℝ} (hleft : IntervalIntegrable f volume 0 y) (hright : IntervalIntegrable f volume y 1) : (∫ x in Ioo (0 : ℝ) 1, f x) = (∫ x in (0 : ℝ)..y, f x) + ∫ x in y..1, f x` |
| `apm_m93J04_kernel_derivative_jump` | m93J04 | `(y : ℝ) : (Real.log y + 1) / y ^ 2 - Real.log y / y ^ 2 = 1 / y ^ 2` |
| `apm_m93J04_kernel_of_le` | m93J04 | `{x y : ℝ} (hxy : x ≤ y) : apm_m93J04_kernel x y = x * Real.log y / y ^ 2` |
| `apm_m93J04_kernel_of_lt` | m93J04 | `{x y : ℝ} (hyx : y < x) : apm_m93J04_kernel x y = x * Real.log x / y ^ 2` |
| `apm_m93J04_testFunction_endpoints` | m93J04 | `(φ : ℝ → ℝ) (hsupp : Function.support φ ⊆ Ioo (0 : ℝ) 1) : φ 0 = 0 ∧ deriv φ 0 = 0 ∧ φ 1 = 0 ∧ deriv φ 1 = 0` |
| `apm_m93j06_abs_sqrt_sub_sqrt_le_sqrt_abs_sub` | m93J06 | `{u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : \|Real.sqrt u - Real.sqrt v\| ≤ Real.sqrt \|u - v\|` |
| `apm_m93j06_flow_distance_zero` | m93J06 | `{f φ : ℝ → ℝ → ℝ} (hφ : apm_m93j06_IsFlow f φ) (L a b : ℝ) : \|φ 0 a - φ 0 b\| = Real.exp (L * \|(0 : ℝ)\|) * \|a - b\|` |
| `apm_m93j06_flow_hasDerivAt` | m93J06 | `{f φ : ℝ → ℝ → ℝ} (hφ : apm_m93j06_IsFlow f φ) (y₀ t : ℝ) : HasDerivAt (fun s ↦ φ s y₀) (f t (φ t y₀)) t` |
| `apm_m93j06_flow_zero` | m93J06 | `{f φ : ℝ → ℝ → ℝ} (hφ : apm_m93j06_IsFlow f φ) (y₀ : ℝ) : φ 0 y₀ = y₀` |
| `apm_m93j06_hasDerivAt_mul_abs` | m93J06 | `(t : ℝ) : HasDerivAt (fun s : ℝ ↦ s * \|s\|) (2 * \|t\|) t` |
| `apm_m93j06_not_holder_unique` | m93J06 | `: ¬ ∀ α : ℝ, 0 < α → α < 1 → ∀ f : ℝ → ℝ → ℝ, (∃ K > 0, ∀ t a b, \|f t a - f t b\| ≤ K * Real.rpow \|a - b\| α) → ∀ y₀, ∃! y : ℝ → ℝ, apm_m93j06_Solves f y₀ y` |
| `apm_m93j06_signedSquare_ne_zero` | m93J06 | `: (fun t : ℝ ↦ t * \|t\|) ≠ fun _ ↦ 0` |
| `apm_m93j06_signedSquare_solves_sqrt` | m93J06 | `: apm_m93j06_Solves (fun _ y ↦ 2 * Real.sqrt \|y\|) 0 (fun t ↦ t * \|t\|)` |
| `apm_m93j06_sqrt_abs_mul_abs` | m93J06 | `(t : ℝ) : Real.sqrt \|t * abs t\| = \|t\|` |
| `apm_m93j06_sqrt_field_holder` | m93J06 | `(t a b : ℝ) : \|2 * Real.sqrt (\|a\|) - 2 * Real.sqrt (\|b\|)\| ≤ 2 * Real.rpow (\|a - b\|) (1 / 2 : ℝ)` |
| `apm_m93j06_zero_solves_sqrt` | m93J06 | `: apm_m93j06_Solves (fun _ y ↦ 2 * Real.sqrt \|y\|) 0 (fun _ ↦ 0)` |
| `apm_m93J07_local_power_four_not_integrable` | m93J07 | `: ¬ IntegrableOn (fun x : ℝ => x ^ (-4 / 3 : ℝ)) (Set.Ioo 0 1) volume` |
| `apm_m93J07_local_power_two_integrable` | m93J07 | `: IntegrableOn (fun x : ℝ => x ^ (-2 / 3 : ℝ)) (Set.Ioo 0 1) volume` |
| `apm_m93J07_localWitness_aestronglyMeasurable` | m93J07 | `: AEStronglyMeasurable apm_m93J07_localWitness volume` |
| `apm_m93J07_localWitness_memLp_two` | m93J07 | `: MemLp apm_m93J07_localWitness 2 volume` |
| `apm_m93J07_localWitness_not_memLp_four` | m93J07 | `: ¬ MemLp apm_m93J07_localWitness 4 volume` |
| `apm_m93J07_tail_power_four_integrable` | m93J07 | `: IntegrableOn (fun x : ℝ => x ^ (-4 / 3 : ℝ)) (Set.Ioi 1) volume` |
| `apm_m93J07_tail_power_two_not_integrable` | m93J07 | `: ¬ IntegrableOn (fun x : ℝ => x ^ (-2 / 3 : ℝ)) (Set.Ioi 1) volume` |
| `apm_m94a01_centered2_isBigO` | m94A01 | `(f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (x : ℝ) : (fun h : ℝ ↦ f (x + h) + f (x - h) - 2 * f x - h ^ 2 * iteratedDeriv 2 f x) =O[nhds 0] (fun h : ℝ ↦ h ^ 4)` |
| `apm_m94a01_contDiff_slice_fst` | m94A01 | `(u : ℝ × ℝ → ℝ) (hu : ContDiff ℝ 4 u) (y : ℝ) : ContDiff ℝ 4 (fun s : ℝ => u (s, y))` |
| `apm_m94a01_contDiff_slice_snd` | m94A01 | `(u : ℝ × ℝ → ℝ) (hu : ContDiff ℝ 4 u) (x : ℝ) : ContDiff ℝ 4 (fun s : ℝ => u (x, s))` |
| `apm_m94a01_iteratedDeriv_two` | m94A01 | `(f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f)` |
| `apm_m94a01_taylor4_isLittleO` | m94A01 | `(f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (x : ℝ) : (fun h : ℝ ↦ f (x + h) - (f x + h * iteratedDeriv 1 f x + h ^ 2 / 2 * iteratedDeriv 2 f x + h ^ 3 / 6 * iteratedDeriv 3 f x + h ^ 4 / 24 * iteratedDeriv 4 f x)) =o[nhds 0] (fun h : ℝ ↦ h ^ 4)` |
| `apm_m94a02_I_smul_map_isHermitian_of_transpose_eq_neg` | m94A02 | `{n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.transpose = -A) : (Complex.I • A.map (algebraMap ℝ ℂ)).IsHermitian` |
| `apm_m94a02_map_conjTranspose_eq_neg_of_transpose_eq_neg` | m94A02 | `{n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.transpose = -A) : (A.map (algebraMap ℝ ℂ))ᴴ = -(A.map (algebraMap ℝ ℂ))` |
| `apm_m94a02_symmetricPart_eq_zero_of_transpose_eq_neg` | m94A02 | `{n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.transpose = -A) : apm_m94a02_symmetricPart A = 0` |
| `apm_m94a02_symmetricPart_isHermitian` | m94A02 | `{n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : (apm_m94a02_symmetricPart A).IsHermitian` |
| `apm_m94a02_symmetricPart_map_isHermitian` | m94A02 | `{n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ((apm_m94a02_symmetricPart A).map (algebraMap ℝ ℂ)).IsHermitian` |
| `apm_m94a02_symmetricPart_transpose` | m94A02 | `{n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : (apm_m94a02_symmetricPart A).transpose = apm_m94a02_symmetricPart A` |
| `apm_m94a03_invNorm_memLp_two_ball_fin_three` | m94A03 | `: MemLp (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖⁻¹) 2 (volume.restrict (Metric.ball 0 1))` |
| `apm_m94a03_logNorm_aestronglyMeasurable` | m94A03 | `{n : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin n))} : AEStronglyMeasurable (apm_m94a03_logNorm : EuclideanSpace ℝ (Fin n) → ℝ) μ` |
| `apm_m94a03_logNormGradient_aestronglyMeasurable` | m94A03 | `{n : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin n))} : AEStronglyMeasurable (apm_m94a03_logNormGradient : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) μ` |
| `apm_m94a03_logNormGradient_memLp_iff` | m94A03 | `{n : ℕ} {p : ℝ≥0∞} {μ : Measure (EuclideanSpace ℝ (Fin n))} : MemLp (apm_m94a03_logNormGradient : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) p μ ↔ MemLp (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖⁻¹) p μ` |
| `apm_m94a03_logNormGradient_memLp_two_ball_fin_three` | m94A03 | `: MemLp (apm_m94a03_logNormGradient : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) 2 (volume.restrict (Metric.ball 0 1))` |
| `apm_m94a03_norm_logNormGradient` | m94A03 | `{n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) : ‖apm_m94a03_logNormGradient x‖ = ‖x‖⁻¹` |
| `apm_m94a03_norm_logNormGradient_all` | m94A03 | `{n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ‖apm_m94a03_logNormGradient x‖ = ‖x‖⁻¹` |
| `apm_m94a04_cube_coeFn` | m94A04 | `(f : Lp ℝ 8 apm_m94a04_measure) : (apm_m94a04_cube f : ℝ → ℝ) =ᵐ[apm_m94a04_measure] fun t ↦ (f t) ^ 3` |
| `apm_m94a04_cubic_remainder` | m94A04 | `(a b : ℝ) : (a + b) ^ 3 - a ^ 3 - 3 * a ^ 2 * b = 3 * a * b ^ 2 + b ^ 3` |
| `apm_m94a04_norm_cube_le` | m94A04 | `(f : Lp ℝ 8 apm_m94a04_measure) : ‖apm_m94a04_cube f‖ ≤ ‖f‖ ^ 3` |
| `apm_m94a04_norm_square_le` | m94A04 | `(f : Lp ℝ 8 apm_m94a04_measure) : ‖apm_m94a04_square f‖ ≤ ‖f‖ ^ 2` |
| `apm_m94a04_square_coeFn` | m94A04 | `(f : Lp ℝ 8 apm_m94a04_measure) : (apm_m94a04_square f : ℝ → ℝ) =ᵐ[apm_m94a04_measure] fun t ↦ (f t) ^ 2` |
| `apm_m94a05_abs_extend_le_norm` | m94A05 | `(u : apm_m94a05_space) (s : ℝ) : \|apm_m94a05_extend u s\| ≤ ‖u‖` |
| `apm_m94a05_abs_picardMap_le` | m94A05 | `{ε : ℝ} (hε : 0 ≤ ε) (u : apm_m94a05_space) (t : apm_m94a05_interval) : \|apm_m94a05_picardMap ε u t\| ≤ ε + Real.pi * ‖u‖ ^ 2` |
| `apm_m94a05_extend_apply_of_mem` | m94A05 | `(u : apm_m94a05_space) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) Real.pi) : apm_m94a05_extend u s = u ⟨s, hs⟩` |
| `apm_m94a05_extend_continuous` | m94A05 | `(u : apm_m94a05_space) : Continuous (apm_m94a05_extend u)` |
| `apm_m94a05_kernel_square_le` | m94A05 | `(u : ℝ → ℝ) {R t s : ℝ} (hu : \|u s\| ≤ R) : \|Real.sin (t * s) * (u s) ^ 2\| ≤ R ^ 2` |
| `apm_m94a05_kernel_square_sub_le` | m94A05 | `(u v : ℝ → ℝ) {R t s : ℝ} (hu : \|u s\| ≤ R) (hv : \|v s\| ≤ R) : \|Real.sin (t * s) * ((u s) ^ 2 - (v s) ^ 2)\| ≤ (2 * R) * \|u s - v s\|` |
| `apm_m94a05_norm_picardMap_le` | m94A05 | `{ε : ℝ} (hε : 0 ≤ ε) (u : apm_m94a05_space) : ‖apm_m94a05_picardMap ε u‖ ≤ ε + Real.pi * ‖u‖ ^ 2` |
| `apm_m94a05_picard_continuous` | m94A05 | `(ε : ℝ) {u : ℝ → ℝ} (hu : ContinuousOn u (Icc 0 Real.pi)) : Continuous (apm_m94a05_picard ε u)` |
| `apm_m94a05_picard_integrable` | m94A05 | `{u : ℝ → ℝ} (hu : ContinuousOn u (Icc 0 Real.pi)) (t : ℝ) : IntervalIntegrable (fun s : ℝ ↦ Real.sin (t * s) * (u s) ^ 2) volume 0 Real.pi` |
| `apm_m94J01_localSummand_eq_zero_of_half_le` | m94J01 | `(n : ℕ) (x : ℝ) (hx : (1 / 2 : ℝ) ≤ \|x - n\|) : apm_m94J01_localSummand n x = 0` |
| `apm_m94J01_localSummand_eventuallyEq` | m94J01 | `(n : ℕ) : apm_m94J01_localSummand n =ᶠ[nhds (n : ℝ)] (fun x : ℝ ↦ (x - n) ^ n / n.factorial)` |
| `apm_m94J01_localSummand_iteratedDeriv` | m94J01 | `(n : ℕ) : iteratedDeriv n (apm_m94J01_localSummand n) (n : ℝ) = 1` |
| `apm_m94J01_negOnePow_not_tendsto` | m94J01 | `(a : ℂ) : ¬ Tendsto (fun n : ℕ ↦ (-1 : ℂ) ^ n) atTop (nhds a)` |
| `apm_m94J01_normalizedMonomial_iteratedDeriv` | m94J01 | `(n : ℕ) : iteratedDeriv n (fun x : ℝ ↦ (x - n) ^ n / n.factorial) (n : ℝ) = 1` |
| `apm_m94J02_diagonal_range_subset_spectrum` | m94J02 | `: Set.range (fun n : ℕ ↦ (2 : ℂ) ^ (-(n : ℤ))) ⊆ apm_m94J02_spectrum` |
| `apm_m94J02_eigenvalue_mem_spectrum` | m94J02 | `(j : ℕ) : (2 : ℂ) ^ (-(j : ℤ)) ∈ apm_m94J02_spectrum` |
| `apm_m94J02_norm_T_le` | m94J02 | `(a : ℕ → ℂ) (ha : apm_m94J02_mem a) : apm_m94J02_norm (apm_m94J02_T a) ≤ apm_m94J02_norm a` |
| `apm_m94J04_f_of_nonpos` | m94J04 | `{p : apm_m94J04_E} (hp : p 0 ≤ 0) : apm_m94J04_f p = p 0` |
| `apm_m94J04_f_of_pos` | m94J04 | `{p : apm_m94J04_E} (hp : 0 < p 0) : apm_m94J04_f p = p 1` |
| `apm_m94J04_inner_curlValue` | m94J04 | `(φ : apm_m94J04_E → apm_m94J04_E) (p : apm_m94J04_E) : inner ℝ (apm_m94J04_curlValue p) (φ p) = (if 0 < p 0 then -φ p 2 else 0)` |
| `apm_m94J04_inner_u_curlTest` | m94J04 | `(φ : apm_m94J04_E → apm_m94J04_E) (p : apm_m94J04_E) : inner ℝ (apm_m94J04_u p) (apm_m94J04_curlTest φ p) = apm_m94J04_f p * (fderiv ℝ (fun q ↦ φ q 2) p (apm_m94J04_basis 1) - fderiv ℝ (fun q ↦ φ q 1) p (apm_m94J04_basis 2))` |
| `apm_m94J04_slice_hasDerivAt` | m94J04 | `(φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E) apm_m94J04_E ⊤) (p : apm_m94J04_E) (i j : Fin 3) (r : ℝ) : HasDerivAt (fun s : ℝ ↦ φ (p + s • apm_m94J04_basis i) j) (fderiv ℝ (fun q ↦ φ q j) (p + r • apm_m94J04_basis i) (apm_m94J04_basis i)) r` |
| `apm_m94J04_sliceLine_isometry` | m94J04 | `(p : apm_m94J04_E) (i : Fin 3) : Isometry (fun s : ℝ ↦ p + s • apm_m94J04_basis i)` |
| `apm_m95A04_Dtest_injective` | m95A04 | `(Dtest : apm_m95A04_Test →ₗ[ℝ] apm_m95A04_Test) (hDtest : ∀ (φ : apm_m95A04_Test) (x : ℝ), Dtest φ x = deriv φ x) : Function.Injective Dtest` |
| `apm_m95A04_regular_iff_ae` | m95A04 | `(regular : (ℝ → ℝ) → apm_m95A04_Dist) (hregular : ∀ (f : ℝ → ℝ), LocallyIntegrable f volume → ∀ φ : apm_m95A04_Test, regular f φ = ∫ x : ℝ, f x * φ x) (f g : ℝ → ℝ) (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume) : regular f = regular g ↔ f =ᵐ[volume] g` |
| `apm_m95a05_injective` | m95A05 | `{V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (A : V →L[ℝ] StrongDual ℝ V) (c : ℝ) (hc : 0 < c) (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v) : Function.Injective A` |
| `apm_m95a05_isClosed_range` | m95A05 | `{V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (A : V →L[ℝ] StrongDual ℝ V) (c : ℝ) (hc : 0 < c) (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v) : IsClosed (Set.range A)` |
| `apm_m95a05_norm_le_apply` | m95A05 | `{V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (A : V →L[ℝ] StrongDual ℝ V) (c : ℝ) (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v) (v : V) : c * ‖v‖ ≤ ‖A v‖` |
| `apm_m95a05_separator_vanishes_on_range` | m95A05 | `{V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (A : V →L[ℝ] StrongDual ℝ V) (F : StrongDual ℝ (StrongDual ℝ V)) (u : ℝ) (hF : ∀ y ∈ Set.range A, F y < u) (v : V) : F (A v) = 0` |
| `apm_m95J01_complete_of_equiv` | m95J01 | `{n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (P : H ≃ₗ[ℝ] Polynomial.degreeLE ℝ n) : Nonempty (CompleteSpace H)` |
| `apm_m95J01_finrank_of_equiv` | m95J01 | `{n : ℕ} {H : Type*} [AddCommGroup H] [Module ℝ H] (P : H ≃ₗ[ℝ] Polynomial.degreeLE ℝ n) : Module.finrank ℝ H = n + 1` |
| `apm_m95J01_range_top_coeff_zero` | m95J01 | `{n : ℕ} {H : Type*} [AddCommGroup H] [Module ℝ H] (P : H ≃ₗ[ℝ] Polynomial.degreeLE ℝ n) (T : H →ₗ[ℝ] H) (hT : ∀ f : H, (P (T f) : Polynomial ℝ) = Polynomial.derivative (Polynomial.derivative (P f : Polynomial ℝ)) - 2 • Polynomial.derivative (P f : Polynomial ℝ) + (P f : Polynomial ℝ)) {f g : H} (hfg : T f - f = g) : (P g : Polynomial ℝ).coeff n = 0` |
| `apm_m95J01_top_coeff_derivative_sub` | m95J01 | `{n : ℕ} (p : Polynomial.degreeLE ℝ n) : (Polynomial.derivative (Polynomial.derivative (p : Polynomial ℝ)) - 2 • Polynomial.derivative (p : Polynomial ℝ)).coeff n = 0` |
| `apm_m95J02_fundamental_eq_radialProfile` | m95J02 | `(n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : apm_m95J02_fundamental n x = apm_m95J02_radialProfile n ‖x‖` |
| `apm_m95J02_fundamental_neg` | m95J02 | `{n : ℕ} (hn : 2 < n) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) : apm_m95J02_fundamental n x < 0` |
| `apm_m95J02_fundamental_two` | m95J02 | `(x : EuclideanSpace ℝ (Fin 2)) : apm_m95J02_fundamental 2 x = Real.log ‖x‖ / (2 * Real.pi)` |
| `apm_m95J02_hasDerivAt_radialProfile_of_two_lt` | m95J02 | `{n : ℕ} (hn : 2 < n) {r : ℝ} (hr : r ≠ 0) : HasDerivAt (apm_m95J02_radialProfile n) (-( (2 - (n : ℝ)) * Real.rpow r ((2 - (n : ℝ)) - 1)) / (((n : ℝ) - 2) * apm_m95J02_sphereArea n)) r` |
| `apm_m95J02_power_denominator_pos` | m95J02 | `{n : ℕ} (hn : 2 < n) : 0 < ((n : ℝ) - 2) * apm_m95J02_sphereArea n` |
| `apm_m95J02_sphereArea_pos` | m95J02 | `{n : ℕ} (hn : 0 < n) : 0 < apm_m95J02_sphereArea n` |
| `apm_m95J02_sphereArea_two` | m95J02 | `: apm_m95J02_sphereArea 2 = 2 * Real.pi` |
| `apm_m95J03_B_continuous` | m95J03 | `: Continuous apm_m95J03_B` |
| `apm_m95J03_B_zero_ne_zero` | m95J03 | `: apm_m95J03_B 0 ≠ 0` |
| `apm_m95J03_B_zero_pow_four` | m95J03 | `: apm_m95J03_B 0 ^ 4 = 0` |
| `apm_m95J03_B_zero_pow_three_ne_zero` | m95J03 | `: apm_m95J03_B 0 ^ 3 ≠ 0` |
| `apm_m95J03_diagonalJordan_tendsto_zero` | m95J03 | `: Tendsto apm_m95J03_diagonalJordan (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 0)` |
| `apm_m95J03_flow_zero` | m95J03 | `: apm_m95J03_flow 0 = 1` |
| `apm_m95J03_ivpSolution_zero` | m95J03 | `(v : Fin 4 → ℝ) : apm_m95J03_ivpSolution v 0 = v` |
| `apm_m95J03_leftInverse_solution` | m95J03 | `(m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (L : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (hLA : L * A = 1) : ((∃ x : Fin n → ℝ, A.mulVec x = b) ↔ A.mulVec (L.mulVec b) = b) ∧ (∀ x : Fin n → ℝ, A.mulVec x = b → x = L.mulVec b)` |
| `apm_m95J04_continuous_green_right` | m95J04 | `(t : ℝ) : Continuous (apm_m95J04_green t)` |
| `apm_m95J04_green_le_quarter` | m95J04 | `{t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) : apm_m95J04_green t s ≤ (1 / 4 : ℝ)` |
| `apm_m95J04_green_mass_polynomial_le` | m95J04 | `(t : ℝ) : t * (1 - t) / 2 ≤ (1 / 8 : ℝ)` |
| `apm_m95J04_green_nonneg` | m95J04 | `{t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) : 0 ≤ apm_m95J04_green t s` |
| `apm_m95J04_green_reflection` | m95J04 | `(t s : ℝ) : apm_m95J04_green (1 - t) (1 - s) = apm_m95J04_green t s` |
| `apm_m95J04_specific_continuous` | m95J04 | `: Continuous fun p : ℝ × ℝ ↦ apm_m95J04_specific p.1 p.2` |
| `apm_m95J04_specific_eq_cos` | m95J04 | `(t x : ℝ) : apm_m95J04_specific t x = (Real.cos (1 - 2 * t) - Real.cos (2 * x - 1)) / 2` |
| `apm_m95J04_specific_lipschitz` | m95J04 | `(t u v : ℝ) : \|apm_m95J04_specific t u - apm_m95J04_specific t v\| ≤ \|u - v\|` |
| `apm_m95J04_specific_reflection` | m95J04 | `(t x : ℝ) : apm_m95J04_specific (1 - t) x = apm_m95J04_specific t x` |
| `apm_m95J05_fundamental_isFundamentalKernel` | m95J05 | `(lam : ℝ) : apm_m95J05_isFundamentalKernel lam (apm_m95J05_fundamental lam)` |
| `apm_m95J06_abs_le_linfNorm` | m95J06 | `{n : ℕ} (x : Fin n → ℝ) (i : Fin n) : \|x i\| ≤ apm_m95j06_linfNorm x` |
| `apm_m95J06_differentiableAt_norm` | m95J06 | `(H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (x : H) (hx : x ≠ 0) : DifferentiableAt ℝ (fun y : H => ‖y‖) x` |
| `apm_m95J06_exists_abs_eq_linfNorm` | m95J06 | `{n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) : ∃ i, \|x i\| = apm_m95j06_linfNorm x` |
| `apm_m95J06_sum_rpow_le_card_mul_linfNorm_rpow` | m95J06 | `{n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) {p : ℝ} (hp : 0 ≤ p) : (∑ i, Real.rpow \|x i\| p) ≤ (n : ℝ) * Real.rpow (apm_m95j06_linfNorm x) p` |
| `apm_m95J06_tendsto_card_rpow_one_div` | m95J06 | `(n : ℕ) (hn : 0 < n) : Tendsto (fun p : ℝ => Real.rpow (n : ℝ) (1 / p)) atTop (nhds 1)` |
| `apm_m95j07_add_smul_cusp_not_differentiable` | m95J07 | `(f : apm_m95j07_C) (hf : apm_m95j07_DifferentiableAtZero f) (c : ℝ) (hc : c ≠ 0) : ¬ apm_m95j07_DifferentiableAtZero (f + c • apm_m95j07_cusp)` |
| `apm_m95j07_automatic_continuity` | m95J07 | `(X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (T : X →ₗ[ℝ] X) (A : X →L[ℝ] X) (hA : Function.Injective A) (hAT : Continuous fun x ↦ A (T x)) : Continuous T` |
| `apm_m95j07_cusp_not_differentiable` | m95J07 | `: ¬ apm_m95j07_DifferentiableAtZero apm_m95j07_cusp` |
| `apm_m95j07_norm_cusp` | m95J07 | `: ‖apm_m95j07_cusp‖ = 1` |
| `apm_m95j07_smul_cusp_not_differentiable` | m95J07 | `(c : ℝ) (hc : c ≠ 0) : ¬ apm_m95j07_DifferentiableAtZero (c • apm_m95j07_cusp)` |
| `apm_m96a05_diagonal_norm_gt_two` | m96A05 | `{n : ℕ} (hn : 0 < n) (a b : ℝ → ℝ) (hbneg : ∀ t ∈ Icc (0 : ℝ) 1, b t < 0) (i : Fin n) : 2 < ‖apm_m96a05_matrix n a b i i‖` |
| `apm_m96a05_matrix_eq_zero_of_not_neighbor` | m96A05 | `{n : ℕ} (a b : ℝ → ℝ) (i j : Fin n) (hji : j ≠ i) (hpred : j.val + 1 ≠ i.val) (hsucc : i.val + 1 ≠ j.val) : apm_m96a05_matrix n a b i j = 0` |
| `apm_m96a05_meshValue_center` | m96A05 | `{n : ℕ} (U : Fin n → ℝ) (i : Fin n) : apm_m96a05_meshValue n U (i.val + 1) = U i` |
| `apm_m96a05_meshValue_pred` | m96A05 | `{n : ℕ} (U : Fin n → ℝ) (i : Fin n) (hi : 0 < i.val) : apm_m96a05_meshValue n U i.val = U ⟨i.val - 1, by omega⟩` |
| `apm_m96a05_meshValue_succ` | m96A05 | `{n : ℕ} (U : Fin n → ℝ) (i : Fin n) (hi : i.val + 1 < n) : apm_m96a05_meshValue n U (i.val + 2) = U ⟨i.val + 1, hi⟩` |
| `apm_m96a05_unique_of_det` | m96A05 | `{n : ℕ} {a b c : ℝ → ℝ} (hscheme : ∀ U : Fin n → ℝ, apm_m96a05_approximateSolution n a b c U ↔ Matrix.mulVec (apm_m96a05_matrix n a b) U = apm_m96a05_rhs n a c) (hdet : (apm_m96a05_matrix n a b).det ≠ 0) : ∃! U : Fin n → ℝ, apm_m96a05_approximateSolution n a b c U` |
| `apm_m96a06_eLpNorm_weighted_le` | m96A06 | `{α : Type*} [MeasurableSpace α] {μ : Measure α} (a : α → ℝ) (f : Lp ℝ 2 μ) : eLpNorm (fun t ↦ a t * f t) 2 μ ≤ eLpNorm a ⊤ μ * eLpNorm (fun t ↦ f t) 2 μ` |
| `apm_m96a06_forceCLM_apply` | m96A06 | `{α : Type*} [MeasurableSpace α] {μ : Measure α} (b : α → ℝ) (hb : MemLp b 2 μ) (g : Lp ℝ 2 μ) : apm_m96a06_forceCLM b hb g = ∫ t, b t * g t ∂μ` |
| `apm_m96a06_forceOnH_apply` | m96A06 | `{α H : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup H] [NormedSpace ℝ H] (value : H →L[ℝ] Lp ℝ 2 μ) (b : α → ℝ) (hb : MemLp b 2 μ) (h : H) : apm_m96a06_forceOnH value b hb h = ∫ t, b t * value h t ∂μ` |
| `apm_m96a06_integrable_force` | m96A06 | `{α : Type*} [MeasurableSpace α] {μ : Measure α} (b : α → ℝ) (hb : MemLp b 2 μ) (g : Lp ℝ 2 μ) : Integrable (fun t => b t * g t) μ` |
| `apm_m96a06_integrable_pair` | m96A06 | `{α : Type*} [MeasurableSpace α] {μ : Measure α} (f g : Lp ℝ 2 μ) : Integrable (fun t => f t * g t) μ` |
| `apm_m96a06_integrable_weighted_pair` | m96A06 | `{α : Type*} [MeasurableSpace α] {μ : Measure α} (a : α → ℝ) (ha : MemLp a ⊤ μ) (f g : Lp ℝ 2 μ) : Integrable (fun t => a t * f t * g t) μ` |
| `apm_m96a06_multiplier_apply` | m96A06 | `{α : Type*} [MeasurableSpace α] {μ : Measure α} (a : α → ℝ) (ha : MemLp a ⊤ μ) (f : Lp ℝ 2 μ) : (apm_m96a06_multiplier a ha f : α → ℝ) =ᵐ[μ] fun t ↦ a t * f t` |
| `apm_m96a06_multiplierCLM_apply` | m96A06 | `{α : Type*} [MeasurableSpace α] {μ : Measure α} (a : α → ℝ) (ha : MemLp a ⊤ μ) (f : Lp ℝ 2 μ) : apm_m96a06_multiplierCLM a ha f = apm_m96a06_multiplier a ha f` |
| `apm_m96a06_norm_multiplier_le` | m96A06 | `{α : Type*} [MeasurableSpace α] {μ : Measure α} (a : α → ℝ) (ha : MemLp a ⊤ μ) (f : Lp ℝ 2 μ) : ‖apm_m96a06_multiplier a ha f‖ ≤ ‖ha.toLp a‖ * ‖f‖` |
| `apm_m96j02_continuousOn_comp_graph` | m96J02 | `(g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2) {T : ℝ} {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 T)) : ContinuousOn (fun t => g t (y t)) (Set.Icc 0 T)` |
| `apm_m96j02_intervalIntegrable_comp_graph` | m96J02 | `(g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2) {T : ℝ} (hT : 0 ≤ T) {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 T)) : IntervalIntegrable (fun t => g t (y t)) volume 0 T` |
| `apm_m96j03_coordinate_second_derivative` | m96J03 | `{n : ℕ} (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : apm_m96j03_E n) (i : Fin n) : fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) = iteratedFDeriv ℝ 2 φ x ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]` |
| `apm_m96j03_integral_ballIndicator` | m96J03 | `{n : ℕ} (g : apm_m96j03_E n → ℝ) : (∫ x, apm_m96j03_ballIndicator x * g x) = ∫ x in Metric.closedBall 0 1, g x` |
| `apm_m96j03_laplacian_const` | m96J03 | `{n : ℕ} (c : ℝ) (x : apm_m96j03_E n) : apm_m96j03_laplacian (fun _ ↦ c) x = 0` |
| `apm_m96j03_measurable_ballIndicator` | m96J03 | `{n : ℕ} : Measurable (apm_m96j03_ballIndicator : apm_m96j03_E n → ℝ)` |
| `apm_m96j03_zero_dim` | m96J03 | `(φ : apm_m96j03_E 0 → ℝ) : (∫ x : apm_m96j03_E 0, apm_m96j03_ballIndicator x * apm_m96j03_laplacian φ x) = ∫ x : apm_m96j03_E 0 in Metric.sphere 0 1, fderiv ℝ φ x x ∂μH[(0 - 1 : ℕ)]` |
| `apm_m96j04_block_exists` | m96J04 | `: ∃ A : apm_m96j04_H →L[ℝ] apm_m96j04_H, (∀ x y : ℓ²(ℕ, ℝ), A (x, y) = (y, 0)) ∧ ∀ n : ℕ, 2 ≤ n → IsCompactOperator (A ^ n)` |
| `apm_m96j04_eigenvector_hasDerivAt` | m96J04 | `(V : apm_m96j04_C →L[ℝ] apm_m96j04_C) (hV : ∀ (f : apm_m96j04_C) (t : Set.Icc (0 : ℝ) 1), V f t = ∫ s in (0 : ℝ)..(t : ℝ), apm_m96j04_extend f s) (eigenvalue : ℝ) (heigen : eigenvalue ≠ 0) (f : apm_m96j04_C) (hf : V f = eigenvalue • f) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : HasDerivAt (apm_m96j04_extend f) (apm_m96j04_extend f t / eigenvalue) t` |
| `apm_m96j04_eigenvector_zero_at_zero` | m96J04 | `(V : apm_m96j04_C →L[ℝ] apm_m96j04_C) (hV : ∀ (f : apm_m96j04_C) (t : Set.Icc (0 : ℝ) 1), V f t = ∫ s in (0 : ℝ)..(t : ℝ), apm_m96j04_extend f s) (eigenvalue : ℝ) (heigen : eigenvalue ≠ 0) (f : apm_m96j04_C) (hf : V f = eigenvalue • f) : f ⟨0, by norm_num⟩ = 0` |
| `apm_m96j04_extend_continuousOn` | m96J04 | `(f : apm_m96j04_C) : ContinuousOn (apm_m96j04_extend f) (Set.Icc (0 : ℝ) 1)` |
| `apm_m96j04_extend_intervalIntegrable` | m96J04 | `(f : apm_m96j04_C) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : IntervalIntegrable (apm_m96j04_extend f) MeasureTheory.volume 0 t` |
| `apm_m96j04_integral_hasDerivAt` | m96J04 | `(f : apm_m96j04_C) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : HasDerivAt (fun u ↦ ∫ s in (0 : ℝ)..u, apm_m96j04_extend f s) (apm_m96j04_extend f t) t` |
| `apm_m96j05_differenceSymbol_tendsto` | m96J05 | `(ξ : ℝ) : Tendsto (fun ε : ℝ => apm_m96j05_differenceSymbol ε ξ) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Complex.I * ξ))` |
| `apm_m96j05_exp_differenceSymbol_mul_tendsto` | m96J05 | `(ξ : ℝ) (z : ℂ) : Tendsto (fun ε : ℝ => Complex.exp (apm_m96j05_differenceSymbol ε ξ) * z) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (apm_m96j05_shiftSymbol ξ * z))` |
| `apm_m96j05_exp_differenceSymbol_tendsto` | m96J05 | `(ξ : ℝ) : Tendsto (fun ε : ℝ => Complex.exp (apm_m96j05_differenceSymbol ε ξ)) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (apm_m96j05_shiftSymbol ξ))` |
| `apm_m96j05_pow_apply_ae` | m96J05 | `(A : apm_m96j05_L2 →L[ℂ] apm_m96j05_L2) (m : ℝ → ℂ) (hA : ∀ f : apm_m96j05_L2, (fun ξ : ℝ => A f ξ) =ᵐ[volume] fun ξ => m ξ * f ξ) : ∀ (n : ℕ) (f : apm_m96j05_L2), (fun ξ : ℝ => (A ^ n) f ξ) =ᵐ[volume] fun ξ => m ξ ^ n * f ξ` |
| `apm_m96j05_symbol_norms` | m96J05 | `(ε ξ : ℝ) : ‖Complex.exp (apm_m96j05_differenceSymbol ε ξ)‖ = 1 ∧ ‖apm_m96j05_shiftSymbol ξ‖ = 1` |
| `apm_m96J06_half_shift_mem` | m96J06 | `{t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) : t / 2 + 1 ∈ Icc (-2 : ℝ) 2 ∧ t / 2 - 1 ∈ Icc (-2 : ℝ) 2` |
| `apm_m96J06_linearPart_involutive` | m96J06 | `(x : ℝ → ℝ) : apm_m96J06_linearPart (apm_m96J06_linearPart x) = x` |
| `apm_m96J06_linearPartC_involutive` | m96J06 | `(x : C(apm_m96J06_interval, ℝ)) : apm_m96J06_linearPartC (apm_m96J06_linearPartC x) = x` |
| `apm_m96J06_linearPartC_norm_le` | m96J06 | `(x : C(apm_m96J06_interval, ℝ)) : ‖apm_m96J06_linearPartC x‖ ≤ 3 * ‖x‖` |
| `apm_m96J06_linearPartCLM_involutive` | m96J06 | `(x : C(apm_m96J06_interval, ℝ)) : apm_m96J06_linearPartCLM (apm_m96J06_linearPartCLM x) = x` |
| `apm_m96J06_quadratic_continuousOn` | m96J06 | `{x : ℝ → ℝ} (hx : ContinuousOn x (Icc (-2 : ℝ) 2)) : ContinuousOn (fun t ↦ x (t / 2 + 1) * x (t / 2 - 1)) (Icc (-2 : ℝ) 2)` |
| `apm_m96J06_quadratic_sub_bound` | m96J06 | `{x z : ℝ → ℝ} {r : ℝ} (hr : 0 ≤ r) (hx : ∀ t ∈ Icc (-2 : ℝ) 2, \|x t\| ≤ r) (hz : ∀ t ∈ Icc (-2 : ℝ) 2, \|z t\| ≤ r) {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) : \|x (t / 2 + 1) * x (t / 2 - 1) - z (t / 2 + 1) * z (t / 2 - 1)\| ≤ 2 * r * max \|x (t / 2 + 1) - z (t / 2 + 1)\| \|x (t / 2 - 1) - z (t / 2 - 1)\|` |
| `apm_m96J06_quadraticC_norm_le` | m96J06 | `(x : C(apm_m96J06_interval, ℝ)) {r : ℝ} (hr : 0 ≤ r) (hx : ‖x‖ ≤ r) : ‖apm_m96J06_quadraticC x‖ ≤ r ^ 2` |
| `apm_m96J06_quadraticC_sub_norm_le` | m96J06 | `(x z : C(apm_m96J06_interval, ℝ)) {r : ℝ} (hr : 0 ≤ r) (hx : ‖x‖ ≤ r) (hz : ‖z‖ ≤ r) : ‖apm_m96J06_quadraticC x - apm_m96J06_quadraticC z‖ ≤ 2 * r * ‖x - z‖` |
| `apm_m97A01_modulus_core` | m97A01 | `(X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (A : X →L[ℂ] X) : ∃ B : X →L[ℂ] X, B.IsPositive ∧ B.comp B = (ContinuousLinearMap.adjoint A).comp A ∧ ∀ C : X →L[ℂ] X, C.IsPositive → C.comp C = (ContinuousLinearMap.adjoint A).comp A → C = B` |
| `apm_m97A01_modulus_norm` | m97A01 | `{X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (A B : X →L[ℂ] X) (hB : B.IsPositive) (hB2 : B.comp B = (ContinuousLinearMap.adjoint A).comp A) (x : X) : ‖B x‖ = ‖A x‖` |
| `apm_m97A01_modulusInclusion_apply` | m97A01 | `{X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (B : X →L[ℂ] X) (x : X) : (apm_m97A01_modulusInclusion B x).1 = B x` |
| `apm_m97A01_polarOnRange_apply` | m97A01 | `{X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (A B : X →L[ℂ] X) (hnorm : ∀ x : X, ‖B x‖ = ‖A x‖) (x : X) : apm_m97A01_polarOnRange A B hnorm ⟨B x, LinearMap.mem_range_self _ x⟩ = A x` |
| `apm_m97A01_polarOnRange_norm` | m97A01 | `{X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (A B : X →L[ℂ] X) (hnorm : ∀ x : X, ‖B x‖ = ‖A x‖) (y : LinearMap.range B.toLinearMap) : ‖apm_m97A01_polarOnRange A B hnorm y‖ = ‖y‖` |
| `apm_m97A02_anchor_preserved` | m97A02 | `{α : ℝ} (hα : Real.cos α = α) {x : ℝ → ℝ} (hx : x α = 0) : Real.sin (x α) + x (Real.cos α) = 0` |
| `apm_m97A02_anchored_pointwise_bound` | m97A02 | `{α r t : ℝ} {x : ℝ → ℝ} (hα : α ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hx : ContDiffOn ℝ 1 x (Icc 0 1)) (hxα : x α = 0) (hder : ∀ s ∈ Icc (0 : ℝ) 1, \|derivWithin x (Icc 0 1) s\| < r) : \|x t\| ≤ r` |
| `apm_m97A02_cos_mem_Icc` | m97A02 | `{t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : Real.cos t ∈ Icc (0 : ℝ) 1` |
| `apm_m97A02_cos_remainder_mul_sub` | m97A02 | `(x y u v : ℝ) : \|(Real.cos x - 1) * u - (Real.cos y - 1) * v\| ≤ \|x\| * \|u - v\| + \|x - y\| * \|v\|` |
| `apm_m97A02_derivWithin_remainder_sub_le` | m97A02 | `{x y : ℝ → ℝ} (hx : ContDiffOn ℝ 1 x (Icc 0 1)) (hy : ContDiffOn ℝ 1 y (Icc 0 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : \|derivWithin (fun s ↦ Real.sin (x s) - x s) (Icc 0 1) t - derivWithin (fun s ↦ Real.sin (y s) - y s) (Icc 0 1) t\| ≤ \|x t\| * \|derivWithin x (Icc 0 1) t - derivWithin y (Icc 0 1) t\| + \|x t - y t\| * \|derivWithin y (Icc 0 1) t\|` |
| `apm_m97A02_derivWithin_sin_sub_self` | m97A02 | `{x : ℝ → ℝ} (hx : ContDiffOn ℝ 1 x (Icc 0 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : derivWithin (fun s ↦ Real.sin (x s) - x s) (Icc 0 1) t = (Real.cos (x t) - 1) * derivWithin x (Icc 0 1) t` |
| `apm_m97A02_sin_one_lt_one` | m97A02 | `: Real.sin 1 < 1` |
| `apm_m97A03_integrableOn_rpow_neg_half` | m97A03 | `: IntegrableOn (fun s : ℝ ↦ s ^ (-1 / 2 : ℝ)) (Icc 0 1)` |
| `apm_m97A03_integral_integrand_sub_bound` | m97A03 | `{t B : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u v : ℝ → ℝ) (huv : ∀ s ∈ Icc (0 : ℝ) 1, \|u s - v s\| ≤ B) : \|∫ s in Icc (0 : ℝ) 1, Real.sqrt ((t + 3) / s) * (Real.sin (t * u s) - Real.sin (t * v s))\| ≤ 4 * B` |
| `apm_m97A03_integral_rpow_neg_half` | m97A03 | `: (∫ s in Icc (0 : ℝ) 1, s ^ (-1 / 2 : ℝ)) = 2` |
| `apm_m97A03_integrand_sub_bound` | m97A03 | `{t s u v : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : 0 < s) : \|Real.sqrt ((t + 3) / s) * (Real.sin (t * u) - Real.sin (t * v))\| ≤ 2 * s ^ (-1 / 2 : ℝ) * \|u - v\|` |
| `apm_m97A03_kernel_lipschitz_majorant` | m97A03 | `{t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : 0 < s) : t * Real.sqrt ((t + 3) / s) ≤ 2 * s ^ (-1 / 2 : ℝ)` |
| `apm_m97A03_sqrt_div_factor` | m97A03 | `{t s : ℝ} (ht : 0 ≤ t + 3) (hs : 0 < s) : Real.sqrt ((t + 3) / s) = Real.sqrt (t + 3) * s ^ (-1 / 2 : ℝ)` |
| `apm_m97A03_t_sqrt_bound` | m97A03 | `{t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ t * Real.sqrt (t + 3) ∧ t * Real.sqrt (t + 3) ≤ 2` |
| `apm_m97a04_diagonal_norm_gt_two` | m97A04 | `{n : ℕ} (hn : 0 < n) (a b : ℝ → ℝ) (hbneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, b t < 0) (i : Fin n) : 2 < ‖apm_m97a04_matrix n a b i i‖` |
| `apm_m97a04_matrix_eq_zero_of_not_neighbor` | m97A04 | `{n : ℕ} (a b : ℝ → ℝ) (i j : Fin n) (hji : j ≠ i) (hpred : j.val + 1 ≠ i.val) (hsucc : i.val + 1 ≠ j.val) : apm_m97a04_matrix n a b i j = 0` |
| `apm_m97a04_matrix_pred` | m97A04 | `{n : ℕ} (a b : ℝ → ℝ) (i : Fin n) (hi : 0 < i.val) : apm_m97a04_matrix n a b i ⟨i.val - 1, by omega⟩ = 1 - apm_m97a04_h n / 2 * a ((i.val + 1) * apm_m97a04_h n)` |
| `apm_m97a04_matrix_succ` | m97A04 | `{n : ℕ} (a b : ℝ → ℝ) (i : Fin n) (hi : i.val + 1 < n) : apm_m97a04_matrix n a b i ⟨i.val + 1, hi⟩ = 1 + apm_m97a04_h n / 2 * a ((i.val + 1) * apm_m97a04_h n)` |
| `apm_m97a04_neighbor_norm_sum` | m97A04 | `{h x : ℝ} (hh : 0 ≤ h) (hsmall : h / 2 * \|x\| < 1) : ‖1 - h / 2 * x‖ + ‖1 + h / 2 * x‖ = 2` |
| `apm_m97a04_unique_mulVec_of_det` | m97A04 | `{n : ℕ} {a b : ℝ → ℝ} (hdet : (apm_m97a04_matrix n a b).det ≠ 0) (rhs : Fin n → ℝ) : ∃! u : Fin n → ℝ, Matrix.mulVec (apm_m97a04_matrix n a b) u = rhs` |
| `apm_m98a02_trivial_space_obstruction` | m98A02 | `(A B : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ)) : ¬ 1 / (1 + ‖A‖) ≤ ‖B‖` |
| `apm_m98a03_derivative_kernel_norm_le` | m98A03 | `(K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ) (f : ℝ → ℝ) (u h : apm_m98a03_C01) (M : ℝ) (hM : ∀ z : ℝ, \|deriv f z\| ≤ M) (x y : Icc (0 : ℝ) 1) : \|K (x, y) * deriv f (u y) * h y\| ≤ ‖K‖ * M * ‖h‖` |
| `apm_m98a03_exists_deriv_bound_on_Icc` | m98A03 | `(f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (a b : ℝ) : ∃ M : ℝ, ∀ z ∈ Icc a b, \|deriv f z\| ≤ M` |
| `apm_m98a03_exists_local_deriv_bound` | m98A03 | `(f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (u : apm_m98a03_C01) : ∃ M : ℝ, ∀ v : apm_m98a03_C01, dist v u < 1 → ∀ y : Icc (0 : ℝ) 1, \|deriv f (v y)\| ≤ M` |
| `apm_m98a03_integrable_derivative_kernel_section` | m98A03 | `(K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (u h : apm_m98a03_C01) (x : Icc (0 : ℝ) 1) : Integrable (fun y : Icc (0 : ℝ) 1 ↦ K (x, y) * deriv f (u y) * h y)` |
| `apm_m98a03_integrable_derivative_majorant` | m98A03 | `(K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ) (M : ℝ) : Integrable (fun _ : Icc (0 : ℝ) 1 ↦ ‖K‖ * M)` |
| `apm_m98a03_integrable_kernel_section` | m98A03 | `(K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ) (f : ℝ → ℝ) (hf : Continuous f) (u : apm_m98a03_C01) (x : Icc (0 : ℝ) 1) : Integrable (fun y : Icc (0 : ℝ) 1 => K (x, y) * f (u y))` |
| `apm_m98a04_canonical_isConvolution` | m98A04 | `{n : ℕ} (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤) (φ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤) : apm_m98a04_IsConvolution T φ (fun x => T (apm_m98a04_translateReflect φ x))` |
| `apm_m98a04_isDistributionalPartial_nil` | m98A04 | `{n : ℕ} (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤) : apm_m98a04_IsDistributionalPartial [] T T` |
| `apm_m98a05_contDiff_perturbation` | m98A05 | `{X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F G : X → Y) (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) : ContDiff ℝ 1 (fun q : X × ℝ => F q.1 + q.2 • G q.1)` |
| `apm_m98a05_hasFDerivAt_perturbation_zero` | m98A05 | `{X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F G : X → Y) (x₀ : X) (A : X →L[ℝ] Y) (hA : HasFDerivAt F A x₀) : HasFDerivAt (fun x ↦ F x + (0 : ℝ) • G x) A x₀` |
| `apm_m98a05_hasFDerivAt_swapped_partial` | m98A05 | `{X P Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (H : X × P → Z) (x₀ : X) (p₀ : P) (A : X →L[ℝ] Z) (hA : HasFDerivAt (fun x ↦ H (x, p₀)) A x₀) : HasFDerivAt (fun x ↦ (fun q : P × X ↦ H (q.2, q.1)) (p₀, x)) A x₀` |
| `apm_m98a05_hasStrictFDerivAt_of_contDiff` | m98A05 | `{E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) (A : E →L[ℝ] F) (hf : ContDiff ℝ 1 f) (hA : HasFDerivAt f A x) : HasStrictFDerivAt f A x` |
| `apm_m98a06_deriv_sin_half` | m98A06 | `(x : ℝ) : deriv (fun t : ℝ ↦ Real.sin (t / 2)) x = Real.cos (x / 2) / 2` |
| `apm_m98a06_negativeMode_admissible` | m98A06 | `: apm_m98a06_Admissible (2 * Real.pi) 0 0 (fun x : ℝ ↦ Real.sin (x / 2))` |
| `apm_m98a06_negativeMode_energy` | m98A06 | `: apm_m98a06_I (2 * Real.pi) (fun x : ℝ ↦ Real.sin (x / 2)) = -(3 * Real.pi / 4)` |
| `apm_m98a06_nonresonant_candidate_admissible` | m98A06 | `{a : ℝ} (ha : Real.sin a ≠ 0) : apm_m98a06_Admissible a 0 1 (fun x ↦ Real.sin x / Real.sin a)` |
| `apm_m98a06_positiveMode_admissible` | m98A06 | `: apm_m98a06_Admissible (2 * Real.pi) 0 0 (fun x : ℝ ↦ Real.sin (2 * x))` |
| `apm_m98a06_sin_ne_zero_of_nonresonant` | m98A06 | `{a : ℝ} (ha : ∀ k : ℤ, a ≠ k * Real.pi) : Real.sin a ≠ 0` |
| `apm_m98J02_hasCompactSupport_add` | m98J02 | `(u v : apm_m98J02_Dist) (hu : apm_m98J02_hasCompactSupport u) (hv : apm_m98J02_hasCompactSupport v) : apm_m98J02_hasCompactSupport (u + v)` |
| `apm_m98J02_hasCompactSupport_neg` | m98J02 | `(u : apm_m98J02_Dist) (hu : apm_m98J02_hasCompactSupport u) : apm_m98J02_hasCompactSupport (-u)` |
| `apm_m98J02_hasCompactSupport_smul` | m98J02 | `(c : ℝ) (u : apm_m98J02_Dist) (hu : apm_m98J02_hasCompactSupport u) : apm_m98J02_hasCompactSupport (c • u)` |
| `apm_m98J02_hasCompactSupport_sub` | m98J02 | `(u v : apm_m98J02_Dist) (hu : apm_m98J02_hasCompactSupport u) (hv : apm_m98J02_hasCompactSupport v) : apm_m98J02_hasCompactSupport (u - v)` |
| `apm_m98J02_solvesT_add_homogeneous` | m98J02 | `(w z : apm_m98J02_Dist) (r : apm_m98J02_Test → ℝ) (hw : apm_m98J02_solvesT w r) (hz : apm_m98J02_solvesT z (fun _ ↦ 0)) : apm_m98J02_solvesT (w + z) r` |
| `apm_m98J03_adjoint_starProjection` | m98J03 | `{H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (V : ClosedSubmodule ℝ H) : V.starProjection.adjoint = V.starProjection` |
| `apm_m98J03_commute_preserves` | m98J03 | `{H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (V : ClosedSubmodule ℝ H) : ∀ A : H →L[ℝ] H, A.comp V.starProjection = V.starProjection.comp A → (∀ x ∈ (V : Set H), A x ∈ (V : Set H)) ∧ (∀ x ∈ (apm_m98J03_perp V : Set H), A x ∈ (apm_m98J03_perp V : Set H))` |
| `apm_m98J03_compact_starProjection_iff` | m98J03 | `{H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (V : ClosedSubmodule ℝ H) : IsCompactOperator V.starProjection ↔ FiniteDimensional ℝ (↥(V : Submodule ℝ H))` |
| `apm_m98J03_perp_isClosed` | m98J03 | `{H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (V : ClosedSubmodule ℝ H) : IsClosed (apm_m98J03_perp V : Set H)` |
| `apm_m98J03_spectrum_eq_one_iff` | m98J03 | `{H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H] (V : ClosedSubmodule ℝ H) : spectrum ℝ V.starProjection = ({1} : Set ℝ) ↔ V = ⊤` |
| `apm_m98J03_spectrum_eq_zero_iff` | m98J03 | `{H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H] (V : ClosedSubmodule ℝ H) : spectrum ℝ V.starProjection = ({0} : Set ℝ) ↔ V = ⊥` |
| `apm_m98J04_arcLength_line` | m98J04 | `(a b α β : ℝ) (hab : a < b) : apm_m98J04_arcLength a b (apm_m98J04_line a b α β) = (b - a) * Real.sqrt (1 + ((β - α) / (b - a)) ^ 2)` |
| `apm_m98J04_arcLength_line_eq_sqrt` | m98J04 | `(a b α β : ℝ) (hab : a < b) : apm_m98J04_arcLength a b (apm_m98J04_line a b α β) = Real.sqrt ((b - a) ^ 2 + (β - α) ^ 2)` |
| `apm_m98J04_deriv_line` | m98J04 | `(a b α β x : ℝ) : deriv (apm_m98J04_line a b α β) x = (β - α) / (b - a)` |
| `apm_m98J04_eq_zero_on_Ioo_of_ae` | m98J04 | `(a b : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Ioo a b)) (hae : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Ioo a b → f x = 0) : ∀ x ∈ Ioo a b, f x = 0` |
| `apm_m98J04_integral_complex_tangent` | m98J04 | `(a b : ℝ) (y : ℝ → ℝ) (hy : ContDiff ℝ 1 y) : ∫ x in a..b, (((1 : ℝ) : ℂ) + ((deriv y x : ℝ) : ℂ) * Complex.I) = ((b - a : ℝ) : ℂ) + ((y b - y a : ℝ) : ℂ) * Complex.I` |
| `apm_m98J04_integral_deriv_eq_sub` | m98J04 | `(a b : ℝ) (y : ℝ → ℝ) (hy : ContDiff ℝ 1 y) : ∫ x in a..b, deriv y x = y b - y a` |
| `apm_m98J04_norm_one_add_deriv_mul_I` | m98J04 | `(y : ℝ → ℝ) (x : ℝ) : ‖((1 : ℝ) : ℂ) + ((deriv y x : ℝ) : ℂ) * Complex.I‖ = Real.sqrt (1 + (deriv y x) ^ 2)` |
| `apm_m98J05_fourier_eq_mathlib` | m98J05 | `(f : ℝ → ℂ) (ξ : ℝ) : apm_m98J05_fourier f ξ = 𝓕 f (ξ / (2 * Real.pi))` |
| `apm_m98J05_fourier_integrable` | m98J05 | `(f : ℝ → ℂ) (hf : Integrable f) (ξ : ℝ) : Integrable (fun x => f x * Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ)))` |
| `apm_m98J05_heatKernel_integrable` | m98J05 | `{t : ℝ} (ht : 0 < t) : Integrable (apm_m98J05_heatKernel t) volume` |
| `apm_m98J05_heatKernel_integral` | m98J05 | `{t : ℝ} (ht : 0 < t) : ∫ x : ℝ, apm_m98J05_heatKernel t x ∂volume = 1` |
| `apm_m98J05_heatKernel_nonneg` | m98J05 | `{t : ℝ} (ht : 0 < t) (x : ℝ) : 0 ≤ apm_m98J05_heatKernel t x` |
| `apm_m98J05_heatSolution_integrable` | m98J05 | `{f : ℝ → ℂ} (hf : Integrable f) {t : ℝ} (ht : 0 < t) (x : ℝ) : Integrable (fun y => f y * (apm_m98J05_heatKernel t (x - y) : ℂ))` |
| `apm_m99A01_deriv_sine_family` | m99A01 | `(n t : ℝ) : deriv (fun x : ℝ => n * Real.sin (2 * x)) t = 2 * n * Real.cos (2 * t)` |
| `apm_m99A01_eq_zero_on_Ioo_of_ae` | m99A01 | `(f : ℝ → ℝ) (hf : ContinuousOn f (Ioo 0 (Real.pi / 2))) (hae : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Ioo 0 (Real.pi / 2) → f x = 0) : ∀ x ∈ Ioo 0 (Real.pi / 2), f x = 0` |
| `apm_m99A01_extremal_ode` | m99A01 | `(t : ℝ) : deriv (deriv apm_m99A01_extremal) t - apm_m99A01_extremal t = 1` |
| `apm_m99A01_functional_sine_family` | m99A01 | `(n : ℝ) : apm_m99A01_functional (fun t : ℝ => n * Real.sin (2 * t)) = (5 * Real.pi / 4) * n ^ 2 + 2 * n` |
| `apm_m99A01_integral_cos_sq_two_mul` | m99A01 | `: ∫ t in (0 : ℝ)..(Real.pi / 2), Real.cos (2 * t) ^ 2 = Real.pi / 4` |
| `apm_m99A01_integral_sin_sq_two_mul` | m99A01 | `: ∫ t in (0 : ℝ)..(Real.pi / 2), Real.sin (2 * t) ^ 2 = Real.pi / 4` |
| `apm_m99A01_integral_sin_two_mul` | m99A01 | `: ∫ t in (0 : ℝ)..(Real.pi / 2), Real.sin (2 * t) = 1` |
| `apm_m99A01_no_maximum` | m99A01 | `: ¬ ∃ y ∈ apm_m99A01_admissible, ∀ z ∈ apm_m99A01_admissible, apm_m99A01_functional z ≤ apm_m99A01_functional y` |
| `apm_m99A01_sine_family_admissible` | m99A01 | `(n : ℝ) : (fun t : ℝ ↦ n * Real.sin (2 * t)) ∈ apm_m99A01_admissible` |
| `apm_m99j01_cos_fixed_unique` | m99J01 | `{x y : ℝ} (hx : Real.cos x = x) (hy : Real.cos y = y) : x = y` |
| `apm_m99j01_fixed_isSolution` | m99J01 | `{ξ : ℝ} (hξ : Real.cos ξ = ξ) : apm_m99j01_IsSolution ξ (fun _ => ξ)` |
| `apm_m99j01_solution_unique` | m99J01 | `{u₀ : ℝ} {u v : ℝ → ℝ} (hu : apm_m99j01_IsSolution u₀ u) (hv : apm_m99j01_IsSolution u₀ v) : ∀ t : ℝ, 0 ≤ t → v t = u t` |
| `apm_m99j01_vectorField_lipschitz` | m99J01 | `: LipschitzWith 2 apm_m99j01_vectorField` |
| `apm_m99j01_vectorField_neg_of_fixed_lt` | m99J01 | `{x ξ : ℝ} (hξ : Real.cos ξ = ξ) (hξx : ξ < x) : apm_m99j01_vectorField x < 0` |
| `apm_m99j01_vectorField_pos_of_lt_fixed` | m99J01 | `{x ξ : ℝ} (hξ : Real.cos ξ = ξ) (hxξ : x < ξ) : 0 < apm_m99j01_vectorField x` |
| `apm_m99j02_g_continuous` | m99J02 | `(u₁ u₂ : ℝ → ℝ) (hu₁ : Continuous u₁) (hu₂ : Continuous u₂) (y : ℝ) : Continuous (apm_m99j02_g u₁ u₂ y)` |
| `apm_m99j02_g_derivative_jump` | m99J02 | `(u₁ u₂ : ℝ → ℝ) (y : ℝ) : deriv u₂ y * u₁ y - deriv u₁ y * u₂ y = apm_m99j02_Wronskian u₁ u₂ y` |
| `apm_m99j02_g_hasDerivWithinAt_Iic` | m99J02 | `(u₁ u₂ : ℝ → ℝ) (hu₁ : Differentiable ℝ u₁) (y : ℝ) : HasDerivWithinAt (apm_m99j02_g u₁ u₂ y) (deriv u₁ y * u₂ y) (Set.Iic y) y` |
| `apm_m99j02_g_hasDerivWithinAt_Ioi` | m99J02 | `(u₁ u₂ : ℝ → ℝ) (hu₂ : Differentiable ℝ u₂) (y : ℝ) : HasDerivWithinAt (apm_m99j02_g u₁ u₂ y) (deriv u₂ y * u₁ y) (Set.Ioi y) y` |
| `apm_m99j02_integrable_mul_test` | m99J02 | `(u φ : ℝ → ℝ) (hu : Continuous u) (hφ : apm_m99j02_IsTestFunction φ) : MeasureTheory.Integrable (fun x : ℝ ↦ u x * φ x) MeasureTheory.volume` |
| `apm_m99j02_wronskian_eq_zero` | m99J02 | `(u₁ u₂ q : ℝ → ℝ) (hu₁ : ContDiff ℝ 2 u₁) (hu₂ : ContDiff ℝ 2 u₂) (hq₁ : ∀ x : ℝ, deriv (deriv u₁) x + q x * u₁ x = 0) (hq₂ : ∀ x : ℝ, deriv (deriv u₂) x + q x * u₂ x = 0) : ∀ y : ℝ, apm_m99j02_Wronskian u₁ u₂ y = apm_m99j02_Wronskian u₁ u₂ 0` |
| `apm_m99j03_dilation_integrable` | m99J03 | `(ψ φ : ℝ → ℝ) (hψ : Continuous ψ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) (n : ℕ) : MeasureTheory.Integrable (fun x : ℝ => ψ (x / (n : ℝ)) * φ x)` |
| `apm_m99j03_dilation_tendsto` | m99J03 | `(ψ φ : ℝ → ℝ) (hψ : Continuous ψ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) : Filter.Tendsto (fun n : ℕ => ∫ x : ℝ, ψ (x / (n : ℝ)) * φ x) Filter.atTop (nhds (ψ 0 * ∫ x : ℝ, φ x))` |
| `apm_m99j03_integral_triangle_one` | m99J03 | `: (∫ x : ℝ, apm_m99j03_triangle 1 x) = 1` |
| `apm_m99j03_triangle_eq_scaled_profile` | m99J03 | `{n : ℕ} (hn : 0 < n) (x : ℝ) : apm_m99j03_triangle n x = (n : ℝ) * apm_m99j03_triangle 1 ((n : ℝ) * x)` |
| `apm_m99j03_triangle_one_continuous` | m99J03 | `: Continuous (apm_m99j03_triangle 1)` |
| `apm_m99j03_triangle_one_eq_max` | m99J03 | `(x : ℝ) : apm_m99j03_triangle 1 x = max (1 - \|x\|) 0` |
| `apm_m99j03_triangle_one_hasCompactSupport` | m99J03 | `: HasCompactSupport (apm_m99j03_triangle 1)` |
| `apm_m99j04_adjoint_comp_of_orthonormal_map` | m99J04 | `{𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] (A : H ≃L[𝕜] H) {ι : Type} (w : HilbertBasis ι 𝕜 H) (horth : Orthonormal 𝕜 (fun i ↦ A (w i))) : (ContinuousLinearMap.adjoint A.toContinuousLinearMap).comp A.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 H` |
| `apm_m99j04_generalized_eigenvector` | m99J04 | `{𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] (A : H ≃L[𝕜] H) (T : H →L[𝕜] H) (w : H) (eigenvalue : 𝕜) (hw : apm_m99j04_conjugate A T w = eigenvalue • w) : T (A w) = eigenvalue • apm_m99j04_weight A (A w)` |
| `apm_m99j04_orthonormal_map_of_adjoint_comp` | m99J04 | `{𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] (A : H ≃L[𝕜] H) {ι : Type} (w : HilbertBasis ι 𝕜 H) (hunit : (ContinuousLinearMap.adjoint A.toContinuousLinearMap).comp A.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 H) : Orthonormal 𝕜 (fun i ↦ A (w i))` |
| `apm_m99j04_weight_inner` | m99J04 | `{𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] (A : H ≃L[𝕜] H) (x y : H) : inner 𝕜 (apm_m99j04_weight A (A x)) (A y) = inner 𝕜 x y` |
| `apm_m99J06_exists_unique_inner_eq` | m99J06 | `{E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (L : E →L[ℝ] ℝ) : ∃! u : E, ∀ v : E, inner ℝ u v = L v` |
| `apm_m99J06_galerkin_energy` | m99J06 | `{H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H) (f : ℝ → ℝ) (V : Submodule ℝ H) (u : V) (hu : apm_m99J06_galerkinEquation M f V u) : ‖(u : H)‖ ^ 2 = ∫ x in Icc (0 : ℝ) 1, f x * M.val (u : H) x` |
| `apm_m99J06_galerkin_unique` | m99J06 | `{H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H) (f : ℝ → ℝ) (V : Submodule ℝ H) (u v : V) (hu : apm_m99J06_galerkinEquation M f V u) (hv : apm_m99J06_galerkinEquation M f V v) : u = v` |
| `apm_m99J06_model_ext` | m99J06 | `{H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (M : apm_m99J06_H01Model H) {u v : H} (hu : M.val u = M.val v) (hdu : M.weakDeriv u = M.weakDeriv v) : u = v` |
| `apm_t00A01_continuous_glueLift` | t00A01 | `{A B C : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) (fA : A → C) (fB : B → C) (hcompat : fA ∘ iA = fB ∘ iB) (hfA : Continuous fA) (hfB : Continuous fB) : Continuous (apm_t00A01_glueLift iA iB fA fB hcompat)` |
| `apm_t00A01_continuous_inl` | t00A01 | `{A B : Type} [TopologicalSpace A] [TopologicalSpace B] (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) : Continuous (apm_t00A01_inl iA iB)` |
| `apm_t00A01_continuous_inr` | t00A01 | `{A B : Type} [TopologicalSpace A] [TopologicalSpace B] (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) : Continuous (apm_t00A01_inr iA iB)` |
| `apm_t00A01_glueLift_unique` | t00A01 | `{A B C : Type} (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) (fA : A → C) (fB : B → C) (hcompat : fA ∘ iA = fB ∘ iB) (g : apm_t00A01_connectedSum iA iB → C) (hgA : g ∘ apm_t00A01_inl iA iB = fA) (hgB : g ∘ apm_t00A01_inr iA iB = fB) : g = apm_t00A01_glueLift iA iB fA fB hcompat` |
| `apm_t00A01_inl_comp_iA_eq_inr_comp_iB` | t00A01 | `{A B : Type} (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) : apm_t00A01_inl iA iB ∘ iA = apm_t00A01_inr iA iB ∘ iB` |
| `apm_t00A01_mk_inl_eq_mk_inr` | t00A01 | `{A B : Type} (iA : apm_t00A01_Sphere2 → A) (iB : apm_t00A01_Sphere2 → B) (s : apm_t00A01_Sphere2) : (Quotient.mk _ (Sum.inl (iA s)) : apm_t00A01_connectedSum iA iB) = Quotient.mk _ (Sum.inr (iB s))` |
| `apm_t00A02_antipodal_eqvGen_iff` | t00A02 | `(x y : apm_t00A02_Sphere2) : Relation.EqvGen apm_t00A02_antipodalRel x y ↔ y = x ∨ y = -x` |
| `apm_t00A02_antipodalCover_eq_iff` | t00A02 | `(x y : apm_t00A02_Sphere2) : apm_t00A02_antipodalCover x = apm_t00A02_antipodalCover y ↔ y = x ∨ y = -x` |
| `apm_t00A02_antipodalCover_fiber_card` | t00A02 | `(b : apm_t00A02_RP2) : Nat.card {e : apm_t00A02_Sphere2 // apm_t00A02_antipodalCover e = b} = 2` |
| `apm_t00A02_antipodalCover_surjective` | t00A02 | `: Function.Surjective apm_t00A02_antipodalCover` |
| `apm_t00A02_coverWitness.not_regular` | t00A02 | `{B : Type} [TopologicalSpace B] {n : ℕ} (w : apm_t00A02_coverWitness B n false) : ¬@apm_t00A02_isRegularCover w.E B w.topology _ w.p` |
| `apm_t00A02_coverWitness.regular` | t00A02 | `{B : Type} [TopologicalSpace B] {n : ℕ} (w : apm_t00A02_coverWitness B n true) : @apm_t00A02_isRegularCover w.E B w.topology _ w.p` |
| `apm_t00a03_component_isOpen` | t00A03 | `{F : Type} [TopologicalSpace F] [T2Space F] [ChartedSpace apm_t00a03_E2 F] [IsManifold apm_t00a03_I2 ⊤ F] {n : ℕ} (curves : Fin n → apm_t00a03_Curve F) (hemb : ∀ i, Topology.IsEmbedding (curves i)) (x : F) : IsOpen (connectedComponentIn (apm_t00a03_cut curves) x)` |
| `apm_t00a03_components_eq_of_inter_nonempty` | t00A03 | `{F : Type} [TopologicalSpace F] {n : ℕ} (curves : Fin n → apm_t00a03_Curve F) {x y : F} (hxy : (connectedComponentIn (apm_t00a03_cut curves) x ∩ connectedComponentIn (apm_t00a03_cut curves) y).Nonempty) : connectedComponentIn (apm_t00a03_cut curves) x = connectedComponentIn (apm_t00a03_cut curves) y` |
| `apm_t00a03_components_eq_or_disjoint` | t00A03 | `{F : Type} [TopologicalSpace F] {n : ℕ} (curves : Fin n → apm_t00a03_Curve F) (x y : F) : connectedComponentIn (apm_t00a03_cut curves) x = connectedComponentIn (apm_t00a03_cut curves) y ∨ Disjoint (connectedComponentIn (apm_t00a03_cut curves) x) (connectedComponentIn (apm_t00a03_cut curves) y)` |
| `apm_t00a03_cut_isOpen` | t00A03 | `{F : Type} [TopologicalSpace F] [T2Space F] {n : ℕ} (curves : Fin n → apm_t00a03_Curve F) (hemb : ∀ i, Topology.IsEmbedding (curves i)) : IsOpen (apm_t00a03_cut curves)` |
| `apm_t00a03_iUnion_components_eq_cut` | t00A03 | `{F : Type} [TopologicalSpace F] {n : ℕ} (curves : Fin n → apm_t00a03_Curve F) : (⋃ x : ↥(apm_t00a03_cut curves), connectedComponentIn (apm_t00a03_cut curves) x) = apm_t00a03_cut curves` |
| `apm_t00a03_parallel_of_range_subset_component` | t00A03 | `{F : Type} [TopologicalSpace F] {n : ℕ} (curves : Fin n → apm_t00a03_Curve F) (hmax : ∀ c : apm_t00a03_Curve F, Topology.IsEmbedding c → ¬apm_t00a03_nullHomotopic c → (∀ i, apm_t00a03_disjoint c (curves i)) → ∃ i, apm_t00a03_parallel c (curves i)) (x : F) (c : apm_t00a03_Curve F) (hc : Topology.IsEmbedding c) (hessential : ¬apm_t00a03_nullHomotopic c) (hcomponent : range c ⊆ connectedComponentIn (apm_t00a03_cut curves) x) : ∃ i, apm_t00a03_parallel c (curves i)` |
| `apm_t00a03_parallel_of_range_subset_cut` | t00A03 | `{F : Type} [TopologicalSpace F] {n : ℕ} (curves : Fin n → apm_t00a03_Curve F) (hmax : ∀ c : apm_t00a03_Curve F, Topology.IsEmbedding c → ¬apm_t00a03_nullHomotopic c → (∀ i, apm_t00a03_disjoint c (curves i)) → ∃ i, apm_t00a03_parallel c (curves i)) (c : apm_t00a03_Curve F) (hc : Topology.IsEmbedding c) (hessential : ¬apm_t00a03_nullHomotopic c) (hcut : range c ⊆ apm_t00a03_cut curves) : ∃ i, apm_t00a03_parallel c (curves i)` |
| `apm_t00j01_fold_continuous` | t00J01 | `: Continuous apm_t00j01_fold` |
| `apm_t00j01_fold_exp` | t00J01 | `(θ : ℝ) : apm_t00j01_fold (Circle.exp θ) = Circle.exp (apm_t00j01_foldLift θ)` |
| `apm_t00j01_fold_pi` | t00J01 | `: apm_t00j01_fold (Circle.exp Real.pi) = Circle.exp Real.pi` |
| `apm_t00j01_fold_pi_deriv_ne` | t00J01 | `: 1 + 2 * Real.cos Real.pi ≠ 0` |
| `apm_t00j01_fold_zero` | t00J01 | `: apm_t00j01_fold (Circle.exp 0) = 1` |
| `apm_t00j01_fold_zero_deriv_ne` | t00J01 | `: 1 + 2 * Real.cos 0 ≠ 0` |
| `apm_t00j01_hasDerivAt_foldLift` | t00J01 | `(θ : ℝ) : HasDerivAt apm_t00j01_foldLift (1 + 2 * Real.cos θ) θ` |
| `apm_t00j02_component_compact_and_pathConnected` | t00J02 | `{S : Type} [TopologicalSpace S] {A : Set S} (hdisks : apm_t00j02_componentsBoundDisks A) {x : S} (hx : x ∈ A) : IsCompact (connectedComponentIn A x) ∧ IsPathConnected (connectedComponentIn A x)` |
| `apm_t00j02_degree_eq_zero_of_homologyMap_eq_zero` | t00J02 | `{S : Type} [TopologicalSpace S] (f : C(S, S)) (degree : ℤ) (hdegree : apm_t00j02_hasDegree f degree) (hzero : apm_t00j02_homologyMap 2 f = 0) : degree = 0` |
| `apm_t00j02_isCompact_connectedComponentIn_of_componentsBoundDisks` | t00J02 | `{S : Type} [TopologicalSpace S] {A : Set S} (hdisks : apm_t00j02_componentsBoundDisks A) {x : S} (hx : x ∈ A) : IsCompact (connectedComponentIn A x)` |
| `apm_t00j02_isPathConnected_connectedComponentIn_of_componentsBoundDisks` | t00J02 | `{S : Type} [TopologicalSpace S] {A : Set S} (hdisks : apm_t00j02_componentsBoundDisks A) {x : S} (hx : x ∈ A) : IsPathConnected (connectedComponentIn A x)` |
| `apm_t00j03_angleFormValue_change` | t00J03 | `(x : apm_t00j03_PuncturedPlane) (v : apm_t00j03_Plane) (lam a : ℝ) (hlam : lam ≠ 0) : apm_t00j03_angleFormValue ⟨lam • x.1, smul_ne_zero hlam x.2⟩ (lam • v + a • x.1) = apm_t00j03_angleFormValue x v` |
| `apm_t00j03_angleFormValue_circle` | t00J03 | `(θ : ℝ) : apm_t00j03_angleFormValue (apm_t00j03_circlePoint θ) (apm_t00j03_circleVelocity θ) = 1` |
| `apm_t00j03_integral_angleFormValue_circle` | t00J03 | `: (∫ θ in (0 : ℝ)..Real.pi, apm_t00j03_angleFormValue (apm_t00j03_circlePoint θ) (apm_t00j03_circleVelocity θ)) = Real.pi` |
| `apm_t00j03_integral_angleFormValue_circle_reverse` | t00J03 | `: (∫ θ in Real.pi..(0 : ℝ), apm_t00j03_angleFormValue (apm_t00j03_circlePoint θ) (apm_t00j03_circleVelocity θ)) = -Real.pi` |
| `apm_t00j03_projectivize_surjective` | t00J03 | `: Function.Surjective apm_t00j03_projectivize` |
| `apm_t00j04_differential_isClosed_of_contMDiff` | t00J04 | `{n : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [ChartedSpace (apm_t00j04_E n) X] [IsManifold (apm_t00j04_I n) ∞ X] {f : X → ℝ} (hf : ContMDiff (apm_t00j04_I n) 𝓘(ℝ, ℝ) ∞ f) : t00J04DifferentialIsClosed (n` |
| `apm_t00j04_mfderiv_chart_linear` | t00J04 | `{n : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [ChartedSpace (apm_t00j04_E n) X] [IsManifold (apm_t00j04_I n) ∞ X] (p : X) (omega_p : TangentSpace (apm_t00j04_I n) p →L[ℝ] ℝ) : mfderiv (apm_t00j04_I n) 𝓘(ℝ, ℝ) (fun x ↦ omega_p (extChartAt (apm_t00j04_I n) p x)) p = omega_p` |
| `apm_t00J06_fst_nat_fiber_infinite` | t00J06 | `(S : Type) [TopologicalSpace S] : ∀ s : S, ((Prod.fst : S × ℕ → S) ⁻¹' ({s} : Set S)).Infinite` |
| `apm_t00J06_isCoveringMap_fst_nat` | t00J06 | `(S : Type) [TopologicalSpace S] : IsCoveringMap (Prod.fst : S × ℕ → S)` |
| `apm_t00j07_attach_glue` | t00J07 | `(f : C(Circle, apm_t00j07_RP2)) (z : Circle) : (Quotient.mk _ (.inl (f z)) : apm_t00j07_attachDisk f) = Quotient.mk _ (.inr (apm_t00j07_circleToDisk z))` |
| `apm_t00j07_basepoint_ne_left` | t00J07 | `(f : C(Circle, apm_t00j07_RP2)) (p : apm_t00j07_RP2) : apm_t00j07_basepoint f ≠ (Quotient.mk _ (.inl p) : apm_t00j07_attachDisk f)` |
| `apm_t00j07_center_eqvGen_iff` | t00J07 | `(f : C(Circle, apm_t00j07_RP2)) (s : Sum apm_t00j07_RP2 apm_t00j07_Disk) : Relation.EqvGen (apm_t00j07_attachRel f) (.inr apm_t00j07_diskCenter) s ↔ s = .inr apm_t00j07_diskCenter` |
| `apm_t00j07_circleToDisk_injective` | t00J07 | `: Function.Injective apm_t00j07_circleToDisk` |
| `apm_t00j07_diskCenter_ne_boundary` | t00J07 | `(z : Circle) : apm_t00j07_diskCenter ≠ apm_t00j07_circleToDisk z` |
| `apm_t00j08_rank_one_impossible` | t00J08 | `: ¬∃ G : Subgroup (FreeGroup (Fin 1)), G.FiniteIndex ∧ Nonempty (G ≃* FreeGroup (Fin 7))` |
| `apm_t00j08_rank_seven_realizable` | t00J08 | `: ∃ G : Subgroup (FreeGroup (Fin 7)), G.FiniteIndex ∧ Nonempty (G ≃* FreeGroup (Fin 7))` |
| `apm_t00j08_rank_zero_impossible` | t00J08 | `: ¬∃ G : Subgroup (FreeGroup (Fin 0)), G.FiniteIndex ∧ Nonempty (G ≃* FreeGroup (Fin 7))` |
| `apm_t00j08_two_le_of_realizable` | t00J08 | `{n : ℕ} (h : ∃ G : Subgroup (FreeGroup (Fin n)), G.FiniteIndex ∧ Nonempty (G ≃* FreeGroup (Fin 7))) : 2 ≤ n` |
| `apm_t01A01_factor_through_complement` | t01A01 | `(f : C(apm_t01A01_RP2, apm_t01A01_RP2)) (hnot_surj : ¬Function.Surjective f) : ∃ q : apm_t01A01_RP2, ∃ g : C(apm_t01A01_RP2, {y : apm_t01A01_RP2 // y ≠ q}), ∀ x, (g x : apm_t01A01_RP2) = f x` |
| `apm_t01A01_nullhomotopic_of_factor` | t01A01 | `(f : C(apm_t01A01_RP2, apm_t01A01_RP2)) (q : apm_t01A01_RP2) (g : C(apm_t01A01_RP2, {y : apm_t01A01_RP2 // y ≠ q})) (hfg : ∀ x, (g x : apm_t01A01_RP2) = f x) (p : {y : apm_t01A01_RP2 // y ≠ q}) (hg : ContinuousMap.Homotopic g (ContinuousMap.const _ p)) : ContinuousMap.Homotopic f (ContinuousMap.const apm_t01A01_RP2 (p : apm_t01A01_RP2))` |
| `apm_t01A02_circle_sq_eq_sq_iff` | t01A02 | `(z w : Circle) : z ^ 2 = w ^ 2 ↔ z = w ∨ z = apm_t01A02_antipode w` |
| `apm_t01A02_cover_continuous` | t01A02 | `: Continuous apm_t01A02_cover` |
| `apm_t01A02_cover_eq_iff` | t01A02 | `(x y : apm_t01A02_Torus) : apm_t01A02_cover x = apm_t01A02_cover y ↔ (x.1 = y.1 ∨ x.1 = apm_t01A02_antipode y.1) ∧ (x.2 = y.2 ∨ x.2 = apm_t01A02_antipode y.2)` |
| `apm_t01A02_cover_eq_prod_pow_two` | t01A02 | `(x : apm_t01A02_Torus) : apm_t01A02_cover x = (x.1 ^ 2, x.2 ^ 2)` |
| `apm_t01A02_cover_surjective` | t01A02 | `: Function.Surjective apm_t01A02_cover` |
| `apm_t01A02_isCoveringMap_circle_pow_two` | t01A02 | `: IsCoveringMap (fun z : Circle ↦ z ^ 2)` |
| `apm_t01a03_fundamentalGroupMap_injective_of_retraction` | t01A03 | `{A X : Type} [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) (a : A) (h : apm_t01a03_HasRetraction i) : Function.Injective (FundamentalGroup.map i a)` |
| `apm_t01a03_H1map_injective_of_retraction` | t01A03 | `{A X : Type} [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) (h : apm_t01a03_HasRetraction i) : Function.Injective (apm_t01a03_H1map i)` |
| `apm_t01a03_noRetraction_circle_of_H1_nontrivial` | t01A03 | `[Nontrivial (apm_t01a03_H1 Circle)] {X : Type} [TopologicalSpace X] (i : C(Circle, X)) (hi : apm_t01a03_H1map i = 0) : ¬apm_t01a03_HasRetraction i` |
| `apm_t01a03_noRetraction_of_H1map_zero` | t01A03 | `{A X : Type} [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) (hi : apm_t01a03_H1map i = 0) (hnonzero : ∃ x : apm_t01a03_H1 A, x ≠ 0) : ¬apm_t01a03_HasRetraction i` |
| `apm_t01a03_noRetraction_twoCircles` | t01A03 | `{S : Type} [TopologicalSpace S] [ConnectedSpace S] (i : C(apm_t01a03_TwoCircles, S)) : ¬apm_t01a03_HasRetraction i` |
| `apm_t01a04_circleCoverMap_surjective` | t01A04 | `: Function.Surjective apm_t01a04_circleCoverMap` |
| `apm_t01a04_circleCoverRaw_respects` | t01A04 | `{x y} (h : Relation.EqvGen apm_t01a04_circleCoverRel x y) : Relation.EqvGen apm_t01a04_wedgeRel (apm_t01a04_circleCoverRaw x) (apm_t01a04_circleCoverRaw y)` |
| `apm_t01a04_torusCoverMap_surjective` | t01A04 | `: Function.Surjective apm_t01a04_torusCoverMap` |
| `apm_t01a04_torusCoverRaw_respects` | t01A04 | `{x y} (h : Relation.EqvGen apm_t01a04_torusCoverRel x y) : Relation.EqvGen apm_t01a04_wedgeRel (apm_t01a04_torusCoverRaw x) (apm_t01a04_torusCoverRaw y)` |
| `apm_t01a07_eq_of_smul_rep_eq` | t01A07 | `(p q : apm_t01a07_RP3) (a : ℝ) (h : a • Projectivization.rep q = Projectivization.rep p) : p = q` |
| `apm_t01a07_fderiv_apply_one` | t01A07 | `(v : Fin 4 → ℝ) : fderiv ℝ apm_t01a07_quartic v (Pi.single 1 1) = -(4 * v 1 ^ 3)` |
| `apm_t01a07_fderiv_apply_three` | t01A07 | `(v : Fin 4 → ℝ) : fderiv ℝ apm_t01a07_quartic v (Pi.single 3 1) = 4 * v 3 ^ 3` |
| `apm_t01a07_fderiv_apply_two` | t01A07 | `(v : Fin 4 → ℝ) : fderiv ℝ apm_t01a07_quartic v (Pi.single 2 1) = -(4 * v 2 ^ 3)` |
| `apm_t01a07_fderiv_apply_zero` | t01A07 | `(v : Fin 4 → ℝ) : fderiv ℝ apm_t01a07_quartic v (Pi.single 0 1) = 4 * v 0 ^ 3` |
| `apm_t01a07_fourth_pow_eq_iff` | t01A07 | `(x y : ℝ) : x ^ 4 = y ^ 4 ↔ x = y ∨ x = -y` |
| `apm_t01a07_smooth` | t01A07 | `: apm_t01a07_IsSmoothProjectiveHypersurface` |
| `apm_t01j01_boundary_union_isClosed` | t01J01 | `{S : Type*} [TopologicalSpace S] [T2Space S] (γ₁ γ₂ : C(Circle, S)) : IsClosed (Set.range γ₁ ∪ Set.range γ₂)` |
| `apm_t01j01_isClosed_of_isAnnulusBetween` | t01J01 | `{S : Type*} [TopologicalSpace S] [T2Space S] {A : Set S} {γ₁ γ₂ : C(Circle, S)} (hA : apm_t01j01_IsAnnulusBetween A γ₁ γ₂) : IsClosed A` |
| `apm_t01j01_isCompact_of_isAnnulusBetween` | t01J01 | `{S : Type*} [TopologicalSpace S] {A : Set S} {γ₁ γ₂ : C(Circle, S)} (hA : apm_t01j01_IsAnnulusBetween A γ₁ γ₂) : IsCompact A` |
| `apm_t01j01_ne_univ_of_isAnnulusBetween` | t01J01 | `{S : Type*} [TopologicalSpace S] {A : Set S} {γ₁ γ₂ : C(Circle, S)} (hA : apm_t01j01_IsAnnulusBetween A γ₁ γ₂) : A ≠ Set.univ` |
| `apm_t01j01_range_isClosed` | t01J01 | `{S : Type*} [TopologicalSpace S] [T2Space S] (γ : C(Circle, S)) : IsClosed (Set.range γ)` |
| `apm_t01j01_ranges_subset_of_isAnnulusBetween` | t01J01 | `{S : Type*} [TopologicalSpace S] [T2Space S] {A : Set S} {γ₁ γ₂ : C(Circle, S)} (hA : apm_t01j01_IsAnnulusBetween A γ₁ γ₂) : Set.range γ₁ ⊆ A ∧ Set.range γ₂ ⊆ A` |
| `apm_t01j02_homotopyMap_injective_of_boundary_nonempty` | t01J02 | `{N X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [PreconnectedSpace (N → Set.Icc (0 : ℝ) 1)] (p : E → X) (hp : IsCoveringMap p) (e : E) (y : I^N) (hy : y ∈ Cube.boundary N) : Function.Injective (apm_t01j02_homotopyMap (N` |
| `apm_t01j02_inducedMap_injective` | t01J02 | `(n : ℕ) (hn : 2 ≤ n) {X Xtilde : Type*} [TopologicalSpace X] [TopologicalSpace Xtilde] (xtilde₀ : Xtilde) (x₀ : X) (p : Xtilde → X) (hp : IsCoveringMap p) (hbase : p xtilde₀ = x₀) : Function.Injective (apm_t01j02_inducedMap n ⟨p, hp.continuous⟩ xtilde₀ x₀ hbase)` |
| `apm_t01J03_continuous_boundaryInclusion` | t01J03 | `: Continuous apm_t01J03_boundaryInclusion` |
| `apm_t01J03_continuous_gluedInl` | t01J03 | `(h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus) : Continuous (apm_t01J03_gluedInl h)` |
| `apm_t01J03_continuous_gluedInr` | t01J03 | `(h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus) : Continuous (apm_t01J03_gluedInr h)` |
| `apm_t01J03_gluedDesc_respects` | t01J03 | `{Y : Type*} [TopologicalSpace Y] (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus) (f g : C(apm_t01J03_SolidTorus, Y)) (hfg : ∀ z, f (apm_t01J03_boundaryInclusion z) = g (apm_t01J03_boundaryInclusion (h z))) {x y} (hxy : Relation.EqvGen (apm_t01J03_glueRel h) x y) : Sum.elim f g x = Sum.elim f g y` |
| `apm_t01J03_gluedDesc_unique` | t01J03 | `{Y : Type*} [TopologicalSpace Y] (h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus) (f g : C(apm_t01J03_SolidTorus, Y)) (hfg : ∀ z, f (apm_t01J03_boundaryInclusion z) = g (apm_t01J03_boundaryInclusion (h z))) (u : C(apm_t01J03_gluedSpace h, Y)) (hul : ∀ x, u (apm_t01J03_gluedInl h x) = f x) (hur : ∀ x, u (apm_t01J03_gluedInr h x) = g x) : u = apm_t01J03_gluedDesc h f g hfg` |
| `apm_t01J03_gluedInl_boundary_eq_gluedInr` | t01J03 | `(h : apm_t01J03_BoundaryTorus ≃ₜ apm_t01J03_BoundaryTorus) (z : apm_t01J03_BoundaryTorus) : apm_t01J03_gluedInl h (apm_t01J03_boundaryInclusion z) = apm_t01J03_gluedInr h (apm_t01J03_boundaryInclusion (h z))` |
| `apm_t01J05_eulerCharacteristic_zero` | t01J05 | `(X : Type) [TopologicalSpace X] : apm_t01J05_eulerCharacteristic 0 X = (Module.finrank ℚ (apm_t01J05_H 0 X) : ℤ)` |
| `apm_t01J05_finrank_H0_eq_zero_of_isEmpty` | t01J05 | `(X : Type) [TopologicalSpace X] [IsEmpty X] : Module.finrank ℚ (apm_t01J05_H 0 X) = 0` |
| `apm_t01J05_isEmpty_of_nowhereZero_zeroDim` | t01J05 | `(X : Type) [TopologicalSpace X] [ChartedSpace (apm_t01J05_Euclidean 0) X] [IsManifold (apm_t01J05_Model 0) (⊤ : ℕ∞) X] (omega : apm_t01J05_OneForm (n` |
| `apm_t01J05_zeroDim` | t01J05 | `(X : Type) [TopologicalSpace X] [ChartedSpace (apm_t01J05_Euclidean 0) X] [IsManifold (apm_t01J05_Model 0) (⊤ : ℕ∞) X] (omega : apm_t01J05_OneForm (n` |
| `apm_t01J05_zeroDim_of_empty_H0` | t01J05 | `(X : Type) [TopologicalSpace X] [ChartedSpace (apm_t01J05_Euclidean 0) X] [IsManifold (apm_t01J05_Model 0) (⊤ : ℕ∞) X] (omega : apm_t01J05_OneForm (n` |
| `apm_t01J06_exists_projectionPullback` | t01J06 | `(alpha : apm_t01J06_SphereForm2) (p : apm_t01J06_S1) : ∃ zeta : apm_t01J06_ProductForm2, zeta = apm_t01J06_projectionPullback alpha ∧ apm_t01J06_isJPullback p zeta alpha` |
| `apm_t01J06_inclusionPullback_apply` | t01J06 | `(omega : apm_t01J06_AmbientForm2) (homega : apm_t01J06_isOmega omega) (alpha : apm_t01J06_SphereForm2) (halpha : apm_t01J06_isInclusionPullback omega alpha) (q : apm_t01J06_S2) (v : Fin 2 → apm_t01J06_sphereTangent q) : alpha q v = ((q : apm_t01J06_E3) 2 + 3) * ((v 0 : apm_t01J06_E3) 0 * (v 1 : apm_t01J06_E3) 1 - (v 0 : apm_t01J06_E3) 1 * (v 1 : apm_t01J06_E3) 0)` |
| `apm_t01J06_inclusionPullback_unique` | t01J06 | `(omega : apm_t01J06_AmbientForm2) (alpha beta : apm_t01J06_SphereForm2) (halpha : apm_t01J06_isInclusionPullback omega alpha) (hbeta : apm_t01J06_isInclusionPullback omega beta) : alpha = beta` |
| `apm_t01J06_isOmega_unique` | t01J06 | `(omega eta : apm_t01J06_AmbientForm2) (homega : apm_t01J06_isOmega omega) (heta : apm_t01J06_isOmega eta) : omega = eta` |
| `apm_t01J06_projectionPullback_isJPullback` | t01J06 | `(alpha : apm_t01J06_SphereForm2) (p : apm_t01J06_S1) : apm_t01J06_isJPullback p (apm_t01J06_projectionPullback alpha) alpha` |
| `apm_t01J06_target_period_pos` | t01J06 | `: 0 < 4 * Real.pi / 3` |
| `apm_t02a03_continuous_circleInclusion` | t02A03 | `: Continuous apm_t02a03_circleInclusion` |
| `apm_t02a03_continuous_torusInclusion` | t02A03 | `: Continuous apm_t02a03_torusInclusion` |
| `apm_t02a03_continuous_wedgeQuotient` | t02A03 | `: Continuous apm_t02a03_wedgeQuotient` |
| `apm_t02a03_inclusions_basepoint_eq` | t02A03 | `: apm_t02a03_torusInclusion (1, 1) = apm_t02a03_circleInclusion 1` |
| `apm_t02a03_surjective_wedgeQuotient` | t02A03 | `: Function.Surjective apm_t02a03_wedgeQuotient` |
| `apm_t02a03_wedgeDesc_respects` | t02A03 | `{Z : Type*} [TopologicalSpace Z] (f : C(apm_t02a03_Torus, Z)) (g : C(Circle, Z)) (hbase : f (1, 1) = g 1) {x y} (hxy : Relation.EqvGen apm_t02a03_WedgeGlue x y) : Sum.elim f g x = Sum.elim f g y` |
| `apm_t02a03_wedgeDesc_unique` | t02A03 | `{Z : Type*} [TopologicalSpace Z] (f : C(apm_t02a03_Torus, Z)) (g : C(Circle, Z)) (hbase : f (1, 1) = g 1) (u : C(apm_t02a03_Y, Z)) (huT : ∀ x, u (apm_t02a03_torusInclusion x) = f x) (huC : ∀ z, u (apm_t02a03_circleInclusion z) = g z) : u = apm_t02a03_wedgeDesc f g hbase` |
| `apm_t02a04_continuous_diskInclusion` | t02A04 | `: Continuous apm_t02a04_diskInclusion` |
| `apm_t02a04_continuous_solidInclusion` | t02A04 | `: Continuous apm_t02a04_solidInclusion` |
| `apm_t02a04_diskInclusion_boundary_eq_solidInclusion_attachingCurve` | t02A04 | `: (fun z : Circle => apm_t02a04_diskInclusion (⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk)) = (fun z : Circle => apm_t02a04_solidInclusion ((⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk), z ^ 2))` |
| `apm_t02a04_gluedDesc_respects` | t02A04 | `{Y : Type*} [TopologicalSpace Y] (f : C(apm_t02a04_SolidTorus, Y)) (g : C(apm_t02a04_Disk, Y)) (hfg : ∀ z : Circle, g (⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk) = f ((⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk), z ^ 2)) {x y} (hxy : Relation.EqvGen apm_t02a04_Glue x y) : Sum.elim f g x = Sum.elim f g y` |
| `apm_t02a04_gluedDesc_unique` | t02A04 | `{Y : Type*} [TopologicalSpace Y] (f : C(apm_t02a04_SolidTorus, Y)) (g : C(apm_t02a04_Disk, Y)) (hfg : ∀ z : Circle, g (⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk) = f ((⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk), z ^ 2)) (u : C(apm_t02a04_X, Y)) (hus : ∀ x, u (apm_t02a04_solidInclusion x) = f x) (hud : ∀ x, u (apm_t02a04_diskInclusion x) = g x) : u = apm_t02a04_gluedDesc f g hfg` |
| `apm_t02a04_mk_disk_boundary_eq_mk_attachingCurve` | t02A04 | `(z : Circle) : (Quotient.mk _ (Sum.inr (⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk)) : apm_t02a04_X) = Quotient.mk _ (Sum.inl ((⟨(z : ℂ), by simpa using z.property.le⟩ : apm_t02a04_Disk), z ^ 2))` |
| `apm_t02a05_inner_normal_tangentProjection` | t02A05 | `(c : apm_t02a05_E3) (q : Metric.sphere c 1) (i : Fin 3) : @inner ℝ apm_t02a05_E3 _ ((q : apm_t02a05_E3) - c) (apm_t02a05_tangentProjection c q i) = 0` |
| `apm_t02a05_quadratic_minimum` | t02A05 | `(a b : ℝ) : 44 * Real.pi / 15 ≤ 44 * Real.pi / 15 + 4 * Real.pi * ((a - 1) ^ 2 + (b - 2) ^ 2) ∧ (44 * Real.pi / 15 + 4 * Real.pi * ((a - 1) ^ 2 + (b - 2) ^ 2) = 44 * Real.pi / 15 ↔ a = 1 ∧ b = 2)` |
| `apm_t02a05_sphere_normal_norm` | t02A05 | `(c : apm_t02a05_E3) (q : Metric.sphere c 1) : ‖(q : apm_t02a05_E3) - c‖ = 1` |
| `apm_t02a05_volume_unit_ball` | t02A05 | `: (volume (Metric.ball (0 : apm_t02a05_E3) 1)).toReal = (4 / 3 : ℝ) * Real.pi` |
| `apm_t02a06_intersectionAntipodal_ne` | t02A06 | `{normal₁ normal₂ : apm_t02a06_S2} (x : apm_t02a06_intersection normal₁ normal₂) : apm_t02a06_intersectionAntipodal x ≠ x` |
| `apm_t02a06_localSign_antipodal` | t02A06 | `{normal₁ normal₂ : apm_t02a06_S2} (x : apm_t02a06_intersection normal₁ normal₂) (hne : dotProduct (crossProduct (normal₁ : Fin 3 → ℝ) (normal₂ : Fin 3 → ℝ)) (x.1 : Fin 3 → ℝ) ≠ 0) : apm_t02a06_localSign (apm_t02a06_intersectionAntipodal x) = -apm_t02a06_localSign x` |
| `apm_t02a06_localSign_eq_one_or_neg_one` | t02A06 | `{normal₁ normal₂ : apm_t02a06_S2} (x : apm_t02a06_intersection normal₁ normal₂) : apm_t02a06_localSign x = 1 ∨ apm_t02a06_localSign x = -1` |
| `apm_t02a06_signedIntersection_eq_zero_of_opposite` | t02A06 | `{normal₁ normal₂ : apm_t02a06_S2} (e : Fin 2 ≃ apm_t02a06_intersection normal₁ normal₂) (h : apm_t02a06_localSign (e 0) = -apm_t02a06_localSign (e 1)) : apm_t02a06_signedIntersection e = 0` |
| `apm_t02a07_family_mem_X` | t02A07 | `(parameter : apm_t02a07_parameterCircle) (y : apm_t02a07_S2) : apm_t02a07_family parameter y ∈ apm_t02a07_X` |
| `apm_t02a07_product_coordinates_ne_zero` | t02A07 | `{x : apm_t02a07_E4} (hx : x ∈ apm_t02a07_Z) : x 2 ≠ 0 ∧ x 3 ≠ 0` |
| `apm_t02a07_product_gradient_ne_zero` | t02A07 | `{x : apm_t02a07_E4} (hx : x ∈ apm_t02a07_Z) : (WithLp.toLp 2 ![(0 : ℝ), 0, x 3, x 2] : apm_t02a07_E4) ≠ 0` |
| `apm_t02a08_comp_hasDegree` | t02A08 | `(orientation : apm_t02a08_H2 ≅ ModuleCat.of ℤ ℤ) (g h : C(apm_t02a08_S2, apm_t02a08_S2)) (m n : ℤ) (hg : ∀ a : apm_t02a08_H2, orientation.hom (apm_t02a08_H2Map g a) = m * orientation.hom a) (hh : ∀ a : apm_t02a08_H2, orientation.hom (apm_t02a08_H2Map h a) = n * orientation.hom a) : apm_t02a08_HasDegree (g.comp h) (m * n)` |
| `apm_t02a08_fiberMap_hasOrientedIntersection` | t02A08 | `(p : Circle) (q : apm_t02a08_S2) (g : C(apm_t02a08_S2, apm_t02a08_S2)) (n : ℤ) (hg : apm_t02a08_HasDegree g n) : apm_t02a08_HasOrientedIntersection (apm_t02a08_fiberMap p g) (apm_t02a08_Z q) n` |
| `apm_t02a08_id_hasDegree` | t02A08 | `(orientation : apm_t02a08_H2 ≅ ModuleCat.of ℤ ℤ) : apm_t02a08_HasDegree (⟨id, continuous_id⟩ : C(apm_t02a08_S2, apm_t02a08_S2)) 1` |
| `apm_t02a08_secondProjection_comp_fiberMap` | t02A08 | `(p : Circle) (g : C(apm_t02a08_S2, apm_t02a08_S2)) : apm_t02a08_secondProjection.comp (apm_t02a08_fiberMap p g) = g` |
| `apm_t03j01_H1_iso_of_curve` | t03J01 | `{X : Type} [TopologicalSpace X] {J : Set X} (hcurve : apm_t03j01_IsCurve J) : Nonempty (apm_t03j01_H1 Circle ≅ apm_t03j01_H1 J)` |
| `apm_t03j01_H1_nonzero_of_curve` | t03J01 | `{X : Type} [TopologicalSpace X] {J : Set X} (hcurve : apm_t03j01_IsCurve J) (hcircle : ∃ a : apm_t03j01_H1 Circle, a ≠ 0) : ∃ a : apm_t03j01_H1 J, a ≠ 0` |
| `apm_t03j01_H1Map_injective_of_retraction` | t03J01 | `{X : Type} [TopologicalSpace X] {J : Set X} (h : apm_t03j01_RetractsOnto J) : Function.Injective (apm_t03j01_H1Map (apm_t03j01_inclusion J))` |
| `apm_t03j01_no_retraction_of_curve_H1Map_zero` | t03J01 | `{X : Type} [TopologicalSpace X] {J : Set X} (hcurve : apm_t03j01_IsCurve J) (hzero : apm_t03j01_H1Map (apm_t03j01_inclusion J) = 0) (hcircle : ∃ a : apm_t03j01_H1 Circle, a ≠ 0) : ¬apm_t03j01_RetractsOnto J` |
| `apm_t03j01_no_retraction_of_H1Map_zero` | t03J01 | `{X : Type} [TopologicalSpace X] {J : Set X} (hzero : apm_t03j01_H1Map (apm_t03j01_inclusion J) = 0) (hnonzero : ∃ a : apm_t03j01_H1 J, a ≠ 0) : ¬apm_t03j01_RetractsOnto J` |
| `apm_t03j01_retraction_comp_inclusion_eq_id` | t03J01 | `{X : Type} [TopologicalSpace X] {J : Set X} (h : apm_t03j01_RetractsOnto J) : (h.choose.comp (apm_t03j01_inclusion J)) = ContinuousMap.id J` |
| `apm_t03J02_continuous_quotientMap` | t03J02 | `(j₁ j₂ : C(Circle, apm_t03J02_Torus)) : Continuous (apm_t03J02_quotientMap j₁ j₂)` |
| `apm_t03J02_glue_eq` | t03J02 | `(j₁ j₂ : C(Circle, apm_t03J02_Torus)) (z : Circle) : apm_t03J02_quotientMap j₁ j₂ (Sum.inl (j₁ z)) = apm_t03J02_quotientMap j₁ j₂ (Sum.inr (j₂ z))` |
| `apm_t03J02_gluedDesc_respects` | t03J02 | `{Y : Type*} [TopologicalSpace Y] (j₁ j₂ : C(Circle, apm_t03J02_Torus)) (f g : C(apm_t03J02_Torus, Y)) (hfg : ∀ z, f (j₁ z) = g (j₂ z)) {x y} (hxy : Relation.EqvGen (apm_t03J02_glueRel j₁ j₂) x y) : Sum.elim f g x = Sum.elim f g y` |
| `apm_t03J02_gluedDesc_unique` | t03J02 | `{Y : Type*} [TopologicalSpace Y] (j₁ j₂ : C(Circle, apm_t03J02_Torus)) (f g : C(apm_t03J02_Torus, Y)) (hfg : ∀ z, f (j₁ z) = g (j₂ z)) (u : C(apm_t03J02_space j₁ j₂, Y)) (hul : ∀ x, u (apm_t03J02_quotientMap j₁ j₂ (.inl x)) = f x) (hur : ∀ x, u (apm_t03J02_quotientMap j₁ j₂ (.inr x)) = g x) : u = apm_t03J02_gluedDesc j₁ j₂ f g hfg` |
| `apm_t03J02_surjective_quotientMap` | t03J02 | `(j₁ j₂ : C(Circle, apm_t03J02_Torus)) : Function.Surjective (apm_t03J02_quotientMap j₁ j₂)` |
| `apm_t03J03_character_card` | t03J03 | `: Nat.card apm_t03J03_character = 7` |
| `apm_t03J03_euler_N3` | t03J03 | `: eulerCharacteristic false 3 = -1` |
| `apm_t03J03_euler_N4` | t03J03 | `: eulerCharacteristic false 4 = -2` |
| `apm_t03J03_euler_Sigma2` | t03J03 | `: eulerCharacteristic true 2 = -2` |
| `apm_t03J03_exists_cylinderLift_of_range_le` | t03J03 | `[PathConnectedSpace apm_t03J03_Cylinder] [LocPathConnectedSpace apm_t03J03_Cylinder] (Y : Type) (tY : TopologicalSpace Y) (p : Y → apm_t03J03_N3) (hp : apm_t03J03_isTwoFoldCover tY inferInstance p) (f : apm_t03J03_Cylinder → apm_t03J03_N3) (hf : @Topology.IsEmbedding apm_t03J03_Cylinder apm_t03J03_N3 inferInstance inferInstance f) (z₀ : apm_t03J03_Cylinder) (y₀ : Y) (hy₀ : p y₀ = f z₀) (hle : (FundamentalGroup.map ⟨f, hf.continuous⟩ z₀).range ≤ (FundamentalGroup.mapOfEq ⟨p, hp.1.continuous⟩ hy₀).range) : ∃ lift : apm_t03J03_Cylinder → Y, @Continuous apm_t03J03_Cylinder Y inferInstance tY lift ∧ ∀ z, p (lift z) = f z` |
| `apm_t03J03_orientationCharacter_ne_zero` | t03J03 | `: apm_t03J03_orientationCharacter ≠ 0` |
| `apm_t03J04_constantVectorField_ne_zero` | t03J04 | `(n : ℕ) [NeZero n] (q : apm_t03J04_Torus n) : apm_t03J04_constantVectorField n q ≠ 0` |
| `apm_t03J04_localDiffeomorph_surjective` | t03J04 | `(n : ℕ) [ChartedSpace (apm_t03J04_HModel n) (apm_t03J04_Torus n)] [IsManifold (apm_t03J04_Model n) (⊤ : ℕ∞) (apm_t03J04_Torus n)] (X : Type) [TopologicalSpace X] [T2Space X] [ChartedSpace (apm_t03J04_E n) X] [IsManifold (modelWithCornersSelf ℝ (apm_t03J04_E n)) (⊤ : ℕ∞) X] [ConnectedSpace X] (phi : apm_t03J04_Torus n → X) (hphi : IsLocalDiffeomorph (apm_t03J04_Model n) (modelWithCornersSelf ℝ (apm_t03J04_E n)) (⊤ : ℕ∞) phi) : Function.Surjective phi` |
| `apm_t03J05_card_imageIntersection_product_self` | t03J05 | `{F : Type} [TopologicalSpace F] (a b : C(Circle, F)) : Nat.card {p // p ∈ apm_t03J05_imageIntersection (apm_t03J05_productTorusMap a a) (apm_t03J05_productTorusMap b b)} = Nat.card {x // x ∈ Set.range a ∩ Set.range b} ^ 2` |
| `apm_t03J05_eulerCharacteristic_genusTwo` | t03J05 | `: eulerCharacteristic true 2 = -2` |
| `apm_t03J05_imageIntersection_product_self` | t03J05 | `{F : Type} [TopologicalSpace F] (a b : C(Circle, F)) : apm_t03J05_imageIntersection (apm_t03J05_productTorusMap a a) (apm_t03J05_productTorusMap b b) = (Set.range a ∩ Set.range b) ×ˢ (Set.range a ∩ Set.range b)` |
| `apm_t03J05_odd_imageIntersection_product_self` | t03J05 | `{F : Type} [TopologicalSpace F] (a b : C(Circle, F)) (hodd : Nat.card {x // x ∈ Set.range a ∩ Set.range b} % 2 = 1) : Nat.card {p // p ∈ apm_t03J05_imageIntersection (apm_t03J05_productTorusMap a a) (apm_t03J05_productTorusMap b b)} % 2 = 1` |
| `apm_t03J05_productTorusMap_isEmbedding` | t03J05 | `{F : Type} [TopologicalSpace F] (a b : C(Circle, F)) (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b) : Topology.IsEmbedding (apm_t03J05_productTorusMap a b)` |
| `apm_t03J05_unpunctureCurve_isEmbedding` | t03J05 | `{F : Type} [TopologicalSpace F] (x : F) (a : C(Circle, apm_t03J05_punctured F x)) (ha : Topology.IsEmbedding a) : Topology.IsEmbedding (apm_t03J05_unpunctureCurve x a)` |
| `apm_t03J06_cylinder_integrand` | t03J06 | `(omega : apm_t03J06_Form2) (homega : apm_t03J06_isOmega omega) (theta z : ℝ) : omega (apm_t03J06_cylinderPoint theta z) (apm_t03J06_cylinderTangents theta) = -(z ^ 2 * Real.exp (Real.cos theta * z) * Real.log (Real.cos theta ^ 2 + 1) - Real.sin theta) * Real.sin theta + (Real.cos theta + Real.sin theta ^ 2 * z ^ 3 * Real.cos (Real.sin theta ^ 2 + z ^ 2)) * Real.cos theta` |
| `apm_t03J06_extDeriv_ne_zero_of_eval_three` | t03J06 | `(omega : apm_t03J06_Form2) (hd : ∀ x : apm_t03J06_E3, extDeriv omega x (fun i ↦ EuclideanSpace.single i (1 : ℝ)) = 3) : extDeriv omega ≠ 0` |
| `apm_t03J06_hemisphere_integrand` | t03J06 | `(omega : apm_t03J06_Form2) (homega : apm_t03J06_isOmega omega) (p : ℝ × ℝ) : let s` |
| `apm_t03J06_isOmega_unique` | t03J06 | `(omega eta : apm_t03J06_Form2) (homega : apm_t03J06_isOmega omega) (heta : apm_t03J06_isOmega eta) : omega = eta` |
| `apm_t03J06_not_exact_of_extDeriv_eval_three` | t03J06 | `(omega : apm_t03J06_Form2) (hd : ∀ x : apm_t03J06_E3, extDeriv omega x (fun i ↦ EuclideanSpace.single i (1 : ℝ)) = 3) : ¬(∃ eta : apm_t03J06_Form1, ContDiff ℝ (⊤ : ℕ∞) eta ∧ extDeriv eta = omega)` |
| `apm_t91a05_continuous_boundaryInclusion` | t91A05 | `: Continuous apm_t91a05_boundaryInclusion` |
| `apm_t91a05_fundamentalGroupMap_injective_of_retraction` | t91A05 | `{A X : Type} [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) (a : A) (r : C(X, A)) (hr : ∀ x, r (i x) = x) : Function.Injective (FundamentalGroup.map i a)` |
| `apm_t91a05_no_retraction_of_circle_fundamentalGroup_nontrivial` | t91A05 | `[Nontrivial (FundamentalGroup apm_t91a05_Circle apm_t91a05_circleBase)] : ¬∃ g : apm_t91a05_Disk → apm_t91a05_Circle, Continuous g ∧ ∀ z : apm_t91a05_Circle, g (apm_t91a05_boundaryInclusion z) = z` |
| `apm_t91a05_no_retraction_of_subsingleton_fundamentalGroup` | t91A05 | `{A X : Type} [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) (a : A) [Subsingleton (FundamentalGroup X (i a))] [Nontrivial (FundamentalGroup A a)] : ¬∃ r : C(X, A), ∀ x, r (i x) = x` |
| `apm_t91J01_cantorSet_measure_zero` | t91J01 | `: volume cantorSet = 0` |
| `apm_t91J02_circleRetract_of_homeomorph` | t91J02 | `(e : apm_t91J02_Torus ≃ₜ apm_t91J02_S2) : ∃ i : C(Circle, apm_t91J02_S2), ∃ r : C(apm_t91J02_S2, Circle), r.comp i = ContinuousMap.id Circle` |
| `apm_t91J02_fundamentalGroupMap_injective_of_retract` | t91J02 | `{A X : Type*} [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) (a : A) (r : C(X, A)) (hr : r.comp i = ContinuousMap.id A) : Function.Injective (FundamentalGroup.map i a)` |
| `apm_t91J02_no_circle_retract_of_fundamentalGroup` | t91J02 | `[Nontrivial (FundamentalGroup Circle (1 : Circle))] (hsphere : ∀ x : apm_t91J02_S2, Subsingleton (FundamentalGroup apm_t91J02_S2 x)) : ¬ ∃ i : C(Circle, apm_t91J02_S2), ∃ r : C(apm_t91J02_S2, Circle), r.comp i = ContinuousMap.id Circle` |
| `apm_t91J02_not_homeomorph_of_no_circle_retract` | t91J02 | `(h : ¬ ∃ i : C(Circle, apm_t91J02_S2), ∃ r : C(apm_t91J02_S2, Circle), r.comp i = ContinuousMap.id Circle) : ¬Nonempty (apm_t91J02_Torus ≃ₜ apm_t91J02_S2)` |
| `apm_t91J03_height_ne_of_circleMap_eq` | t91J03 | `(gamma : C(Circle, apm_t91J03_Annulus)) (hgamma : Topology.IsEmbedding (gamma : Circle → apm_t91J03_Annulus)) {z w : Circle} (hzw : z ≠ w) (hprojection : apm_t91J03_circleMap gamma z = apm_t91J03_circleMap gamma w) : apm_t91J03_height gamma z ≠ apm_t91J03_height gamma w` |
| `apm_t91J03_no_two_of_forced_fiber_collision` | t91J03 | `(gamma : C(Circle, apm_t91J03_Annulus)) (hgamma : Topology.IsEmbedding (gamma : Circle → apm_t91J03_Annulus)) (hcollision : ∀ n : ℤ, apm_t91J03_HasWindingNumber gamma n → n.natAbs = 2 → ∃ z w : Circle, z ≠ w ∧ apm_t91J03_circleMap gamma z = apm_t91J03_circleMap gamma w ∧ apm_t91J03_height gamma z = apm_t91J03_height gamma w) : ∀ n : ℤ, apm_t91J03_HasWindingNumber gamma n → n.natAbs ≠ 2` |
| `apm_t91J05_eulerCharacteristic_odd_genus` | t91J05 | `(n : ℕ) : eulerCharacteristic true (2 * n + 1) = (n : ℤ) * eulerCharacteristic true 3` |
| `apm_t91J05_isFiniteCover_of_homeomorph` | t91J05 | `{X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (hY : apm_t91J05_IsFiniteCover Y) : apm_t91J05_IsFiniteCover X` |
| `apm_t91J06_exists_mem_stage` | t91J06 | `{X : Type*} (f : ℕ → apm_t91J06_I → X) (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X)) (x : X) : ∃ n, x ∈ apm_t91J06_stage f n` |
| `apm_t91J06_exists_mem_stage_interior` | t91J06 | `{X : Type*} (f : ℕ → apm_t91J06_I → X) (hnested : ∀ n, f n '' (univ : Set apm_t91J06_I) ⊆ f (n + 1) '' apm_t91J06_Iinterior) (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X)) (x : X) : ∃ n, x ∈ f n '' apm_t91J06_Iinterior` |
| `apm_t91J06_exists_pair_mem_stage_interior` | t91J06 | `{X : Type*} (f : ℕ → apm_t91J06_I → X) (hnested : ∀ n, f n '' (univ : Set apm_t91J06_I) ⊆ f (n + 1) '' apm_t91J06_Iinterior) (hcover : (⋃ n, f n '' (univ : Set apm_t91J06_I)) = (univ : Set X)) (x y : X) : ∃ n, x ∈ f n '' apm_t91J06_Iinterior ∧ y ∈ f n '' apm_t91J06_Iinterior` |
| `apm_t91J06_stage_compact` | t91J06 | `{X : Type*} [TopologicalSpace X] (f : ℕ → apm_t91J06_I → X) (hf : ∀ n, Topology.IsEmbedding (f n)) (n : ℕ) : IsCompact (apm_t91J06_stage f n)` |
| `apm_t91J06_stage_mono` | t91J06 | `{X : Type*} (f : ℕ → apm_t91J06_I → X) (hnested : ∀ n, f n '' (univ : Set apm_t91J06_I) ⊆ f (n + 1) '' apm_t91J06_Iinterior) : Monotone (apm_t91J06_stage f)` |
| `apm_t92J05_genusTwo_generators_generate` | t92J05 | `: Subgroup.closure (Set.range (PresentedGroup.of : Fin 4 → apm_t92J05_genusTwoGroup)) = ⊤` |
| `apm_t92J05_genusTwo_surface_relation` | t92J05 | `: (PresentedGroup.of 0 : apm_t92J05_genusTwoGroup) * PresentedGroup.of 1 * (PresentedGroup.of 0)⁻¹ * (PresentedGroup.of 1)⁻¹ * (PresentedGroup.of 2 * PresentedGroup.of 3 * (PresentedGroup.of 2)⁻¹ * (PresentedGroup.of 3)⁻¹) = 1` |
| `apm_t92J05_product_group_of_subsingleton_left` | t92J05 | `{A B : Type} [TopologicalSpace A] [TopologicalSpace B] (a : A) (b : B) [Subsingleton (FundamentalGroup A a)] (hB : Nonempty (FundamentalGroup B b ≃* Multiplicative ℤ)) : Nonempty (FundamentalGroup (A × B) (a, b) ≃* Multiplicative ℤ)` |
| `apm_t92J06_continuous_inl` | t92J06 | `: Continuous apm_t92J06_inl` |
| `apm_t92J06_continuous_inr` | t92J06 | `: Continuous apm_t92J06_inr` |
| `apm_t92J06_inl_base_eq_inr_base` | t92J06 | `: apm_t92J06_inl apm_t92J06_circleBase = apm_t92J06_inr apm_t92J06_circleBase` |
| `apm_t92J06_wedgeDesc_respects` | t92J06 | `{Y : Type*} [TopologicalSpace Y] (f g : C(apm_t92J06_S1, Y)) (hbase : f apm_t92J06_circleBase = g apm_t92J06_circleBase) {x y} (hxy : Relation.EqvGen apm_t92J06_wedgeRel x y) : Sum.elim f g x = Sum.elim f g y` |
| `apm_t92J06_wedgeDesc_unique` | t92J06 | `{Y : Type*} [TopologicalSpace Y] (f g : C(apm_t92J06_S1, Y)) (hbase : f apm_t92J06_circleBase = g apm_t92J06_circleBase) (u : C(apm_t92J06_X, Y)) (hul : ∀ z, u (apm_t92J06_inl z) = f z) (hur : ∀ z, u (apm_t92J06_inr z) = g z) : u = apm_t92J06_wedgeDesc f g hbase` |
| `apm_t92J07_exists_common_regularValue_of_null` | t92J07 | `(m : ℕ) (d : PNat → ℕ) (M : PNat → Type*) [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (apm_t92J07_E (d i)) (M i)] (f : ∀ i, M i → apm_t92J07_E m) (hnull : ∀ i, volume (apm_t92J07_criticalValues (n` |
| `apm_t92J07_isRegularValue_fin_zero` | t92J07 | `{n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (apm_t92J07_E n) M] (f : M → apm_t92J07_E 0) (x : apm_t92J07_E 0) : apm_t92J07_IsRegularValue (n` |
| `apm_t92J08_blowupCurve_hasDerivAt` | t92J08 | `{t : ℝ} (ht : t ≠ 1) : HasDerivAt apm_t92J08_blowupCurve ((apm_t92J08_blowupCurve t) ^ 2) t` |
| `apm_t92J08_blowupCurve_isMIntegralCurveOn` | t92J08 | `: IsMIntegralCurveOn apm_t92J08_blowupCurve apm_t92J08_quadraticField (Iio 1)` |
| `apm_t92J09_inner_integral` | t92J09 | `(θ : ℝ) : (∫ φ in (0 : ℝ)..2 * Real.pi, apm_t92J09_pullbackOmega θ φ) = Real.pi * Real.sin θ ^ 3` |
| `apm_t92J09_param_mem_sphere` | t92J09 | `(θ φ : ℝ) : apm_t92J09_param θ φ ∈ apm_t92J09_sphere` |
| `apm_t92J09_pullbackOmega_eq` | t92J09 | `(θ φ : ℝ) : apm_t92J09_pullbackOmega θ φ = Real.sin θ ^ 3 * Real.cos φ ^ 2` |
| `apm_t92J09_sphereIntegral_eq` | t92J09 | `: apm_t92J09_sphereIntegral = (4 / 3 : ℝ) * Real.pi` |
| `apm_t93a03_connectedSum_not_simplyConnected_of_piOne_equiv` | t93A03 | `{φ₁ φ₂ : T93A03Disk → T93A03Summand} (hspine : T93A03ConnectedSum φ₁ φ₂ ≃ₕ T93A03Spine) (e : FundamentalGroup T93A03Spine t93A03SpineBasepoint ≃* FreeGroup (Fin 2)) : ¬ SimplyConnectedSpace (T93A03ConnectedSum φ₁ φ₂)` |
| `apm_t93a03_continuous_spineQuotient` | t93A03 | `: Continuous apm_t93a03_spineQuotient` |
| `apm_t93a03_inl_base_eq_inr_base` | t93A03 | `: apm_t93a03_spineQuotient (.inl 1) = apm_t93a03_spineQuotient (.inr 1)` |
| `apm_t93a03_spine_not_simplyConnected_of_piOne_equiv` | t93A03 | `(e : FundamentalGroup T93A03Spine t93A03SpineBasepoint ≃* FreeGroup (Fin 2)) : ¬ SimplyConnectedSpace T93A03Spine` |
| `apm_t93a03_spineDesc_respects` | t93A03 | `{Y : Type*} [TopologicalSpace Y] (f g : C(Circle, Y)) (hbase : f 1 = g 1) {x y : Sum Circle Circle} (hxy : Relation.EqvGen T93A03WedgeRel x y) : Sum.elim f g x = Sum.elim f g y` |
| `apm_t93a03_spineDesc_unique` | t93A03 | `{Y : Type*} [TopologicalSpace Y] (f g : C(Circle, Y)) (hbase : f 1 = g 1) (u : C(T93A03Spine, Y)) (hul : ∀ x, u (apm_t93a03_spineQuotient (.inl x)) = f x) (hur : ∀ x, u (apm_t93a03_spineQuotient (.inr x)) = g x) : u = apm_t93a03_spineDesc f g hbase` |
| `apm_t93a03_surjective_spineQuotient` | t93A03 | `: Function.Surjective apm_t93a03_spineQuotient` |
| `apm_t93a04_lineDirection_ne_zero` | t93A04 | `: apm_t93a04_lineDirection ≠ 0` |
| `apm_t93a04_range_sup_span_eq_top_of_projection_surjective` | t93A04 | `{E F G : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [Module ℝ E] [Module ℝ F] [Module ℝ G] (L : E →ₗ[ℝ] F) (q : F →ₗ[ℝ] G) (v : F) (hker : LinearMap.ker q = Submodule.span ℝ ({v} : Set F)) (hsurj : Function.Surjective (q.comp L)) : LinearMap.range L ⊔ Submodule.span ℝ ({v} : Set F) = ⊤` |
| `apm_t94a06_family_contMDiff` | t94A06 | `{E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H] [TopologicalSpace X] (I : ModelWithCorners ℝ E H) [ChartedSpace H X] [IsManifold I ∞ X] (f : X → apm_t94a06_E3) (hf : ContMDiff I 𝓘(ℝ, apm_t94a06_E3) ∞ f) (s : apm_t94a06_E2) : ContMDiff I 𝓘(ℝ, apm_t94a06_E3) ∞ (apm_t94a06_family f s)` |
| `apm_t94a06_family_zero` | t94A06 | `{X : Type*} (f : X → apm_t94a06_E3) : apm_t94a06_family f 0 = f` |
| `apm_t94a06_mfderiv_family` | t94A06 | `{E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H] [TopologicalSpace X] (I : ModelWithCorners ℝ E H) [ChartedSpace H X] [IsManifold I ∞ X] (f : X → apm_t94a06_E3) (hf : ContMDiff I 𝓘(ℝ, apm_t94a06_E3) ∞ f) (s : apm_t94a06_E2) (x : X) : mfderiv I 𝓘(ℝ, apm_t94a06_E3) (apm_t94a06_family f s) x = mfderiv I 𝓘(ℝ, apm_t94a06_E3) f x` |
| `apm_t94a07_fixedPointParam_injective` | t94A07 | `(R r : ℝ) (hr : 0 < r) (hR : r < R) : Function.Injective (apm_t94a07_fixedPointParam R r)` |
| `apm_t94a07_fixedPoints_card` | t94A07 | `(R r : ℝ) (hr : 0 < r) (hR : r < R) : Nat.card {p // p ∈ apm_t94a07_fixedPoints R r} = 4` |
| `apm_t94a07_fixedPoints_eq_range` | t94A07 | `(R r : ℝ) : apm_t94a07_fixedPoints R r = Set.range (apm_t94a07_fixedPointParam R r)` |
| `apm_t94a07_fixedSet_eq` | t94A07 | `(R r : ℝ) (hr : 0 < r) (hR : r < R) : {p \| p ∈ apm_t94a07_torus R r ∧ apm_t94a07_halfTurn p = p} = apm_t94a07_fixedPoints R r` |
| `apm_t94a07_halfTurn_eq_iff` | t94A07 | `(p : apm_t94a07_E3) : apm_t94a07_halfTurn p = p ↔ p 1 = 0 ∧ p 2 = 0` |
| `apm_t94a08_dquadratic1_ne_zero` | t94A08 | `{z : apm_t94a08_C3} (hz : z ≠ 0) : apm_t94a08_dquadratic1 z ≠ 0` |
| `apm_t94a08_e0_ne_zero` | t94A08 | `: (Pi.single 0 1 : apm_t94a08_C3) ≠ 0` |
| `apm_t94a08_hasFDerivAt_quadratic1` | t94A08 | `(z : apm_t94a08_C3) : HasFDerivAt apm_t94a08_quadratic1 (apm_t94a08_dquadratic1 z) z` |
| `apm_t94a08_node_mem_both_branches` | t94A08 | `: apm_t94a08_node ∈ apm_t94a08_sigma2BranchPlus ∩ apm_t94a08_sigma2BranchMinus` |
| `apm_t94a08_node_mem_sigma2` | t94A08 | `: apm_t94a08_node ∈ apm_t94a08_sigma2` |
| `apm_t94a08_quadratic2_factor` | t94A08 | `(z : apm_t94a08_C3) : apm_t94a08_quadratic2 z = (z 1 + Complex.I * z 2) * (z 1 - Complex.I * z 2)` |
| `apm_t94a08_regularLevelSet_quadratic1` | t94A08 | `: apm_t94a08_IsRegularLevelSet apm_t94a08_quadratic1 apm_t94a08_sigma1` |
| `apm_t94a08_sigma2_eq_branches` | t94A08 | `: apm_t94a08_sigma2 = apm_t94a08_sigma2BranchPlus ∪ apm_t94a08_sigma2BranchMinus` |
| `apm_t94a09_contDiff_J` | t94A09 | `: ContDiff ℝ ∞ apm_t94a09_J` |
| `apm_t94a09_contDiff_torusFieldExt` | t94A09 | `: ContDiff ℝ ∞ apm_t94a09_torusFieldExt` |
| `apm_t94a09_exists_smoothSphereField_S3` | t94A09 | `: ∃ V : apm_t94a09_S3 → apm_t94a09_E4, apm_t94a09_SmoothSphereField V ∧ ∀ p, V p ≠ 0` |
| `apm_t94a09_exists_smoothTorusField_unique_zero` | t94A09 | `: ∃ V : apm_t94a09_Torus → ℂ × ℂ, apm_t94a09_SmoothTorusField V ∧ ∃! p, V p = 0` |
| `apm_t94a09_inner_J` | t94A09 | `(x : apm_t94a09_E4) : ⟪apm_t94a09_J x, x⟫_ℝ = 0` |
| `apm_t94a09_J_ne_zero_of_ne_zero` | t94A09 | `{x : apm_t94a09_E4} (hx : x ≠ 0) : apm_t94a09_J x ≠ 0` |
| `apm_t94a09_smoothSphereField_restrict` | t94A09 | `{E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Vext : E → E) (hV : ContDiff ℝ ∞ Vext) (horth : ∀ p : Metric.sphere (0 : E) 1, ⟪Vext p, (p : E)⟫_ℝ = 0) : apm_t94a09_SmoothSphereField (fun p ↦ Vext p)` |
| `apm_t94a09_smoothTorusField_restrict` | t94A09 | `(Vext : (ℂ × ℂ) → (ℂ × ℂ)) (hV : ContDiff ℝ ∞ Vext) (horth : ∀ p : apm_t94a09_Torus, Complex.re (Vext (p.1, p.2)).1 * Complex.re p.1 + Complex.im (Vext (p.1, p.2)).1 * Complex.im p.1 = 0 ∧ Complex.re (Vext (p.1, p.2)).2 * Complex.re p.2 + Complex.im (Vext (p.1, p.2)).2 * Complex.im p.2 = 0) : apm_t94a09_SmoothTorusField (fun p ↦ Vext (p.1, p.2))` |
| `apm_t94a09_torusFieldExt_eq_zero_iff` | t94A09 | `(p : apm_t94a09_Torus) : apm_t94a09_torusFieldExt (p.1, p.2) = 0 ↔ p = (1, 1)` |
| `apm_t94a09_torusFieldExt_tangent` | t94A09 | `(p : apm_t94a09_Torus) : Complex.re (apm_t94a09_torusFieldExt (p.1, p.2)).1 * Complex.re p.1 + Complex.im (apm_t94a09_torusFieldExt (p.1, p.2)).1 * Complex.im p.1 = 0 ∧ Complex.re (apm_t94a09_torusFieldExt (p.1, p.2)).2 * Complex.re p.2 + Complex.im (apm_t94a09_torusFieldExt (p.1, p.2)).2 * Complex.im p.2 = 0` |
| `apm_t94a09_torusScalar_eq_zero_iff` | t94A09 | `(p : ℂ × ℂ) : apm_t94a09_torusScalar p = 0 ↔ p = (1, 1)` |
| `apm_t94a10_ambientExtension_apply_of_isOmega` | t94A10 | `{omega : apm_t94a10_Form 2} (homega : apm_t94a10_IsOmega omega) (x : apm_t94a10_Punctured) (v : Fin 2 → apm_t94a10_E3) : apm_t94a10_ambientExtension omega x.1 v = (x.1 0 * (v 0 1 * v 1 2 - v 0 2 * v 1 1) - x.1 1 * (v 0 0 * v 1 2 - v 0 2 * v 1 0) + x.1 2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)) / (Real.sqrt (x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2)) ^ 3` |
| `apm_t94a10_radial_denominator_eq_one_of_norm_eq_one` | t94A10 | `(x : apm_t94a10_E3) (hx : ‖x‖ = 1) : (Real.sqrt (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)) ^ 3 = 1` |
| `apm_t94a10_radial_denominator_ne_zero` | t94A10 | `(x : apm_t94a10_Punctured) : (Real.sqrt (x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2)) ^ 3 ≠ 0` |
| `apm_t94a10_radial_denominator_pos` | t94A10 | `(x : apm_t94a10_Punctured) : 0 < (Real.sqrt (x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2)) ^ 3` |
| `apm_t94a10_radial_sq_eq_norm_sq` | t94A10 | `(x : apm_t94a10_E3) : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = ‖x‖ ^ 2` |
| `apm_t94a10_radial_sq_pos` | t94A10 | `(x : apm_t94a10_Punctured) : 0 < x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2` |
| `apm_t94a10_radial_sqrt_ne_zero` | t94A10 | `(x : apm_t94a10_Punctured) : Real.sqrt (x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2) ≠ 0` |
| `apm_t94J04_eulerChar_cover_arithmetic` | t94J04 | `(k : ℕ) : (2 : ℤ) - 2 * ((k : ℤ) + 1) = (k : ℤ) * (2 - 2 * 2)` |
| `apm_t94J04_quotient_equiv_of_equal_positive_index` | t94J04 | `{G : Type*} [Group G] (H K : Subgroup G) (k : ℕ) (hk : 0 < k) (hH : H.index = k) (hK : K.index = k) : Nonempty ((G ⧸ H) ≃ (G ⧸ K))` |
| `apm_t94J04_subgroups_equiv_of_index_one` | t94J04 | `{G : Type*} [Group G] (H K : Subgroup G) (hH : H.index = 1) (hK : K.index = 1) : Nonempty (H ≃* K)` |
| `apm_t94J05_contractibleSpace_complement` | t94J05 | `(q : apm_t94J05_S3) : ContractibleSpace {y : apm_t94J05_S3 // y ≠ q}` |
| `apm_t94J05_factor_through_complement` | t94J05 | `(f : C(apm_t94J05_Torus, apm_t94J05_S3)) (hnot_surj : ¬Function.Surjective f) : ∃ q : apm_t94J05_S3, ∃ g : C(apm_t94J05_Torus, {y : apm_t94J05_S3 // y ≠ q}), ∀ x, (g x : apm_t94J05_S3) = f x` |
| `apm_t94J05_nullhomotopic_of_factor` | t94J05 | `(f : C(apm_t94J05_Torus, apm_t94J05_S3)) (q : apm_t94J05_S3) (g : C(apm_t94J05_Torus, {y : apm_t94J05_S3 // y ≠ q})) (hfg : ∀ x, (g x : apm_t94J05_S3) = f x) (p : {y : apm_t94J05_S3 // y ≠ q}) (hg : ContinuousMap.Homotopic g (ContinuousMap.const _ p)) : ContinuousMap.Homotopic f (ContinuousMap.const apm_t94J05_Torus (p : apm_t94J05_S3))` |
| `apm_t94J05_nullhomotopic_of_not_surjective` | t94J05 | `(f : C(apm_t94J05_Torus, apm_t94J05_S3)) (hf : ¬ Function.Surjective f) : ContinuousMap.Homotopic f (ContinuousMap.const apm_t94J05_Torus apm_t94J05_northPole)` |
| `apm_t94J05_nullhomotopic_to_northPole` | t94J05 | `(f : C(apm_t94J05_Torus, apm_t94J05_S3)) (p : apm_t94J05_S3) (hf : ContinuousMap.Homotopic f (ContinuousMap.const apm_t94J05_Torus p)) : ContinuousMap.Homotopic f (ContinuousMap.const apm_t94J05_Torus apm_t94J05_northPole)` |
| `apm_t94J06_boundary_domination` | t94J06 | `{z : ℂ} (hz : ‖z‖ = 7) : ‖apm_t94J06_function z - z ^ 4‖ < ‖z ^ 4‖` |
| `apm_t94J06_boundary_homotopy_ne_zero` | t94J06 | `: ∀ t : Set.Icc (0 : ℝ) 1, ∀ z ∈ Metric.sphere (0 : ℂ) 7, z ^ 4 + (t.1 : ℂ) * (apm_t94J06_function z - z ^ 4) ≠ 0` |
| `apm_t94J06_boundary_ne_zero` | t94J06 | `: ∀ z ∈ Metric.sphere (0 : ℂ) 7, apm_t94J06_function z ≠ 0` |
| `apm_t94J06_boundaryHomotopy_continuous` | t94J06 | `: Continuous apm_t94J06_boundaryHomotopy` |
| `apm_t94J06_boundaryHomotopy_ne_zero` | t94J06 | `(p : Set.Icc (0 : ℝ) 1 × Metric.sphere (0 : ℂ) 7) : apm_t94J06_boundaryHomotopy p ≠ 0` |
| `apm_t94J06_continuous` | t94J06 | `: Continuous apm_t94J06_function` |
| `apm_t94J09_continuous_n6Quotient` | t94J09 | `: Continuous apm_t94J09_n6Quotient` |
| `apm_t94J09_continuous_polygonQuotient` | t94J09 | `: Continuous apm_t94J09_polygonQuotient` |
| `apm_t94J09_edgeCount_eq` | t94J09 | `: apm_t94J09_edgeCount apm_t94J09_word = 7` |
| `apm_t94J09_eqvGen_respects` | t94J09 | `{X Z : Type*} {r : X → X → Prop} (f : X → Z) (hr : ∀ x y, r x y → f x = f y) {x y : X} (hxy : Relation.EqvGen r x y) : f x = f y` |
| `apm_t94J09_eulerCharacteristic_eq` | t94J09 | `: apm_t94J09_eulerCharacteristic apm_t94J09_word apm_t94J09_vertexClass = -4` |
| `apm_t94J09_n6Desc_unique` | t94J09 | `{Z : Type*} [TopologicalSpace Z] (f : C(apm_t94J09_Disk, Z)) (hr : ∀ x y, apm_t94J09_N6Rel x y → f x = f y) (u : C(apm_t94J09_N6, Z)) (hu : ∀ x, u (apm_t94J09_n6Quotient x) = f x) : u = apm_t94J09_n6Desc f hr` |
| `apm_t94J09_nonorientableGenus_eq` | t94J09 | `: apm_t94J09_nonorientableGenus (apm_t94J09_eulerCharacteristic apm_t94J09_word apm_t94J09_vertexClass) = 6` |
| `apm_t94J09_not_oppositeOrientationPairing` | t94J09 | `: ¬apm_t94J09_hasOppositeOrientationPairing apm_t94J09_word` |
| `apm_t94J09_polygonDesc_unique` | t94J09 | `{Z : Type*} [TopologicalSpace Z] (f : C(apm_t94J09_Disk, Z)) (hr : ∀ x y, apm_t94J09_PolygonRel x y → f x = f y) (u : C(apm_t94J09_PolygonSurface, Z)) (hu : ∀ x, u (apm_t94J09_polygonQuotient x) = f x) : u = apm_t94J09_polygonDesc f hr` |
| `apm_t94J09_surjective_n6Quotient` | t94J09 | `: Function.Surjective apm_t94J09_n6Quotient` |
| `apm_t94J09_surjective_polygonQuotient` | t94J09 | `: Function.Surjective apm_t94J09_polygonQuotient` |
| `apm_t94J09_vertexCount_eq` | t94J09 | `: apm_t94J09_vertexCount apm_t94J09_vertexClass = 2` |
| `apm_t95j06_flow_add` | t95J06 | `(H : apm_t95j06_S5 × ℝ → apm_t95j06_S5) (hH : apm_t95j06_isHopfFlow H) (z : apm_t95j06_S5) (s t : ℝ) : H (H (z, s), t) = H (z, s + t)` |
| `apm_t95j06_flow_periodic` | t95J06 | `(H : apm_t95j06_S5 × ℝ → apm_t95j06_S5) (hH : apm_t95j06_isHopfFlow H) (z : apm_t95j06_S5) (t : ℝ) : H (z, t + 2 * Real.pi) = H (z, t)` |
| `apm_t95j06_flow_zero` | t95J06 | `(H : apm_t95j06_S5 × ℝ → apm_t95j06_S5) (hH : apm_t95j06_isHopfFlow H) (z : apm_t95j06_S5) : H (z, 0) = z` |
| `apm_t95j06_T_invariant` | t95J06 | `(H : apm_t95j06_S5 × ℝ → apm_t95j06_S5) (hH : apm_t95j06_isHopfFlow H) : apm_t95j06_IsInvariant H apm_t95j06_T` |
| `apm_t96A03_continuous_inl` | t96A03 | `(h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) : Continuous (apm_t96A03_inl h)` |
| `apm_t96A03_continuous_inr` | t96A03 | `(h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) : Continuous (apm_t96A03_inr h)` |
| `apm_t96A03_continuous_quotient` | t96A03 | `(h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) : Continuous (apm_t96A03_quotient h)` |
| `apm_t96A03_glueDesc_respects` | t96A03 | `{Z : Type*} [TopologicalSpace Z] (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) (f g : C(apm_t96A03_Sphere2, Z)) (hfg : ∀ x : apm_t96A03_EquatorSpace, f x.1 = g (h x).1) {x y : Sum apm_t96A03_Sphere2 apm_t96A03_Sphere2} (hxy : Relation.EqvGen (apm_t96A03_glueRel h) x y) : Sum.elim f g x = Sum.elim f g y` |
| `apm_t96A03_glueDesc_unique` | t96A03 | `{Z : Type*} [TopologicalSpace Z] (h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) (f g : C(apm_t96A03_Sphere2, Z)) (hfg : ∀ x : apm_t96A03_EquatorSpace, f x.1 = g (h x).1) (u : C(apm_t96A03_X h, Z)) (hul : ∀ x, u (apm_t96A03_inl h x) = f x) (hur : ∀ x, u (apm_t96A03_inr h x) = g x) : u = apm_t96A03_glueDesc h f g hfg` |
| `apm_t96A03_inl_eq_inr_on_equator` | t96A03 | `(h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) : (fun x : apm_t96A03_EquatorSpace => apm_t96A03_inl h x.1) = (fun x => apm_t96A03_inr h (h x).1)` |
| `apm_t96A03_isQuotientMap_quotient` | t96A03 | `(h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) : Topology.IsQuotientMap (apm_t96A03_quotient h)` |
| `apm_t96A03_quotient_glue` | t96A03 | `(h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) (x : apm_t96A03_EquatorSpace) : apm_t96A03_quotient h (Sum.inl x.1) = apm_t96A03_quotient h (Sum.inr (h x).1)` |
| `apm_t96A03_surjective_quotient` | t96A03 | `(h : apm_t96A03_EquatorSpace ≃ₜ apm_t96A03_EquatorSpace) : Function.Surjective (apm_t96A03_quotient h)` |
| `apm_t96a08_isPiecewiseSmoothPath_const` | t96A08 | `{E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M] (p : M) : apm_t96a08_IsPiecewiseSmoothPath I (fun _ : ℝ ↦ p)` |
| `apm_t96a08_lineIntegral_const` | t96A08 | `{E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M] (ω : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (p : M) : apm_t96a08_LineIntegral I ω (fun _ : ℝ ↦ p) = 0` |
| `apm_t96a08_potential_base_eq_zero` | t96A08 | `{E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M] (ω : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (base : M) (f : M → ℝ) (hf : ∀ p : M, ∀ γ : ℝ → M, apm_t96a08_IsPiecewiseSmoothPath I γ → γ 0 = base → γ 1 = p → f p = apm_t96a08_LineIntegral I ω γ) : f base = 0` |
| `apm_t96a08_potential_unique` | t96A08 | `{E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] (I : ModelWithCorners ℝ E E) [ChartedSpace E M] (ω : ∀ p : M, TangentSpace I p →L[ℝ] ℝ) (base : M) (hreachable : ∀ p : M, ∃ γ : ℝ → M, apm_t96a08_IsPiecewiseSmoothPath I γ ∧ γ 0 = base ∧ γ 1 = p) (f g : M → ℝ) (hf : ∀ p : M, ∀ γ : ℝ → M, apm_t96a08_IsPiecewiseSmoothPath I γ → γ 0 = base → γ 1 = p → f p = apm_t96a08_LineIntegral I ω γ) (hg : ∀ p : M, ∀ γ : ℝ → M, apm_t96a08_IsPiecewiseSmoothPath I γ → γ 0 = base → γ 1 = p → g p = apm_t96a08_LineIntegral I ω γ) : f = g` |
| `apm_t96j05_exists_positive_nonempty_radialLevel` | t96J05 | `{n : ℕ} {X : Set (apm_t96j05_E n)} (hXnz : ∃ x : X, (x.1 : apm_t96j05_E n) ≠ 0) : ∃ r : ℝ, 0 < r ∧ Nonempty (apm_t96j05_radialLevel X r)` |
| `apm_t96j05_exists_positive_nonempty_radialLevel_of_nontrivial` | t96J05 | `{n : ℕ} {X : Set (apm_t96j05_E n)} [Nonempty X] [Nontrivial X] : ∃ r : ℝ, 0 < r ∧ Nonempty (apm_t96j05_radialLevel X r)` |
| `apm_t96j06_coordinatePoint_mem` | t96J06 | `: apm_t96j06_coordinatePoint ∈ apm_t96j06_RP1InRP2` |
| `apm_t96j06_mk_pair_mem_ProductSubspace_iff` | t96J06 | `(u v : Fin 3 → ℝ) (hu : u ≠ 0) (hv : v ≠ 0) : (Projectivization.mk ℝ u hu, Projectivization.mk ℝ v hv) ∈ apm_t96j06_ProductSubspace ↔ u 2 = 0 ∧ v 2 = 0` |
| `apm_t96j06_offLinePoint_not_mem` | t96J06 | `: apm_t96j06_offLinePoint ∉ apm_t96j06_RP1InRP2` |
| `apm_t96j06_ProductSubspace_ne_univ` | t96J06 | `: apm_t96j06_ProductSubspace ≠ Set.univ` |
| `apm_t96j06_ProductSubspace_nonempty` | t96J06 | `: apm_t96j06_ProductSubspace.Nonempty` |
| `apm_t96j06_single_two_ne` | t96J06 | `: (Pi.single 2 1 : Fin 3 → ℝ) ≠ 0` |
| `apm_t96j06_single_zero_ne` | t96J06 | `: (Pi.single 0 1 : Fin 3 → ℝ) ≠ 0` |
| `apm_t96j07_not_fixed_axis_clause` | t96J07 | `: ¬(∀ x : apm_t96j07_V, (x ≠ 0 → apm_t96j07_projectivelyEq x (apm_t96j07_A x)) ↔ ∃ i : Fin 4, apm_t96j07_projectivelyEq x (apm_t96j07_axis i))` |
| `apm_t96j08_extDeriv_etaForm_apply` | t96J08 | `(η : apm_t96j08_Point → apm_t96j08_Point →L[ℝ] ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (p u v : apm_t96j08_Point) : extDeriv (apm_t96j08_etaForm η) p ![u, v] = apm_t96j08_dOneForm η p u v` |
| `apm_t96j08_integral_singularTerm_eq_zero` | t96J08 | `: (∫ q : apm_t96j08_DiskPoint in Metric.closedBall 0 1, ((q 0) ^ 2 - (q 1) ^ 2) / Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)) = 0` |
| `apm_t96j08_not_isClosed` | t96J08 | `: ¬apm_t96j08_IsClosed` |
| `apm_t96j08_pullback_eq` | t96J08 | `(q : apm_t96j08_DiskPoint) : apm_t96j08_omega (apm_t96j08_upperHemisphere q) (apm_t96j08_paramTangentX q) (apm_t96j08_paramTangentY q) = 1 + Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2) + ((q 0) ^ 2 - (q 1) ^ 2) / Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2)` |
| `apm_t96j08_singularTerm_swap` | t96J08 | `(q : apm_t96j08_DiskPoint) : ((apm_t96j08_swap q 0) ^ 2 - (apm_t96j08_swap q 1) ^ 2) / Real.sqrt (1 - (apm_t96j08_swap q 0) ^ 2 - (apm_t96j08_swap q 1) ^ 2) = -(((q 0) ^ 2 - (q 1) ^ 2) / Real.sqrt (1 - (q 0) ^ 2 - (q 1) ^ 2))` |
| `apm_t96j08_swapEquiv_apply` | t96J08 | `(q : apm_t96j08_DiskPoint) : apm_t96j08_swapEquiv q = apm_t96j08_swap q` |
| `apm_t97a01_continuous_quotientTorusRP2` | t97A01 | `: Continuous apm_t97a01_quotientTorusRP2` |
| `apm_t97a01_continuous_quotientX` | t97A01 | `: Continuous apm_t97a01_quotientX` |
| `apm_t97a01_quotientTorusRP2_identifies_c` | t97A01 | `(t : Set.Icc (0 : ℝ) 1) : apm_t97a01_quotientTorusRP2 (apm_t97a01_edgePoint 4 t) = apm_t97a01_quotientTorusRP2 (apm_t97a01_edgePoint 5 t)` |
| `apm_t97a01_quotientX_identifies_a` | t97A01 | `(t : Set.Icc (0 : ℝ) 1) : apm_t97a01_quotientX (apm_t97a01_edgePoint 0 t) = apm_t97a01_quotientX (apm_t97a01_edgePoint 1 t)` |
| `apm_t97a01_RelX_to_standardN3` | t97A01 | `{x y : apm_t97a01_Disk} (h : apm_t97a01_RelX x y) : ConstructionTargets.Surfaces.SurfaceRel false 3 x y` |
| `apm_t97a01_standardN3_to_RelX` | t97A01 | `{x y : apm_t97a01_Disk} (h : ConstructionTargets.Surfaces.SurfaceRel false 3 x y) : apm_t97a01_RelX x y` |
| `apm_t97a01_surjective_quotientTorusRP2` | t97A01 | `: Function.Surjective apm_t97a01_quotientTorusRP2` |
| `apm_t97a01_surjective_quotientX` | t97A01 | `: Function.Surjective apm_t97a01_quotientX` |
| `apm_t97A02_homotopic_const_of_projection_homotopies` | t97A02 | `{X : Type} [TopologicalSpace X] (f : C(X, apm_t97A02_Torus)) (p : apm_t97A02_Torus) (h₁ : ContinuousMap.Homotopic (apm_t97A02_firstProjection f) (ContinuousMap.const X p.1)) (h₂ : ContinuousMap.Homotopic (apm_t97A02_secondProjection f) (ContinuousMap.const X p.2)) : ContinuousMap.Homotopic f (ContinuousMap.const X p)` |
| `apm_t97A03_base_north_eq` | t97A03 | `(A B : Circle) : (Quotient.mk _ (.inl A) : apm_t97A03_BaseSpace A B) = Quotient.mk _ (.inr apm_t97A03_north)` |
| `apm_t97A03_base_south_eq` | t97A03 | `(A B : Circle) : (Quotient.mk _ (.inl B) : apm_t97A03_BaseSpace A B) = Quotient.mk _ (.inr apm_t97A03_south)` |
| `apm_t97A03_fiber_equiv_fin_two` | t97A03 | `{A B : Circle} {Y : Type} (p : Y → apm_t97A03_BaseSpace A B) (hdegree : ∀ x : apm_t97A03_BaseSpace A B, Nat.card (p ⁻¹' ({x} : Set _)) = 2) (x : apm_t97A03_BaseSpace A B) : Nonempty ((p ⁻¹' ({x} : Set _)) ≃ Fin 2)` |
| `apm_t97A03_surjective_of_fiber_card_two` | t97A03 | `{A B : Circle} {Y : Type} (p : Y → apm_t97A03_BaseSpace A B) (hdegree : ∀ x : apm_t97A03_BaseSpace A B, Nat.card (p ⁻¹' ({x} : Set _)) = 2) : Function.Surjective p` |
| `apm_t97a04_L_eq_matrix_mulVec` | t97A04 | `(p : apm_t97a04_RealPlane) : apm_t97a04_L p = (apm_t97a04_matrix.map ((Int.castRingHom ℝ))).mulVec p` |
| `apm_t97a04_lefschetz_arithmetic` | t97A04 | `: (1 : ℤ) = 1 - Matrix.trace apm_t97a04_matrix + 3` |
| `apm_t97a04_matrix_det` | t97A04 | `: Matrix.det apm_t97a04_matrix = 3` |
| `apm_t97a04_matrix_mulVec` | t97A04 | `(v : apm_t97a04_IntPlane) : apm_t97a04_matrix.mulVec v = ![2 * v 0 + v 1, v 1 - v 0]` |
| `apm_t97a04_matrix_trace` | t97A04 | `: Matrix.trace apm_t97a04_matrix = 3` |
| `apm_t97J01_surjective_of_connected` | t97J01 | `{X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ConnectedSpace X] [PreconnectedSpace Y] (p : X → Y) (hp : IsCoveringMap p) : Function.Surjective p` |
| `apm_t97J02_candidate_eulerCharacteristics` | t97J02 | `: apm_t97J02_eulerCharacteristic false 4 = -2 ∧ apm_t97J02_eulerCharacteristic false 12 = 5 * apm_t97J02_eulerCharacteristic false 4 ∧ apm_t97J02_eulerCharacteristic true 7 = 6 * apm_t97J02_eulerCharacteristic false 4 ∧ apm_t97J02_eulerCharacteristic false 14 = 6 * apm_t97J02_eulerCharacteristic false 4` |
| `apm_t97J02_continuous_surfaceQuotient` | t97J02 | `(orientable : Bool) (genus : ℕ) : Continuous (apm_t97J02_surfaceQuotient orientable genus)` |
| `apm_t97J02_nonorientable_genus_of_euler_eq` | t97J02 | `(n genus : ℕ) (h : apm_t97J02_eulerCharacteristic false genus = (n : ℤ) * apm_t97J02_eulerCharacteristic false 4) : genus = 2 * n + 2` |
| `apm_t97J02_orientable_genus_of_euler_eq` | t97J02 | `(n genus : ℕ) (h : apm_t97J02_eulerCharacteristic true genus = (n : ℤ) * apm_t97J02_eulerCharacteristic false 4) : genus = n + 1` |
| `apm_t97J02_surjective_surfaceQuotient` | t97J02 | `(orientable : Bool) (genus : ℕ) : Function.Surjective (apm_t97J02_surfaceQuotient orientable genus)` |
| `apm_t97J03_fundamentalGroupMap_injective_of_retraction` | t97J03 | `{A X : Type} [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) (a : A) (r : C(X, A)) (hr : ∀ x, r (i x) = x) : Function.Injective (FundamentalGroup.map i a)` |
| `apm_t97J03_no_disk_retraction` | t97J03 | `[Nontrivial (FundamentalGroup apm_t97J03_Circle ⟨1, by simp⟩)] : ¬∃ r : C(apm_t97J03_Disk, apm_t97J03_Circle), ∀ z : apm_t97J03_Circle, r ⟨z.1, le_of_eq z.2⟩ = z` |
| `apm_t97J03_no_retraction_of_subsingleton_fundamentalGroup` | t97J03 | `{A X : Type} [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) (a : A) [Subsingleton (FundamentalGroup X (i a))] [Nontrivial (FundamentalGroup A a)] : ¬∃ r : C(X, A), ∀ x, r (i x) = x` |
| `apm_t97J04_continuous_circleInclusion` | t97J04 | `: Continuous apm_t97J04_circleInclusion` |
| `apm_t97J04_continuous_torusInclusion` | t97J04 | `: Continuous apm_t97J04_torusInclusion` |
| `apm_t97J04_continuous_wedgeQuotient` | t97J04 | `: Continuous apm_t97J04_wedgeQuotient` |
| `apm_t97J04_inl_base_eq_inr_base` | t97J04 | `: (Quotient.mk _ (.inl (1, 1)) : apm_t97J04_X) = Quotient.mk _ (.inr 1)` |
| `apm_t97J04_summandInclusions_injective` | t97J04 | `: Function.Injective apm_t97J04_torusInclusion ∧ Function.Injective apm_t97J04_circleInclusion` |
| `apm_t97J04_surjective_wedgeQuotient` | t97J04 | `: Function.Surjective apm_t97J04_wedgeQuotient` |
| `apm_t97J04_wedgeDesc_respects` | t97J04 | `{Z : Type*} [TopologicalSpace Z] (f : C(apm_t97J04_Torus, Z)) (g : C(Circle, Z)) (hbase : f (1, 1) = g 1) {x y} (hxy : Relation.EqvGen apm_t97J04_WedgeRel x y) : Sum.elim f g x = Sum.elim f g y` |
| `apm_t97J04_wedgeDesc_unique` | t97J04 | `{Z : Type*} [TopologicalSpace Z] (f : C(apm_t97J04_Torus, Z)) (g : C(Circle, Z)) (hbase : f (1, 1) = g 1) (u : C(apm_t97J04_X, Z)) (huT : ∀ x, u (apm_t97J04_torusInclusion x) = f x) (huC : ∀ z, u (apm_t97J04_circleInclusion z) = g z) : u = apm_t97J04_wedgeDesc f g hbase` |
| `apm_t97J05_f_gamma_eq_value` | t97J05 | `{t : ℝ} (ht : t ∈ apm_t97J05_parameterDomain) : apm_t97J05_f (apm_t97J05_gamma t) = apm_t97J05_value` |
| `apm_t97J05_gamma_bijOn` | t97J05 | `: Set.BijOn apm_t97J05_gamma apm_t97J05_parameterDomain apm_t97J05_parameterTarget` |
| `apm_t97J05_gamma_injOn` | t97J05 | `: Set.InjOn apm_t97J05_gamma apm_t97J05_parameterDomain` |
| `apm_t97J05_gamma_mem_parameterTarget` | t97J05 | `{t : ℝ} (ht : t ∈ apm_t97J05_parameterDomain) : apm_t97J05_gamma t ∈ apm_t97J05_parameterTarget` |
| `apm_t97J05_gamma_surjOn` | t97J05 | `: Set.SurjOn apm_t97J05_gamma apm_t97J05_parameterDomain apm_t97J05_parameterTarget` |
| `apm_t98a03_threeFoldCover_fiber_equiv_fin_three` | t98A03 | `{X : Type*} [TopologicalSpace X] (C : apm_t98a03_Cover X) (hC : apm_t98a03_IsConnectedThreeFoldCover C) (x : X) : Nonempty ({e : C.total // C.projection e = x} ≃ Fin 3)` |
| `apm_t98a03_threeFoldCover_surjective` | t98A03 | `{X : Type*} [TopologicalSpace X] (C : apm_t98a03_Cover X) (hC : apm_t98a03_IsConnectedThreeFoldCover C) : Function.Surjective C.projection` |
| `apm_t98a03_wedge_base_eq` | t98A03 | `(t₀ : apm_t98a03_Torus) (r₀ : apm_t98a03_RP2) : apm_t98a03_basepoint t₀ r₀ = Quotient.mk _ (.inr r₀)` |
| `apm_t98a04_circleOrbit_subset_fiber` | t98A04 | `(z : apm_t98a04_S3) : apm_t98a04_circleOrbit z ⊆ apm_t98a04_fiber (apm_t98a04_hopf z)` |
| `apm_t98a04_continuous_hopf` | t98A04 | `: Continuous apm_t98a04_hopf` |
| `apm_t98a05_circleClosed_of_extDeriv_formula` | t98A05 | `(alpha : apm_t98a05_Form 1) (hd : ∀ (x : apm_t98a05_E3) (v : Fin 2 → apm_t98a05_E3), extDeriv alpha x v = 2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)) : apm_t98a05_isCircleClosed alpha` |
| `apm_t98a05_wedgeEval_eq_zero` | t98A05 | `(alpha : apm_t98a05_Form 1) (halpha : apm_t98a05_isAlpha alpha) (beta : apm_t98a05_Form 2) (hbeta : apm_t98a05_isBeta beta) (x : apm_t98a05_E3) (v : Fin 3 → apm_t98a05_E3) : apm_t98a05_wedgeEval alpha beta x v = 0` |
| `apm_t98J03_sphere_zero_coord` | t98J03 | `(x : apm_t98J03_Sphere 0) : (x.1 0) = 1 ∨ (x.1 0) = -1` |
| `apm_t98J03_sphereZero_positive_homology_isZero` | t98J03 | `(k : ℕ) (hk : 0 < k) : Limits.IsZero (apm_t98J03_H 0 k)` |
| `apm_t98J03_sphereZeroSign_injective` | t98J03 | `: Function.Injective apm_t98J03_sphereZeroSign` |
| `apm_t98J03_sphereZeroSign_surjective` | t98J03 | `: Function.Surjective apm_t98J03_sphereZeroSign` |
| `apm_t99J03_nonorientable_genus_eq_of_eulerCharacteristic_eq` | t99J03 | `{g h : ℕ} (heq : apm_t99J03_eulerCharacteristic false g = apm_t99J03_eulerCharacteristic false h) : g = h` |
| `apm_t99J03_orientable_genus_eq_of_eulerCharacteristic_eq` | t99J03 | `{g h : ℕ} (heq : apm_t99J03_eulerCharacteristic true g = apm_t99J03_eulerCharacteristic true h) : g = h` |
| `apm_t99J03_unique_classification_of_exists_of_euler_invariant` | t99J03 | `(X : Type) [TopologicalSpace X] (hex : (∃ g : ℕ, Nonempty (X ≃ₜ apm_t99J03_Surface true g)) ∨ (∃ k : ℕ, 0 < k ∧ Nonempty (X ≃ₜ apm_t99J03_Surface false k))) (hχo : ∀ g h : ℕ, Nonempty (X ≃ₜ apm_t99J03_Surface true g) → Nonempty (X ≃ₜ apm_t99J03_Surface true h) → apm_t99J03_eulerCharacteristic true g = apm_t99J03_eulerCharacteristic true h) (hχn : ∀ g h : ℕ, Nonempty (X ≃ₜ apm_t99J03_Surface false g) → Nonempty (X ≃ₜ apm_t99J03_Surface false h) → apm_t99J03_eulerCharacteristic false g = apm_t99J03_eulerCharacteristic false h) : (∃! g : ℕ, Nonempty (X ≃ₜ apm_t99J03_Surface true g)) ∨ (∃! k : ℕ, 0 < k ∧ Nonempty (X ≃ₜ apm_t99J03_Surface false k))` |
| `apm_t99J04_dualCoordinates_bijective` | t99J04 | `{n : ℕ} (hn : 0 < n) {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (hfin : Module.finrank ℝ V = n) (phi : Fin n → Module.Dual ℝ V) (hli : LinearIndependent ℝ phi) : Function.Bijective (fun v : V ↦ fun i ↦ phi i v)` |
| `apm_t99J04_surjective_of_bijective_mfderiv_of_localIFT` | t99J04 | `{E E' X Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [CompleteSpace E'] [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X] [ChartedSpace E X] [IsManifold (modelWithCornersSelf ℝ E) ⊤ X] [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace E' Y] [IsManifold (modelWithCornersSelf ℝ E') ⊤ Y] (f : X → Y) (hf : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') ⊤ f) (hbij : ∀ x, Function.Bijective (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') f x)) (hlocalIFT : ∀ x, ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') ⊤ f x → Function.Bijective (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') f x) → IsLocalDiffeomorphAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E') ⊤ f x) : Function.Surjective f` |
| `apm_t99J04_surjective_of_isLocalDiffeomorph` | t99J04 | `{E E' X Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X] [ChartedSpace E X] [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace E' Y] (f : X → Y) (hf : IsLocalDiffeomorph (𝓘(ℝ, E)) (𝓘(ℝ, E')) ⊤ f) : Function.Surjective f` |
| `apm_translation_symmDiff_tendsto_zero` | a99J02 | `(B : Set ℝ) (hB : MeasurableSet B) (hBfin : volume B ≠ ⊤) (x : ℝ) : Tendsto (fun y => volume (((apmSubtractionMap y) ⁻¹' B) ∆ ((apmSubtractionMap x) ⁻¹' B))) (nhds x) (nhds 0)` |
| `apmAssociated_eq_C_mul_unique` | b96A03 | `{F n : Type*} [Field F] {x y : MvPolynomial n F} (hy : y ≠ 0) (hxy : Associated x y) : ∃! c : Fˣ, x = MvPolynomial.C (c : F) * y` |
| `apmB03NotIntegrallyClosed` | b03J03 | `: ¬ IsIntegrallyClosed (AdjoinRoot apmB03Poly)` |
| `apmB03RootSq` | b03J03 | `: AdjoinRoot.root apmB03Poly * AdjoinRoot.root apmB03Poly = 5` |
| `apmIndicator_memLp_two` | a99J02 | `{E : Set ℝ} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤) : MemLp (apmIndicator E) 2 volume` |
| `apmLogAbsPositive_le_abs` | a99J01 | `{X : Type*} (f : X → ℝ) (x : X) : apmLogAbsPositive f x ≤ ENNReal.ofReal \|f x\|` |
| `apmLogAbsPositive_setLIntegral_ne_top` | a99J01 | `{X : Type*} [MeasurableSpace X] {mu : Measure X} {f : X → ℝ} (hf : Integrable f mu) (E : Set X) : ∫⁻ x in E, apmLogAbsPositive f x ∂mu ≠ ⊤` |
| `apmLogIntegralOn_eq_bot_of_negative_eq_top` | a99J01 | `{X : Type*} [MeasurableSpace X] {mu : Measure X} {f : X → ℝ} {E : Set X} (hneg : ∫⁻ x in E, apmLogAbsNegative f x ∂mu = ⊤) : apmLogIntegralOn f E mu = ⊥` |
| `apmLogIntegralOn_le_of_negative_eq_top` | a99J01 | `{X : Type*} [MeasurableSpace X] {mu : Measure X} {f : X → ℝ} {E : Set X} (hneg : ∫⁻ x in E, apmLogAbsNegative f x ∂mu = ⊤) (r : EReal) : apmLogIntegralOn f E mu ≤ r` |
| `apmN_eq_apmEc` | a03J01 | `{d : ℕ} (E : ℕ → Set (EuclideanSpace ℝ (Fin d))) : ∀ x, apmN E x = (apmEc E x : ENNReal)` |
| `apmPoissonIntegral_congr_ae` | a98J03 | `(y : ℝ) {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) : apmPoissonIntegral y f = apmPoissonIntegral y g` |
| `apmPoissonIntegral_L2_contraction` | a98J03 | `{y : ℝ} (hy : 0 < y) {f : ℝ → ℝ} (hf : MemLp f 2 volume) : eLpNorm (apmPoissonIntegral y f) 2 volume ≤ eLpNorm f 2 volume` |
| `apmPoissonIntegral_memLp` | a98J03 | `{y : ℝ} (hy : 0 < y) {f : ℝ → ℝ} (hf : MemLp f 2 volume) : MemLp (apmPoissonIntegral y f) 2 volume` |
| `apmPoissonIntegral_toLp_congr` | a98J03 | `{y : ℝ} (hy : 0 < y) {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (hfg : f =ᵐ[volume] g) : (apmPoissonIntegral_memLp hy hf).toLp (apmPoissonIntegral y f) = (apmPoissonIntegral_memLp hy hg).toLp (apmPoissonIntegral y g)` |
| `apmPoissonKernel_eq_radial` | a98J03 | `(y x : ℝ) : apmPoissonKernel y x = ConstructionTargets.RadialMajorantAE.poissonKernel y x` |
| `apmPoissonKernel_integrable` | a98J03 | `{y : ℝ} (hy : 0 < y) : Integrable (apmPoissonKernel y) volume` |
| `apmPoissonKernel_integral_one` | a98J03 | `{y : ℝ} (hy : 0 < y) : ∫ x, apmPoissonKernel y x ∂volume = 1` |
| `apmPoissonKernel_nonneg` | a98J03 | `{y : ℝ} (hy : 0 < y) (x : ℝ) : 0 ≤ apmPoissonKernel y x` |
| `apmSmallestPrimeDivisor_eq_minFac` | b01A02 | `{p n : ℕ} (h : apmSmallestPrimeDivisor p n) : p = n.minFac` |
| `apmTwoGeneratorIdeal_not_principal` | b03J02 | `(R : Type*) [CommRing R] [IsDomain R] (a : R) (ha : a ≠ 0) (hna : ¬IsUnit a) : ¬(apmTwoGeneratorIdeal a).IsPrincipal` |
| `arctan_pos` | a95J05 | `' {t : ℝ} (ht : 0 < t) : 0 < arctan t` |
| `arctan_zero` | a95J05 | `' : arctan 0 = 0` |
| `argStar_eq` | a02J07 | `(z : ℂ) : argStar z = arg (-z) + π` |
| `argStar_lt_two_pi` | a02J07 | `{z : ℂ} (hz : z ∈ posSlitPlane) : argStar z < 2 * π` |
| `argStar_pos` | a02J07 | `{z : ℂ} (hz : z ∈ posSlitPlane) : 0 < argStar z` |
| `auxProd_continuousOn` | a95A05 | `{f : ℂ → ℂ} (hf : ContinuousOn f (closedBall 0 1)) : ContinuousOn (auxProd f) (closedBall 0 1)` |
| `auxProd_diffContOnCl` | a95A05 | `{f : ℂ → ℂ} (hf_diff : DifferentiableOn ℂ f (ball 0 1)) (hf_cont : ContinuousOn f (closedBall 0 1)) : DiffContOnCl ℂ (auxProd f) (ball 0 1)` |
| `auxProd_differentiableOn` | a95A05 | `{f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) : DifferentiableOn ℂ (auxProd f) (ball 0 1)` |
| `auxProd_vanish_on_frontier` | a95A05 | `{f : ℂ → ℂ} (hf_cont : ContinuousOn f (closedBall 0 1)) (hf_vanish : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ z.im → f z = 0) : ∀ z ∈ frontier (ball 0 1 : Set ℂ), auxProd f z = 0` |
| `b_def` | a96J01 | `(n : ℕ) : b n = 1 - (2 : ℝ)⁻¹ ^ (n + 1)` |
| `b_eq_a_succ` | a96J01 | `(n : ℕ) : b n = a (n + 1)` |
| `b_le_one` | a96J01 | `(n : ℕ) : b n ≤ 1` |
| `ball_bounded` | a95A05 | `: Bornology.IsBounded (ball (0 : ℂ) 1)` |
| `ball_volume_recursion` | a01A04 | `(n : ℕ) (hn : 0 < n) : ∃ f : ℝ → ℝ, (∀ t, 0 ≤ f t ∧ f t ≤ 1) ∧ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).toReal = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal * ∫ t, (ballSlice t) ^ n` |
| `ball_volume_superexponential_decay` | a01A04 | `(A : ℝ) (hA : 0 < A) : Tendsto (fun n => A ^ n * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal) atTop (nhds 0)` |
| `ballSlice_integral_eq_sin_pow` | a01A04 | `(n : ℕ) (hn : 0 < n) : (∫ t, (ballSlice t) ^ n) = ∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ (n + 1)` |
| `ballSlice_integral_tendsto_zero` | a01A04 | `: Tendsto (fun n => ∫ t, (ballSlice t) ^ n) atTop (nhds 0)` |
| `ballSlice_le_one` | a01A04 | `(t : ℝ) : ballSlice t ≤ 1` |
| `ballSlice_lt_one_of_ne_zero` | a01A04 | `{t : ℝ} (ht : t ≠ 0) : ballSlice t < 1` |
| `ballSlice_nonneg` | a01A04 | `(t : ℝ) : 0 ≤ ballSlice t` |
| `banachZarecki_monotone` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) (hf_N : ∀ E ⊆ Icc (0 : ℝ) 1, volume E = 0 → volume (f '' E) = 0) : AbsolutelyContinuousOnInterval f 0 1` |
| `bounded_integral_implies_integrable` | a97J01 | `(f : ℝ → ℝ) (hf_meas : Measurable f) (c : ℝ) (hc : 0 < c) (hbound : ∀ (A : Set ℝ), MeasurableSet A → Bornology.IsBounded A → (∃ M, ∀ x ∈ A, \|f x\| ≤ M) → \|∫ x in A, f x ∂volume\| ≤ c) : Integrable f volume ∧ ∫⁻ x, ENNReal.ofReal \|f x\| ∂volume ≤ ENNReal.ofReal (2 * c)` |
| `bpm_1_1_1` | bpm-1-1-1 | `(θ p : ℝ) (hθ : θ ∈ Icc 0 (Real.pi / 2)) (hp : 0 < p ∧ p < 1) : Real.rpow (Real.cos θ) p ≤ Real.cos (p * θ)` |
| `bpm_1_1_2` | bpm-1-1-2 | `(f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Icc (0 : ℝ) 1)) (hf0 : f 0 = 0) : sSup ((fun x : ℝ => \|f x\|) '' Icc (0 : ℝ) 1) ≤ Real.sqrt (∫ x in (0 : ℝ)..1, (deriv f x) ^ 2)` |
| `bpm_1_1_2_deriv_memLp_two` | bpm-1-1-2 | `(f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Icc (0 : ℝ) 1)) : MeasureTheory.MemLp (deriv f) 2 (MeasureTheory.volume.restrict (Icc 0 1))` |
| `bpm_1_1_2_eq_integral_deriv` | bpm-1-1-2 | `(f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Icc (0 : ℝ) 1)) (hf0 : f 0 = 0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : f x = ∫ t in (0 : ℝ)..x, deriv f t` |
| `bpm_1_1_2_integral_abs_deriv_le` | bpm-1-1-2 | `(f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Icc (0 : ℝ) 1)) : ∫ x in Icc (0 : ℝ) 1, \|deriv f x\| ≤ Real.sqrt (∫ x in (0 : ℝ)..1, (deriv f x) ^ 2)` |
| `bpm_1_1_2_sSup_le_of_pointwise` | bpm-1-1-2 | `(f : ℝ → ℝ) (C : ℝ) (hpoint : ∀ x ∈ Icc (0 : ℝ) 1, \|f x\| ≤ C) : sSup ((fun x : ℝ => \|f x\|) '' Icc (0 : ℝ) 1) ≤ C` |
| `bpm_1_2_2` | bpm-1-2-2 | `(f : ℝ → ℝ) (hiv : ∀ ⦃a b : ℝ⦄, a ≤ b → a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → uIcc (f a) (f b) ⊆ f '' Icc a b) (hclosed : ∀ c : ℝ, IsClosed (Icc (0 : ℝ) 1 ∩ f ⁻¹' ({c} : Set ℝ))) : ContinuousOn f (Icc (0 : ℝ) 1)` |
| `bpm_1_3_1` | bpm-1-3-1 | `(k : ℕ) (A : Fin (k + 1) → ℝ) (hanti : Antitone A) (hnonneg : ∀ i, 0 ≤ A i) : Tendsto (fun n : ℕ => Real.rpow (∑ i, (A i) ^ n) (1 / (n : ℝ))) atTop (𝓝 (A 0))` |
| `bpm_1_3_2` | bpm-1-3-2 | `: Tendsto (fun n : ℕ => Real.rpow (((n : ℝ) ^ n) / (Nat.factorial n : ℝ)) (1 / (n : ℝ))) atTop (𝓝 (Real.exp 1))` |
| `bpm_1_4_1` | bpm-1-4-1 | `(a b : ℝ) (f : ℝ → ℝ) (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b)) (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) : f b = f a` |
| `bpm_1_5_1` | bpm-1-5-1 | `(f : ℝ → ℝ) (hcont : ContinuousOn f (Icc (0 : ℝ) 1)) (hnonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x) (hint : (∫ x in (0 : ℝ)..1, f x) = 0) : ∀ x ∈ Icc (0 : ℝ) 1, f x = 0` |
| `bpm_1_6_2` | bpm-1-6-2 | `(f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (hderiv : ∀ n x, ∃ d : ℝ, HasDerivAt (f n) d x ∧ \|d\| ≤ 1) (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Continuous g` |
| `bpm_1_7_1` | bpm-1-7-1 | `(f : ℝ → ℝ) (hbase : ∀ x ∈ Ico (-Real.pi) Real.pi, f x = x) (hperiod : ∀ (x : ℝ) (n : ℤ), f (x + 2 * (n : ℝ) * Real.pi) = f x) : (1 / Real.pi) * (∫ x in (-Real.pi)..Real.pi, f x) = 0 ∧ ∀ n : ℕ, 1 ≤ n → (1 / Real.pi) * (∫ x in (-Real.pi)..Real.pi, f x * Real.cos ((n : ℝ) * x)) = 0 ∧ (1 / Real.pi) * (∫ x in (-Real.pi)..Real.pi, f x * Real.sin ((n : ℝ) * x)) = 2 * (-1 : ℝ) ^ (n + 1) / (n : ℝ)` |
| `bpm_1_7_1_integral_id_mul_cos` | bpm-1-7-1 | `(n : ℕ) (hn : 1 ≤ n) : (∫ x in (-Real.pi)..Real.pi, x * Real.cos ((n : ℝ) * x)) = 0` |
| `bpm_1_7_1_integral_id_mul_sin` | bpm-1-7-1 | `(n : ℕ) (hn : 1 ≤ n) : (∫ x in (-Real.pi)..Real.pi, x * Real.sin ((n : ℝ) * x)) = 2 * Real.pi * (-1 : ℝ) ^ (n + 1) / (n : ℝ)` |
| `bpm_1_7_1_integral_mul_eq` | bpm-1-7-1 | `(f g : ℝ → ℝ) (hbase : ∀ x ∈ Ico (-Real.pi) Real.pi, f x = x) : (∫ x in (-Real.pi)..Real.pi, f x * g x) = ∫ x in (-Real.pi)..Real.pi, x * g x` |
| `bpm_1_8_1_cap_concave` | bpm-1-8-1 | `{δ : ℝ} (hδ : 0 < δ) : ConcaveOn ℝ (Icc (0 : ℝ) 1) (bpm_1_8_1_cap δ)` |
| `bpm_1_8_1_cap_continuous` | bpm-1-8-1 | `(δ : ℝ) : Continuous (bpm_1_8_1_cap δ)` |
| `bpm_1_8_1_cap_eq_one` | bpm-1-8-1 | `{δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) : bpm_1_8_1_cap δ x = 1` |
| `bpm_1_8_1_weighted_cap_sum_concave` | bpm-1-8-1 | `(S : Finset ℕ) (c δ : ℕ → ℝ) (hc : ∀ n ∈ S, 0 ≤ c n) (hδ : ∀ n ∈ S, 0 < δ n) : ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun x => ∑ n ∈ S, c n * bpm_1_8_1_cap (δ n) x)` |
| `bpm_1_8_1_weighted_cap_sum_continuous_zero` | bpm-1-8-1 | `(S : Finset ℕ) (c δ : ℕ → ℝ) : Continuous (fun x => ∑ n ∈ S, c n * bpm_1_8_1_cap (δ n) x) ∧ (∑ n ∈ S, c n * bpm_1_8_1_cap (δ n) 0) = 0` |
| `cantorSet_measure_zero` | a95J06 | `: volume cantorSet = 0` |
| `card_roots_le_degree` | LIB: ConstructionTargets.LemniscateComponents | `(hp : 0 < p.natDegree) : (Polynomial.roots p).toFinset.card ≤ p.natDegree` |
| `card_roots_le_degree` | a00J04 | `(hp : 0 < p.natDegree) : (Polynomial.roots p).toFinset.card ≤ p.natDegree` |
| `card_roots_le_degree` | a01A08 | `(hp : 0 < p.natDegree) : (Polynomial.roots p).toFinset.card ≤ p.natDegree` |
| `cauchy_estimate_taylor` | a96A06 | `(g : ℂ → ℂ) (hg : Differentiable ℂ g) (n : ℕ) {R : ℝ} (hR : 0 < R) {C : ℝ} (hC : ∀ z ∈ sphere (0:ℂ) R, ‖g z‖ ≤ C) : ‖iteratedDeriv n g 0 / (n.factorial : ℂ)‖ ≤ C / R ^ n` |
| `cauchy_riemann_ray_implies_const` | a92J07 | `{u v : ℝ → ℝ → ℝ} (hC1 : ContDiff ℝ 1 (Function.uncurry u) ∧ ContDiff ℝ 1 (Function.uncurry v)) (hcr1 : ∀ x y, deriv (fun x' => u x' y) x = deriv (fun y' => v x y') y) (hcr2 : ∀ x y, deriv (fun y' => u x y') y = -(deriv (fun x' => v x' y) x)) (hray : ∀ x y, v x y = 0 → 0 < u x y) : ∃ c₁ c₂ : ℝ, ∀ x y, u x y = c₁ ∧ v x y = c₂` |
| `cauchy_schwarz_bound` | a00J02 | `(f : ℝ → ℝ) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (hf_deriv_sq : IntegrableOn (fun x ↦ \|deriv f x\| ^ 2) (Icc (0 : ℝ) 1) volume) : \|∫ t in Icc (0 : ℝ) x, deriv f t ∂volume\| ≤ Real.sqrt x * Real.sqrt (∫ t in Icc (0 : ℝ) x, \|deriv f t\| ^ 2 ∂volume)` |
| `cauchyTransform_differentiableAt` | a00J05 | `{z₀ : ℂ} (hz₀ : z₀ ∉ (↑) '' K) : DifferentiableAt ℂ (cauchyTransform K) z₀` |
| `cauchyTransform_differentiableAt` | a01A11 | `(z : ℂ) (hz : z ∉ ofReal '' K) : DifferentiableAt ℂ (cauchyTransform K) z` |
| `cauchyTransform_differentiableOn` | a00J05 | `: DifferentiableOn ℂ (cauchyTransform K) ((↑) '' K)ᶜ` |
| `cauchyTransform_mul_z_tendsto` | a00J05 | `: Tendsto (fun z : ℂ => z * cauchyTransform K z) (cocompact ℂ) (𝓝 (-(volume K).toReal))` |
| `cauchyTransform_not_entire` | a01A11 | `(h_diff : ∀ z, z ∉ ofReal '' K → DifferentiableAt ℂ (cauchyTransform K) z) (h_decay : Tendsto (cauchyTransform K) (cocompact ℂ) (nhds 0)) (h_nonzero : ∃ z, z ∉ ofReal '' K ∧ cauchyTransform K z ≠ 0) : ¬ ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, z ∉ ofReal '' K → G z = cauchyTransform K z` |
| `cauchyTransform_not_extendable_to_entire` | a00J05 | `(g : ℂ → ℂ) (hg : Differentiable ℂ g) (hagree : Set.EqOn g (cauchyTransform K) ((↑) '' K)ᶜ) : False` |
| `cauchyTransform_tendsto_neg_vol` | a01A11 | `: Tendsto (fun z : ℂ => z * cauchyTransform K z) (cocompact ℂ) (nhds (↑(-(volume K).toReal) : ℂ))` |
| `chain_rule_at_zero` | a95J01 | `{f g h : ℂ → ℂ} (hg : DifferentiableAt ℂ g (h 0)) (hh : DifferentiableAt ℂ h 0) (hfgh : ∀ᶠ z in nhds 0, f z = g (h z)) : deriv f 0 = deriv g (h 0) * deriv h 0` |
| `circleAverage_poissonKernel_smul_im_eq` | LIB: ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f) {R : ℝ} {w : ℂ} (hw : w ∈ Metric.ball 0 R) : Real.circleAverage (poissonKernel 0 w • fun z : ℂ => (f z).im) 0 R = (f w).im` |
| `circleAverage_poissonKernel_smul_im_eq_upper` | LIB: ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f) (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) {R : ℝ} {w : ℂ} (hw : w ∈ Metric.ball 0 R) : (f w).im = (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..Real.pi, (poissonKernel 0 w (circleMap 0 R θ) - poissonKernel 0 w (star (circleMap 0 R θ))) * (f (circleMap 0 R θ)).im` |
| `circleIntegrable_sub_inv_of_not_on_circle` | a94J06 | `{w : ℂ} (hw : ‖w‖ ≠ 1) : CircleIntegrable (fun z => (z - w)⁻¹) 0 1` |
| `circleIntegral_inv` | a96A05 | `: ∮ (z : ℂ) in C(0, 1), z⁻¹ = 2 * Real.pi * I` |
| `circleIntegral_inv_sub_polynomial` | a96A05 | `(P : Polynomial ℂ) : ∮ (z : ℂ) in C(0, 1), (fun z => z⁻¹ - Polynomial.aeval z P) z = 2 * Real.pi * I` |
| `circleIntegral_logDeriv_eq_divisor_sum` | LIB: ConstructionTargets.Rouche | `{f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hne : ∀ z ∈ sphere c R, f z ≠ 0) : (∮ z in C(c, R), logDeriv f z) = (∑ᶠ z, (divisor f (closedBall c R) z : ℂ)) * (2 * Real.pi * I)` |
| `circleIntegral_logDeriv_eq_zero_of_analyticOnNhd_of_ne_zero` | LIB: ConstructionTargets.Rouche | `{h : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hh : AnalyticOnNhd ℂ h (closedBall c R)) (hne : ∀ z ∈ closedBall c R, h z ≠ 0) : (∮ z in C(c, R), logDeriv h z) = 0` |
| `circleIntegral_logDeriv_factorizedRational` | LIB: ConstructionTargets.Rouche | `{U : Set ℂ} (D : Function.locallyFinsuppWithin U ℤ) (hD : D.support.Finite) {c : ℂ} {R : ℝ} (hR : 0 < R) (hDb : D.support ⊆ ball c R) : (∮ z in C(c, R), logDeriv (∏ᶠ u, (· - u) ^ D u) z) = (∑ᶠ u, (D u : ℂ)) * (2 * Real.pi * I)` |
| `circleIntegral_polynomial` | a96A05 | `(P : Polynomial ℂ) : ∮ (z : ℂ) in C(0, 1), Polynomial.aeval z P = 0` |
| `circleMap_two_pi_sub` | LIB: ConstructionTargets.HerglotzRigidity | `(R θ : ℝ) : circleMap 0 R (2 * Real.pi - θ) = star (circleMap 0 R θ)` |
| `clamp01_eq_self` | LIB: ConstructionTargets.BanachZarecki | `{x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : clamp01 x = x` |
| `clamp01_mem` | LIB: ConstructionTargets.BanachZarecki | `(x : ℝ) : clamp01 x ∈ Icc (0 : ℝ) 1` |
| `common_denom_of_fg_submodule` | b96A04 | `(R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (M : Submodule R K) (hfg : M.FG) : ∃ r : R, r ≠ 0 ∧ ∀ m ∈ M, r • m ∈ Set.range (algebraMap R K)` |
| `compact_is_measurable` | LIB: ConstructionTargets.LusinN | `{K : Set ℝ} (hK : IsCompact K) : MeasurableSet K` |
| `compact_is_measurable` | a95A02 | `{K : Set ℝ} (hK : IsCompact K) : MeasurableSet K` |
| `complete_square` | a01A10 | `(x y : ℝ) : -(x : ℂ)^2 + (Complex.I * (y : ℂ) * x) = -(((x : ℂ) - Complex.I * (y : ℂ) / 2)^2) - (y : ℂ)^2 / 4` |
| `component_eq_of_subset_superlevel` | LIB: ConstructionTargets.LemniscateComponents | `(hp : 0 < p.natDegree) {x y : ↥((lemniscate p)ᶜ)} (hxsuper : componentSet x ⊆ superlevel p) (hysuper : componentSet y ⊆ superlevel p) : (x : ConnectedComponents ↥((lemniscate p)ᶜ)) = y` |
| `component_eq_of_subset_superlevel` | a00J04 | `(hp : 0 < p.natDegree) {x y : ↥((lemniscate p)ᶜ)} (hxsuper : componentSet x ⊆ superlevel p) (hysuper : componentSet y ⊆ superlevel p) : (x : ConnectedComponents ↥((lemniscate p)ᶜ)) = y` |
| `component_eq_of_subset_superlevel` | a01A08 | `(hp : 0 < p.natDegree) {x y : ↥((lemniscate p)ᶜ)} (hxsuper : componentSet x ⊆ superlevel p) (hysuper : componentSet y ⊆ superlevel p) : (x : ConnectedComponents ↥((lemniscate p)ᶜ)) = y` |
| `componentSet_connected` | LIB: ConstructionTargets.LemniscateComponents | `(x : ↥((lemniscate p)ᶜ)) : IsConnected (componentSet x)` |
| `componentSet_connected` | a00J04 | `(x : ↥((lemniscate p)ᶜ)) : IsConnected (componentSet x)` |
| `componentSet_connected` | a01A08 | `(x : ↥((lemniscate p)ᶜ)) : IsConnected (componentSet x)` |
| `componentSet_eq_of_common_point` | LIB: ConstructionTargets.LemniscateComponents | `{x y : ↥((lemniscate p)ᶜ)} {z : ℂ} (hzx : z ∈ componentSet x) (hzy : z ∈ componentSet y) : (x : ConnectedComponents ↥((lemniscate p)ᶜ)) = y` |
| `componentSet_eq_of_common_point` | a00J04 | `{x y : ↥((lemniscate p)ᶜ)} {z : ℂ} (hzx : z ∈ componentSet x) (hzy : z ∈ componentSet y) : (x : ConnectedComponents ↥((lemniscate p)ᶜ)) = y` |
| `componentSet_eq_of_common_point` | a01A08 | `{x y : ↥((lemniscate p)ᶜ)} {z : ℂ} (hzx : z ∈ componentSet x) (hzy : z ∈ componentSet y) : (x : ConnectedComponents ↥((lemniscate p)ᶜ)) = y` |
| `componentSet_frontier_subset_lemniscate` | LIB: ConstructionTargets.LemniscateComponents | `(x : ↥((lemniscate p)ᶜ)) : frontier (componentSet x) ⊆ lemniscate p` |
| `componentSet_frontier_subset_lemniscate` | a00J04 | `(x : ↥((lemniscate p)ᶜ)) : frontier (componentSet x) ⊆ lemniscate p` |
| `componentSet_frontier_subset_lemniscate` | a01A08 | `(x : ↥((lemniscate p)ᶜ)) : frontier (componentSet x) ⊆ lemniscate p` |
| `componentSet_nonempty` | LIB: ConstructionTargets.LemniscateComponents | `(x : ↥((lemniscate p)ᶜ)) : (componentSet x).Nonempty` |
| `componentSet_nonempty` | a00J04 | `(x : ↥((lemniscate p)ᶜ)) : (componentSet x).Nonempty` |
| `componentSet_nonempty` | a01A08 | `(x : ↥((lemniscate p)ᶜ)) : (componentSet x).Nonempty` |
| `componentSet_open` | LIB: ConstructionTargets.LemniscateComponents | `(x : ↥((lemniscate p)ᶜ)) : IsOpen (componentSet x)` |
| `componentSet_open` | a00J04 | `(x : ↥((lemniscate p)ᶜ)) : IsOpen (componentSet x)` |
| `componentSet_open` | a01A08 | `(x : ↥((lemniscate p)ᶜ)) : IsOpen (componentSet x)` |
| `componentSet_subset_compl` | LIB: ConstructionTargets.LemniscateComponents | `(x : ↥((lemniscate p)ᶜ)) : componentSet x ⊆ (lemniscate p)ᶜ` |
| `componentSet_subset_compl` | a00J04 | `(x : ↥((lemniscate p)ᶜ)) : componentSet x ⊆ (lemniscate p)ᶜ` |
| `componentSet_subset_compl` | a01A08 | `(x : ↥((lemniscate p)ᶜ)) : componentSet x ⊆ (lemniscate p)ᶜ` |
| `componentSet_subset_superlevel_or_sublevel` | LIB: ConstructionTargets.LemniscateComponents | `(x : ↥((lemniscate p)ᶜ)) : componentSet x ⊆ superlevel p ∨ componentSet x ⊆ sublevel p` |
| `componentSet_subset_superlevel_or_sublevel` | a00J04 | `(x : ↥((lemniscate p)ᶜ)) : componentSet x ⊆ superlevel p ∨ componentSet x ⊆ sublevel p` |
| `componentSet_subset_superlevel_or_sublevel` | a01A08 | `(x : ↥((lemniscate p)ᶜ)) : componentSet x ⊆ superlevel p ∨ componentSet x ⊆ sublevel p` |
| `composition_isometric_isomorphism` | a00J03 | `[Fact (1 ≤ p)] (e : MeasurableEquiv X X) (he : MeasurePreserving e μ μ) (he_symm : MeasurePreserving e.symm μ μ) : Function.Surjective (compMeasurePreserving e he : Lp E p μ → Lp E p μ)` |
| `composition_isometry` | a00J03 | `[Fact (1 ≤ p)] {φ : X → X} (hφ : MeasurePreserving φ μ μ) : Isometry (compMeasurePreserving φ hφ : Lp E p μ → Lp E p μ)` |
| `conditionN_on_cantor_of_fix` | a95J06 | `{f : ℝ → ℝ} (hf_fix : ∀ x ∈ cantorSet, f x = x) : LusinConditionN f cantorSet` |
| `conj_apply_conj_eq` | LIB: ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f) (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (z : ℂ) : star (f (star z)) = f z` |
| `conj_eq_inv_on_circle` | a94J06 | `{ζ : ℂ} (hζ : ‖ζ‖ = 1) : starRingEnd ℂ ζ = ζ⁻¹` |
| `connected_iff_ladderConnected` | t94J01 | `: IsPreconnected (Set.univ : Set X) ↔ LadderConnectedSpace X` |
| `connected_manifold_path_connected` | t94A05 | `(H M : Type*) [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [LocPathConnectedSpace H] [ConnectedSpace M] : PathConnectedSpace M` |
| `connected_of_ladderConnected` | t94J01 | `(h : LadderConnectedSpace X) : IsPreconnected (Set.univ : Set X)` |
| `connected_superset_meets_unit_sphere` | a95A06 | `{U : Set ℂ} (hconn : IsConnected U) (hstrict : ball (0 : ℂ) 1 ⊂ U) : ∃ z ∈ U, ‖z‖ = 1` |
| `connectedComponents_complement_lemniscate_le` | LIB: ConstructionTargets.LemniscateComponents | `(p : ℂ[X]) : Nat.card (ConnectedComponents ↥((lemniscate p)ᶜ)) ≤ p.natDegree + 1` |
| `connectedComponents_complement_lemniscate_le` | a00J04 | `: Nat.card (ConnectedComponents ↥((lemniscate p)ᶜ)) ≤ p.natDegree + 1` |
| `connectedComponents_complement_lemniscate_le` | a01A08 | `: Nat.card (ConnectedComponents ↥((lemniscate p)ᶜ)) ≤ p.natDegree + 1` |
| `constant_of_symmetric_mean_value` | a95A04 | `{f : ℝ → ℝ} (hf : IntegrableOn f (Icc (0:ℝ) 1) volume) (hsym : SymmetricMeanValue f) : f =ᵐ[volume.restrict (Icc (0:ℝ) 1)] fun _ => ∫ t in (0:ℝ)..1, f t` |
| `continuous_circleIntegral_logDeriv_roucheHomotopy` | LIB: ConstructionTargets.Rouche | `{f g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hfg : ∀ z ∈ sphere c R, ‖g z‖ < ‖f z‖) : Continuous (fun t : Set.Icc (0 : ℝ) 1 ↦ ∮ z in C(c, R), logDeriv (fun w ↦ f w + (t.1 : ℂ) * g w) z)` |
| `continuous_clamp01` | LIB: ConstructionTargets.BanachZarecki | `: Continuous clamp01` |
| `continuous_convolution_indicator` | a96J02 | `(A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) (hAfin : volume A ≠ ∞) (hBfin : volume B ≠ ∞) : Continuous ((indicator A (1 : ℝ → ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (indicator B (1 : ℝ → ℝ)))` |
| `continuous_distTo` | t94A02 | `(S : Set ℝ) : Continuous fun x : ℝ => distTo S x` |
| `continuous_folded_poisson_integrand` | LIB: ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f) (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) {R : ℝ} {w : ℂ} (hw : w ∈ Metric.ball 0 R) : Continuous (fun θ : ℝ => (poissonKernel 0 w (circleMap 0 R θ) - poissonKernel 0 w (star (circleMap 0 R θ))) * (f (circleMap 0 R θ)).im)` |
| `continuous_monotoneExtension` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1)) : Continuous (monotoneExtension f)` |
| `continuous_overlapMeasure` | a96J02 | `(A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) (hBfin : volume B ≠ ∞) : Continuous (fun x => volume (A ∩ (subtractionMap x) ⁻¹' B))` |
| `continuous_overlapSet` | a96J02 | `(A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) (hBfin : volume B ≠ ∞) : Continuous (overlapSet A B hA hB)` |
| `continuous_poissonKernel_mul_im_circle` | LIB: ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f) {R : ℝ} {w : ℂ} (hw : w ∈ Metric.ball 0 R) : Continuous (fun θ : ℝ => poissonKernel 0 w (circleMap 0 R θ) * (f (circleMap 0 R θ)).im)` |
| `continuous_sepFun` | t94A02 | `{A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B) (hdisj : Disjoint A B) : Continuous fun x : ℝ => sepFun A B x` |
| `continuous_subtractionMap` | a96J02 | `: Continuous subtractionMap` |
| `continuous_surfaceQuotient` | LIB: ConstructionTargets.Surfaces | `(orientable : Bool) (genus : ℕ) : Continuous (surfaceQuotient orientable genus)` |
| `contour_integral_eval` | a92J06 | `: (∮ z in C((0 : ℂ), 1), (2 : ℂ) / (I * (z ^ 2 + 4 * z + 1))) = Complex.ofReal (2 * π / sqrt 3)` |
| `convergesInMeasure.exists_subseq_ae_tendsto` | a92J02 | `{f : ℕ → α → ℝ} {g : α → ℝ} (hcm : ConvergesInMeasure (μ` |
| `convergesInMeasure.tendstoInMeasure` | a92J02 | `{f : ℕ → α → ℝ} {g : α → ℝ} (hcm : ConvergesInMeasure (μ` |
| `convolution_aestronglyMeasurable` | LIB: ConstructionTargets.YoungConvolution | `{f g : ℝ → ℝ} (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) : AEStronglyMeasurable (convolution f g) volume` |
| `convolution_continuous` | a03J03 | `{p q : ℝ} (hpq : p.HolderConjugate q) {f : ℝ → ℝ} {g : ℝ → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal q) volume) : Continuous (fun x => ∫ y, f (x - y) * g y)` |
| `convolution_identity_counterexample` | a01A03 | `: ∃ (g : ℝ → ℝ) (h : ℝ), Integrable g volume ∧ 0 < h ∧ (∀ f : ℝ → ℝ, ContDiff ℝ ⊤ f → HasCompactSupport f → ∀ x : ℝ, (∫ t, g t * (deriv f) (x - t) ∂volume) = f (x + h) - f (x - h)) ∧ ¬(g =ᵐ[volume] fun x => if x ∈ Set.Icc (-h) h then 1 else 0)` |
| `convolution_identity_implies_indicator` | a01A03 | `(g : ℝ → ℝ) (hg1 : Integrable g volume) (h : ℝ) (hh : 0 < h) (hidentity : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ x : ℝ, (∫ t, g t * (deriv f) (x - t) ∂volume) = f (x + h) - f (x - h)) : g =ᵐ[volume] fun x => if x ∈ Set.Icc (-h) h then 1 else 0` |
| `convolution_indicator_eq_overlapReal` | a96J02 | `(A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) (x : ℝ) : ((indicator A (1 : ℝ → ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (indicator B (1 : ℝ → ℝ))) x = volume.real (A ∩ (subtractionMap x) ⁻¹' B)` |
| `convolution_integrand_integrableAE` | a95J08 | `{f g : ℝ → ℝ} {p : ℝ≥0∞} (hp : 1 < p) (hp' : p ≠ ⊤) (hf : Integrable f volume) (hg : MemLp g p volume) : ∀ᵐ x ∂volume, Integrable (fun y => f (x - y) * g y) volume` |
| `convolution_memLp` | LIB: ConstructionTargets.YoungConvolution | `{f g : ℝ → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hf : Integrable f volume) (hg : MemLp g p volume) : MemLp (convolution f g) p volume` |
| `convolution_tendsto_zero` | a03J03 | `{p q : ℝ} (hpq : p.HolderConjugate q) {f : ℝ → ℝ} {g : ℝ → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal q) volume) : Tendsto (fun x => ∫ y, f (x - y) * g y) (cocompact ℝ) (nhds 0)` |
| `countable_ordConnectedSection_of_isOpen` | LIB: ConstructionTargets.LusinN | `{U : Set ℝ} (hU : IsOpen U) : (ordConnectedSection U).Countable` |
| `countable_ordConnectedSection_of_isOpen` | a95A02 | `{U : Set ℝ} (hU : IsOpen U) : (ordConnectedSection U).Countable` |
| `counterexample_from_spikes` | a01J01 | `: let f : ℕ → ℝ → ℝ` |
| `damped_fresnel_boundary_norm_le` | a01A10 | `{ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 < x) : ‖(-2 * ((ε : ℂ) - I) * x)⁻¹ * cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)‖ ≤ 1 / (2 * x)` |
| `damped_fresnel_integration_by_parts` | a01A10 | `{ε a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : (∫ x in a..b, cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)) = (-2 * ((ε : ℂ) - I) * b)⁻¹ * cexp (-((ε : ℂ) - I) * (b : ℂ) ^ 2) - (-2 * ((ε : ℂ) - I) * a)⁻¹ * cexp (-((ε : ℂ) - I) * (a : ℂ) ^ 2) - ∫ x in a..b, (2 * ((ε : ℂ) - I) / (-2 * ((ε : ℂ) - I) * (x : ℂ)) ^ 2) * cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)` |
| `damped_fresnel_remainder_norm_le` | a01A10 | `{ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 < x) : ‖(2 * ((ε : ℂ) - I) / (-2 * ((ε : ℂ) - I) * (x : ℂ)) ^ 2) * cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)‖ ≤ 1 / (2 * x ^ 2)` |
| `dense_compl_of_interior_empty` | a95A01 | `(K : Set ℝ) (hK_int : interior K = ∅) : Dense Kᶜ` |
| `deriv_eq_zero_of_factorization` | a94A10 | `(f : ℂ → ℂ) (x₀ : ℂ) (n : ℕ) (hn : 2 ≤ n) (g : ℂ → ℂ) (hg : AnalyticAt ℂ g x₀) (hg_eq : ∀ᶠ z in 𝓝 x₀, f z - f x₀ = (z - x₀)^n * g z) : deriv f x₀ = 0` |
| `deriv_ne_zero_of_injOn` | LIB: ConstructionTargets.UnivalentDeriv | `{U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hinj : InjOn g U) {z : ℂ} (hz : z ∈ U) : deriv g z ≠ 0` |
| `deriv_ne_zero_on_reals` | a94A10 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f) (hreal : RealIffReal f) : ∀ x : ℝ, deriv f (↑x) ≠ 0` |
| `deriv_norm_le_norm` | a93J06 | `{f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1)) (hf'0 : deriv f 0 = 0) (hbound : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖deriv f z‖ ≤ 1) : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖deriv f z‖ ≤ ‖z‖` |
| `deriv_norm_le_sup_div_radius` | a01A07 | `{g : ℂ → ℂ} {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hg : DifferentiableOn ℂ g (closedBall z₀ ρ)) {M : ℝ} (hM : ∀ w ∈ closedBall z₀ ρ, ‖g w‖ ≤ M) : ‖deriv g z₀‖ ≤ M / ρ` |
| `deriv_sum_of_monotone` | a01J03 | `(f : ℝ → ℝ) (fns : ℕ → ℝ → ℝ) (hmono : ∀ n, Monotone (fns n)) (hsummable : ∀ x, Summable fun n => fns n x) (hf : ∀ x, f x = pointwiseSum fns x) : ∀ᵐ x ∂volume, HasDerivAt f (derivativeSum fns x) x` |
| `deriv_sum_of_monotone_ae` | a01J03 | `(f : ℝ → ℝ) (fns : ℕ → ℝ → ℝ) (hmono : ∀ n, Monotone (fns n)) (hsummable : ∀ x, Summable fun n => fns n x) (hf : ∀ x, f x = pointwiseSum fns x) : deriv f =ᵐ[volume] derivativeSum fns` |
| `diffContOnCl_aeval` | LIB: ConstructionTargets.LemniscateComponents | `(p : ℂ[X]) (U : Set ℂ) : DiffContOnCl ℂ (fun z : ℂ => aeval z p) U` |
| `diffContOnCl_aeval` | a00J04 | `(p : ℂ[X]) (U : Set ℂ) : DiffContOnCl ℂ (fun z : ℂ => aeval z p) U` |
| `diffContOnCl_aeval` | a01A08 | `(p : ℂ[X]) (U : Set ℂ) : DiffContOnCl ℂ (fun z : ℂ => aeval z p) U` |
| `differentiable_image_null_of_null` | a03J02 | `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : MeasureTheory.Measure E} [μ.IsAddHaarMeasure] {f : E → E} (hf : Differentiable ℝ f) {s : Set E} (hs : μ s = 0) : μ (f '' s) = 0` |
| `differentiableOn_of_L1_limit` | a01A07 | `{f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} (hΩ : IsOpen Ω) (hf : ∀ n, DifferentiableOn ℂ (f n) Ω) (hF : ContinuousOn F Ω) (hconv : L1ConvergesOnDisks f F Ω) : DifferentiableOn ℂ F Ω` |
| `diffQuot_implies_unifCont` | a93A01 | `{f : ℝ → ℝ} (hf : DiffQuotientCondition f) : UnifContOn01 f` |
| `dirichlet_integral_improper` | LIB: ConstructionTargets.Sinc | `: Filter.Tendsto (fun R : ℝ => ∫ x in Set.Icc (-R) R, Real.sinc x ∂volume) Filter.atTop (nhds π)` |
| `dirichlet_integral_improper` | a02J05 | `: Filter.Tendsto (fun R : ℝ => ∫ x in Set.Icc (-R) R, Real.sinc x ∂volume) Filter.atTop (nhds π)` |
| `disk_selfmap_deriv_one_eq_identity` | a92J04 | `{f : ℂ → ℂ} (hf_holo : DifferentiableOn ℂ f (ball (0 : ℂ) 1)) (hf_maps : ∀ z ∈ ball (0 : ℂ) 1, f z ∈ ball (0 : ℂ) 1) (hf_zero : f 0 = 0) (hf_deriv : deriv f 0 = 1) : ∀ z ∈ ball (0 : ℂ) 1, f z = z` |
| `disk_selfmap_tangent_identity` | a92J04 | `{a : ℕ → ℂ} (hconv : ∀ z ∈ ball (0 : ℂ) 1, Summable (fun n => a (n + 2) * z ^ (n + 2))) (hf_maps : ∀ z ∈ ball (0 : ℂ) 1, ‖z + ∑' n, a (n + 2) * z ^ (n + 2)‖ < 1) : ∀ n, 2 ≤ n → a n = 0` |
| `disk_selfmap_tangent_identity` | a92J04 | `' (f : ℂ → ℂ) (hf_holo : DifferentiableOn ℂ f (ball (0 : ℂ) 1)) (hf_maps : ∀ z ∈ ball (0 : ℂ) 1, f z ∈ ball (0 : ℂ) 1) (hf_zero : f 0 = 0) (hf_deriv : deriv f 0 = 1) : ∀ z ∈ ball (0 : ℂ) 1, f z = z` |
| `distribution_polynomial_decay` | a01A06 | `{g : ℝ → ℝ} {A : ℝ} (hg : OrliczBound g A) (hA : 0 < A) : ∃ C : ℝ, 0 < C ∧ ∀ (lam : ℝ), 1 ≤ lam → μ {x ∈ Icc (0 : ℝ) 1 \| lam < g x} ≤ ENNReal.ofReal (C / lam)` |
| `distTo_add_pos` | t94A02 | `{A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B) (hdisj : Disjoint A B) (x : ℝ) : 0 < distTo A x + distTo B x` |
| `distTo_eq_zero_iff` | t94A02 | `{S : Set ℝ} (hS : IsClosed S) (x : ℝ) : distTo S x = 0 ↔ x ∈ S` |
| `distTo_nonneg` | t94A02 | `(S : Set ℝ) (x : ℝ) : 0 ≤ distTo S x` |
| `dominant_ne_zero_on_sphere` | LIB: ConstructionTargets.Rouche | `{f g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hfg : ∀ z ∈ sphere c R, ‖g z‖ < ‖f z‖) : ∀ z ∈ sphere c R, f z ≠ 0` |
| `doubly_periodic_entire_is_const` | a93J05 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f) (hper1 : ∀ z, f (z + 1) = f z) (hperi : ∀ z, f (z + I) = f z) : ∃ c : ℂ, ∀ z, f z = c` |
| `dyadic_integral_eq` | a95A04 | `{f : ℝ → ℝ} (hf : IntegrableOn f (Icc (0:ℝ) 1) volume) (hsym : SymmetricMeanValue f) (j : ℕ) (k : ℕ) (hk : k < 2 ^ j) : ∫ t in ((↑k : ℝ) / 2 ^ j)..((↑(k + 1) : ℝ) / 2 ^ j), f t = (∫ t in (0:ℝ)..1, f t) / 2 ^ j` |
| `eLpNorm_indicator_rpow_eq` | a02J02 | `{α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ} (hp : 0 < p) (s : Set α) (h : α → ℝ) : eLpNorm (s.indicator h) (ENNReal.ofReal p) μ ^ p = eLpNorm (s.indicator (fun x => \|h x\| ^ p)) 1 μ` |
| `eLpNorm_tendsto_top` | a00J01 | `{f : ℝ → ℝ} (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 1))) (_hf_top : eLpNorm f ⊤ (volume.restrict (Icc 0 1)) < ⊤) : Tendsto (fun p : ℝ≥0∞ => eLpNorm f p (volume.restrict (Icc 0 1))) atTop (nhds (eLpNorm f ⊤ (volume.restrict (Icc 0 1))))` |
| `eLpNorm_top_eq_essSup` | a93J04 | `{α : Type*} {E : Type*} [NormedAddCommGroup E] [MeasurableSpace α] (f : α → E) (μ : Measure α) : eLpNorm f ⊤ μ = essSup (fun x => ‖f x‖₊ : α → ℝ≥0∞) μ` |
| `eLpNorm_translation_tendsto` | LIB: ConstructionTargets.L2Translation | `{p : ENNReal} (hp : 1 ≤ p) (hp' : p ≠ ⊤) (f : ℝ → ℝ) (hf : MemLp f p volume) : Tendsto (fun t => eLpNorm (fun x => f (x - t) - f x) p volume) (𝓝 0) (𝓝 0)` |
| `eLpNorm_translation_tendsto` | LIB: ConstructionTargets.L2Translation | `(f : ℝ → ℝ) (hf : MemLp f 2 volume) : Tendsto (fun t => eLpNorm (fun x => f (x - t) - f x) 2 volume) (𝓝 0) (𝓝 0)` |
| `entire_avoids_ray_const` | a92J07 | `{f : ℂ → ℂ} (hf : Differentiable ℂ f) (homit : ∀ z, f z ∈ slitPlane) : ∃ c : ℂ, ∀ z, f z = c` |
| `entire_coeffs_tendsto_zero` | a96A06 | `(g : ℂ → ℂ) (hg : Differentiable ℂ g) : Tendsto (fun n => iteratedDeriv n g 0 / (n.factorial : ℂ)) atTop (𝓝 0)` |
| `entire_lower_bound_is_monomial` | a95J02 | `{f : ℂ → ℂ} {lam : ℝ} (hlam : 0 < lam) (hf : Differentiable ℂ f) (hf1 : f 1 = 1) (hbound : ∀ z : ℂ, ‖z‖ ^ lam ≤ ‖f z‖) : ∃ n : ℕ, 0 < n ∧ (lam = ↑n) ∧ ∀ z, f z = z ^ n` |
| `eq_const_of_norm_le_rpow_half` | a94J08 | `(q : ℂ → ℂ) (hq_diff : Differentiable ℂ q) (hq : ∀ z : ℂ, ‖q z‖ ≤ ‖z‖ ^ ((1 : ℝ) / 2)) : ∀ z, q z = q 0` |
| `eq_deriv_mul` | LIB: ConstructionTargets.SchwarzEquality | `{h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball 0 1)) (hh_maps : MapsTo h (ball 0 1) (ball 0 1)) (hh_zero : h 0 = 0) (heq : ‖deriv h 0‖ = 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : h z = deriv h 0 * z` |
| `eq_zero_of_vanishing_on_upper_arc` | a95A05 | `{f : ℂ → ℂ} (hf_holo : DifferentiableOn ℂ f (ball 0 1)) (hf_cont : ContinuousOn f (closedBall 0 1)) (hf_vanish : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ z.im → f z = 0) : ∀ z ∈ ball (0 : ℂ) 1, f z = 0` |
| `eq_zero_on_closure_of_frontier_zero` | a95A05 | `{g : ℂ → ℂ} (hg_diff : DifferentiableOn ℂ g (ball 0 1)) (hg_cont : ContinuousOn g (closedBall 0 1)) (hg_bdy : ∀ z ∈ frontier (ball 0 1 : Set ℂ), g z = 0) : ∀ z ∈ closedBall (0 : ℂ) 1, g z = 0` |
| `eqOn_deriv_mul` | LIB: ConstructionTargets.SchwarzEquality | `{h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball 0 1)) (hh_maps : MapsTo h (ball 0 1) (ball 0 1)) (hh_zero : h 0 = 0) (heq : ‖deriv h 0‖ = 1) : EqOn h (fun z ↦ deriv h 0 * z) (ball 0 1)` |
| `eulerCharacteristic_connectedSum` | LIB: ConstructionTargets.Surfaces | `(o1 : Bool) (g1 : ℕ) (o2 : Bool) (g2 : ℕ) : eulerCharacteristic (connectedSum o1 g1 o2 g2).1 (connectedSum o1 g1 o2 g2).2 = eulerCharacteristic o1 g1 + eulerCharacteristic o2 g2 - 2` |
| `eVariationOn_intervalIntegral_le_integral_norm` | a93A04 | `{g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hg : IntervalIntegrable g volume a b) (hc : c ∈ Icc a b) : eVariationOn (fun x ↦ ∫ t in c..x, g t) (Icc a b) ≤ ENNReal.ofReal (∫ t in a..b, ‖g t‖)` |
| `even_ball_volume` | a01A04 | `(k : ℕ) (hk : 0 < k) : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * k))) 1)).toReal = Real.pi ^ k / k.factorial` |
| `even_ball_volume_exact` | a01A04 | `(k : ℕ) (hk : 0 < k) : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * k))) 1)).toReal = Real.pi ^ k / k.factorial` |
| `evenCoefficients_radius_pos` | a96J10 | `(p : FormalMultilinearSeries ℂ ℂ ℂ) (hp : 0 < p.radius) : 0 < (FormalMultilinearSeries.ofScalars ℂ (fun n => p.coeff (2 * n))).radius` |
| `evenCoefficients_sum` | a96J10 | `(h : ℂ → ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ) (hp : HasFPowerSeriesAt h p 0) (hodd : ∀ n : ℕ, Odd n → p.coeff n = 0) : ∀ᶠ w in nhds 0, (FormalMultilinearSeries.ofScalars ℂ (fun n => p.coeff (2 * n))).sum w = h (evenFactorRoot w)` |
| `evenFactorRoot_sq` | a96J10 | `(w : ℂ) : evenFactorRoot w ^ 2 = w` |
| `evenFactorRoot_tendsto` | a96J10 | `: Filter.Tendsto evenFactorRoot (nhds 0) (nhds 0)` |
| `eventually_le_norm_of_weak` | a93A03 | `{h : ℕ → H} {x : H} (hweak : WeakTendsto h x) : ∀ a : ℝ, a < ‖x‖ → ∀ᶠ n in atTop, a ≤ ‖h n‖` |
| `exists_closedBall_subset_of_mem_open` | a01A07 | `{U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U) : ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U` |
| `exists_factorization_of_order_ge_two` | a94A10 | `(f : ℂ → ℂ) (x₀ : ℂ) (hf : Differentiable ℂ f) (hord : 2 ≤ analyticOrderAt (fun z => f z - f x₀) x₀) (hne : analyticOrderAt (fun z => f z - f x₀) x₀ ≠ ⊤) : ∃ (n : ℕ) (g : ℂ → ℂ), 2 ≤ n ∧ AnalyticAt ℂ g x₀ ∧ g x₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 x₀, f z - f x₀ = (z - x₀)^n * g z` |
| `exists_local_normal_form_of_deriv_eq_zero` | LIB: ConstructionTargets.UnivalentDeriv | `{U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hinj : InjOn g U) {z : ℂ} (hz : z ∈ U) (hderiv : deriv g z = 0) : ∃ n : ℕ, 2 ≤ n ∧ ∃ F : ℂ → ℂ, AnalyticAt ℂ F z ∧ F z ≠ 0 ∧ (fun w => g w - g z) =ᶠ[𝓝 z] fun w => (w - z) ^ n * F w` |
| `exists_nonreal_preimage_of_real` | a94A10 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f) (hreal : RealIffReal f) (x₀ : ℂ) (n : ℕ) (hn : 2 ≤ n) (g : ℂ → ℂ) (hg : AnalyticAt ℂ g x₀) (hg_ne : g x₀ ≠ 0) (hg_eq : ∀ᶠ z in 𝓝 x₀, f z - f x₀ = (z - x₀)^n * g z) : ∃ z : ℂ, z.im ≠ 0 ∧ (f z).im = 0` |
| `exists_not_mem_of_dense_compl` | a95A01 | `(K : Set ℝ) (hK_int : interior K = ∅) {a b : ℝ} (hab : a < b) : ∃ x ∈ Icc a b, x ∉ K` |
| `exists_pos_measure_bounded_subset` | a96J02 | `(A : Set ℝ) (hA : MeasurableSet A) (hApos : 0 < volume A) : ∃ n : ℕ, 0 < volume (A ∩ Set.Icc (-(n : ℝ)) n)` |
| `exists_radialLaverage_bound_of_memLp` | LIB: ConstructionTargets.RadialMajorantAE | `{f : ℝ → ℝ} (hf : MemLp f 2 volume) (x : ℝ) (hx : Tendsto (radialLaverage f x) (𝓝[>] 0) (𝓝 0)) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ s, radialLaverage f x s ≤ C` |
| `exists_rat_Icc_subset_of_mem_open` | a95J06 | `{U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U) : ∃ a b : ℚ, x ∈ Icc (a : ℝ) (b : ℝ) ∧ Icc (a : ℝ) (b : ℝ) ⊆ U` |
| `exists_root_in_bounded_isOpen_sublevel_frontier_lemniscate` | LIB: ConstructionTargets.LemniscateComponents | `{U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ sublevel p) (hF : frontier U ⊆ lemniscate p) (hnonempty : U.Nonempty) : ∃ z ∈ U, aeval z p = 0` |
| `exists_root_in_bounded_isOpen_sublevel_frontier_lemniscate` | a00J04 | `{U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ sublevel p) (hF : frontier U ⊆ lemniscate p) (hnonempty : U.Nonempty) : ∃ z ∈ U, aeval z p = 0` |
| `exists_root_in_bounded_isOpen_sublevel_frontier_lemniscate` | a01A08 | `{U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ sublevel p) (hF : frontier U ⊆ lemniscate p) (hnonempty : U.Nonempty) : ∃ z ∈ U, aeval z p = 0` |
| `exists_root_in_componentSet_of_subset_sublevel` | LIB: ConstructionTargets.LemniscateComponents | `(hp : 0 < p.natDegree) (x : ↥((lemniscate p)ᶜ)) (hsub : componentSet x ⊆ sublevel p) : ∃ z ∈ componentSet x, aeval z p = 0` |
| `exists_root_in_componentSet_of_subset_sublevel` | a00J04 | `(hp : 0 < p.natDegree) (x : ↥((lemniscate p)ᶜ)) (hsub : componentSet x ⊆ sublevel p) : ∃ z ∈ componentSet x, aeval z p = 0` |
| `exists_root_in_componentSet_of_subset_sublevel` | a01A08 | `(hp : 0 < p.natDegree) (x : ↥((lemniscate p)ᶜ)) (hsub : componentSet x ⊆ sublevel p) : ∃ z ∈ componentSet x, aeval z p = 0` |
| `exists_rotation` | LIB: ConstructionTargets.SchwarzEquality | `{h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball 0 1)) (hh_maps : MapsTo h (ball 0 1) (ball 0 1)) (hh_zero : h 0 = 0) (heq : ‖deriv h 0‖ = 1) : ∃ α : ℝ, ∀ z ∈ ball (0 : ℂ) 1, h z = Complex.exp (Complex.I * (α : ℂ)) * z` |
| `exists_simultaneous_residue_of_twoSided` | b98J04 | `{R : Type*} [Ring R] (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided] (h : I ⊔ J = ⊤) (a b : R) : ∃ r : R, r - a ∈ I ∧ r - b ∈ J` |
| `exists_spike` | a96A02 | `(x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) : ∃ n : ℕ, 0 < n ∧ 1 / ((n : ℝ) + 1) < x ∧ x ≤ 1 / (n : ℝ)` |
| `exists_spikeWidth_lt` | a01J01 | `{δ : ℝ} (hδ : 0 < δ) : ∃ n : ℕ, spikeWidth n < δ` |
| `exists_tendsto_integral_fresnel` | a01A10 | `: ∃ L : ℂ, Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, cexp (I * (x : ℂ) ^ 2)) Filter.atTop (nhds L)` |
| `exists_tendsto_integral_sinc` | LIB: ConstructionTargets.Sinc | `: ∃ L : ℝ, Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sinc x) Filter.atTop (nhds L)` |
| `exists_tendsto_symmetric_integral_sinc` | LIB: ConstructionTargets.Sinc | `: ∃ L : ℝ, Filter.Tendsto (fun R : ℝ => ∫ x in Set.Icc (-R) R, Real.sinc x ∂volume) Filter.atTop (nhds L)` |
| `exists_unit_mul` | LIB: ConstructionTargets.SchwarzEquality | `{h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball 0 1)) (hh_maps : MapsTo h (ball 0 1) (ball 0 1)) (hh_zero : h 0 = 0) (heq : ‖deriv h 0‖ = 1) : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ ball (0 : ℂ) 1, h z = c * z` |
| `exists_zeroFree_factorization_on_closedBall` | LIB: ConstructionTargets.Rouche | `{f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hne : ∀ z ∈ sphere c R, f z ≠ 0) : ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall c R) ∧ (∀ z : closedBall c R, h z ≠ 0) ∧ f =ᶠ[codiscreteWithin (closedBall c R)] (∏ᶠ u, (· - u) ^ divisor f (closedBall c R) u) * h` |
| `exp_two_pi_mul_sub_ne_zero_of_norm_lt_one` | a96J10 | `{z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) : Complex.exp (2 * (Real.pi : ℂ) * z) - 1 ≠ 0` |
| `exponential_decay_implies_L2` | a01A06 | `{g : ℝ → ℝ} (hg_meas : Measurable g) (hg_nn : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ g x) (hg_int : IntegrableOn g (Icc (0 : ℝ) 1) volume) {C α : ℝ} (hC : 0 < C) (hα : 0 < α) (hdecay : ∀ (lam : ℝ), 0 ≤ lam → μ {x ∈ Icc (0 : ℝ) 1 \| lam < g x} ≤ ENNReal.ofReal (C * Real.exp (-α * lam))) : IntegrableOn (fun x => g x ^ 2) (Icc (0 : ℝ) 1) volume` |
| `extension_deriv_eq_lacunary_deriv_series` | a95A06 | `{F : ℂ → ℂ} {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (hF_eq : ∀ z ∈ ball (0 : ℂ) 1, F z = lacunarySeries z) : deriv F w = ∑' n : ℕ, w ^ (n.factorial - 1)` |
| `extension_deriv_eventually_bounded` | a95A06 | `{U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {z : ℂ} (hz : z ∈ U) : ∀ᶠ w in 𝓝 z, ‖deriv F w‖ < ‖deriv F z‖ + 1` |
| `exterior_pathConnected` | LIB: ConstructionTargets.LemniscateComponents | `(R : ℝ) (hR : 0 ≤ R) : IsPathConnected {z : ℂ \| R < ‖z‖}` |
| `exterior_pathConnected` | a00J04 | `(R : ℝ) (hR : 0 ≤ R) : IsPathConnected {z : ℂ \| R < ‖z‖}` |
| `exterior_pathConnected` | a01A08 | `(R : ℝ) (hR : 0 ≤ R) : IsPathConnected {z : ℂ \| R < ‖z‖}` |
| `f_continuous` | a96J01 | `(n : ℕ) : Continuous (f n)` |
| `f_eq_zero_of_ne` | a96J01 | `{n m : ℕ} {x : ℝ} (hmn : m ≠ n) (hn : 0 < f n x) : f m x = 0` |
| `f_le` | a96J01 | `(n : ℕ) (x : ℝ) : f n x ≤ 1 / ((n + 1 : ℕ) : ℝ)` |
| `f_mid` | a96J01 | `(n : ℕ) : f n (mid n) = 1 / ((n + 1 : ℕ) : ℝ)` |
| `f_nonneg` | a96J01 | `(n : ℕ) (x : ℝ) : 0 ≤ f n x` |
| `f_nonzero_unique` | a96J01 | `{n : ℕ} {x : ℝ} (hn : f n x ≠ 0) : ∀ m, m ≠ n → f m x = 0` |
| `f_poly_exp_deriv_ne_zero` | a94J07 | `{z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) : deriv f_poly_exp z ≠ 0` |
| `f_poly_exp_injective_on_disk` | a94J07 | `: Set.InjOn f_poly_exp (ball (0 : ℂ) 1)` |
| `f_pos_imp` | a96J01 | `(n : ℕ) {x : ℝ} (hfx : 0 < f n x) : a n < x ∧ x < b n` |
| `f_radial_conv_L2_bound` | a95A03 | `{g : E → ℝ} (hg : MemLp g 2 volume) : eLpNorm (fun x => ∫ y, f_radial (x - y) * g y ∂volume) 2 volume ≤ ENNReal.ofReal (2 * π ^ 2) * eLpNorm g 2 volume` |
| `f_radial_eq_of_ne_zero` | a95A03 | `(x : E) (hx : x ≠ 0) : f_radial x = ‖x‖⁻¹ ^ 2 * (1 + ‖x‖ ^ 2)⁻¹` |
| `f_radial_integrable` | a95A03 | `: Integrable f_radial volume` |
| `f_radial_integral` | a95A03 | `: ∫ x : E, f_radial x ∂volume = 2 * π ^ 2` |
| `f_radial_memLp_iff` | a95A03 | `{p : ℝ} (hp : 0 < p) : MemLp f_radial (ENNReal.ofReal p) (volume : Measure E) ↔ 3/4 < p ∧ p < 3/2` |
| `f_radial_not_memLp_top` | a95A03 | `: ¬ MemLp f_radial ⊤ (volume : Measure E)` |
| `f_summable` | a96J01 | `(x : ℝ) : Summable (fun n => f n x)` |
| `f_tail_le` | a96J01 | `(N : ℕ) (x : ℝ) : ∑' k, f (k + N + 1) x ≤ 1 / ((N + 2 : ℕ) : ℝ)` |
| `f_unique_pos` | a96J01 | `{n m : ℕ} {x : ℝ} (hn : 0 < f n x) (hm : 0 < f m x) : n = m` |
| `f_zero_eq_zero` | a95J02 | `{f : ℂ → ℂ} {lam : ℝ} (hlam : 0 < lam) (hf : Differentiable ℂ f) (hf1 : f 1 = 1) (hbound : ∀ z : ℂ, ‖z‖ ^ lam ≤ ‖f z‖) : f 0 = 0` |
| `factorial_dvd_of_le` | a95A06 | `{n q : ℕ} (hq : 0 < q) (hn : q ≤ n) : q ∣ n.factorial` |
| `false_of_affine_factorization` | a94A10 | `(f : ℂ → ℂ) (hreal : RealIffReal f) (x₀ : ℂ) (n : ℕ) (hn : 2 ≤ n) (g : ℂ → ℂ) (hg : AnalyticAt ℂ g x₀) (hg_eq : ∀ᶠ z in 𝓝 x₀, f z - f x₀ = (z - x₀)^n * g z) (haffine : ∃ a b : ℂ, ∀ z, f z = a * z + b) : False` |
| `false_of_entire_nonvanishing_lower_bound` | a94J08 | `(f : ℂ → ℂ) (hf_diff : Differentiable ℂ f) (hf_ne : ∀ z, f z ≠ 0) (hbound : ∀ z : ℂ, ‖z‖ ^ ((3 : ℝ) / 2) ≤ ‖f z‖) : False` |
| `finrank_E_eq_three` | a95A03 | `: finrank ℝ E = 3` |
| `fourier_maps_L1_to_C0` | a92J03 | `{f : ℝ → ℂ} (hf : Integrable f volume) : Continuous (fourierTransform f) ∧ (∀ ξ, ‖fourierTransform f ξ‖ ≤ ∫ x, ‖f x‖ ∂volume) ∧ Tendsto (fourierTransform f) (cocompact ℝ) (𝓝 0)` |
| `fourierTransform_continuous` | a92J03 | `{f : ℝ → ℂ} (hf : Integrable f volume) : Continuous (fourierTransform f)` |
| `fourierTransform_norm_le` | a92J03 | `{f : ℝ → ℂ} (hf : Integrable f volume) (ξ : ℝ) : ‖fourierTransform f ξ‖ ≤ ∫ x, ‖f x‖ ∂volume` |
| `fourierTransform_tendsto_zero` | a92J03 | `{f : ℝ → ℂ} (hf : Integrable f volume) : Tendsto (fourierTransform f) (cocompact ℝ) (𝓝 0)` |
| `fraction_surjective_of_free_embedding` | b96A04 | `(R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (F : Type) [AddCommGroup F] [Module R F] [Module.Free R F] (i : K →ₗ[R] F) (hi : Function.Injective i) : Function.Surjective (algebraMap R K)` |
| `fresnel_bochner_integral_eq_zero` | a01A10 | `: (∫ x in Set.Ioi (0 : ℝ), cexp (Complex.I * (x : ℂ)^2)) = 0` |
| `fresnel_claimed_value_ne_zero` | a01A10 | `: (1 + Complex.I) * (√π) / (2 * (√2)) ≠ 0` |
| `fresnel_integral` | a01A10 | `: Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, cexp (Complex.I * (x : ℂ)^2)) Filter.atTop (nhds ((1 + Complex.I) * (√π) / (2 * (√2))))` |
| `fresnel_integrand_not_integrable` | a01A10 | `: ¬ IntegrableOn (fun x : ℝ => cexp (Complex.I * (x : ℂ)^2)) (Set.Ioi 0)` |
| `fresnel_remainder_norm_eq` | a01A10 | `{x : ℝ} (hx : 0 < x) : ‖(2 * ((0 : ℂ) - I) / (-2 * ((0 : ℂ) - I) * (x : ℂ)) ^ 2) * cexp (-((0 : ℂ) - I) * (x : ℂ) ^ 2)‖ = 1 / (2 * x ^ 2)` |
| `frontier_connectedComponentIn_subset_frontier` | LIB: ConstructionTargets.LemniscateComponents | `{α : Type*} [TopologicalSpace α] [LocallyConnectedSpace α] {U : Set α} (hU : IsOpen U) {x : α} (hx : x ∈ U) : frontier (connectedComponentIn U x) ⊆ frontier U` |
| `ftc_a00j02` | a00J02 | `(f : ℝ → ℝ) (hf_ac : AbsolutelyContinuousOnInterval f 0 1) (hf_zero : f 0 = 0) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : f x = ∫ t in (0)..x, deriv f t` |
| `G_zero` | a94A06 | `: G 0 = -(Real.sqrt 3 * π) / 72` |
| `gamma_half_nat_lower` | a01A04 | `(k : ℕ) : (k.factorial : ℝ) * Real.sqrt Real.pi / 2 ≤ Real.Gamma ((k : ℝ) + 3 / 2)` |
| `gaussConv_eq_integral_unitKernel` | a94A03 | `{t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) (x : ℝ) : gaussConv t f x = ∫ z, gaussKernel 1 z * f (x - t * z) ∂volume` |
| `gaussConv_Lp_contraction` | a94A03 | `{p : ENNReal} (hp : 1 ≤ p) (hp' : p ≠ ⊤) {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : MemLp f p volume) : eLpNorm (gaussConv t f) p volume ≤ eLpNorm f p volume` |
| `gaussConv_memLp` | a94A03 | `{p : ENNReal} (hp : 1 ≤ p) (hp' : p ≠ ⊤) {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : MemLp f p volume) : MemLp (gaussConv t f) p volume` |
| `gaussConv_tendsto_Lp` | a94A03 | `{p : ENNReal} (hp : 1 ≤ p) (hp' : p ≠ ⊤) {f : ℝ → ℝ} (hf : MemLp f p volume) : Tendsto (fun t => eLpNorm (fun x => gaussConv t f x - f x) p volume) (𝓝[>] 0) (𝓝 0)` |
| `gaussian_fourier_transform` | a01A10 | `(y : ℝ) : ∫ x : ℝ, cexp ((Complex.I * ↑y * ↑x) + (-(↑x : ℂ)^2)) = ↑(√π) * cexp (-(↑y : ℂ)^2 / 4)` |
| `gaussian_translation_average_tendsto_Lp` | a94A03 | `{p : ENNReal} [Fact (1 ≤ p)] (hp' : p ≠ ⊤) {f : ℝ → ℝ} (hf : MemLp f p volume) : let τ : ℝ → C(ℝ, ℝ)` |
| `gaussian_translation_average_toLp` | a94A03 | `{p : ENNReal} [Fact (1 ≤ p)] (hp' : p ≠ ⊤) {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : MemLp f p volume) : let τ : ℝ → C(ℝ, ℝ)` |
| `gaussKernel_integrable` | a94A03 | `{t : ℝ} (ht : 0 < t) : Integrable (gaussKernel t) volume` |
| `gaussKernel_integral_eq_one` | a94A03 | `{t : ℝ} (ht : 0 < t) : ∫ x, gaussKernel t x ∂volume = 1` |
| `gaussKernel_neg` | a94A03 | `(t x : ℝ) : gaussKernel t (-x) = gaussKernel t x` |
| `gaussKernel_nonneg` | a94A03 | `{t : ℝ} (ht : 0 < t) (x : ℝ) : 0 ≤ gaussKernel t x` |
| `gaussKernel_scale` | a94A03 | `{t : ℝ} (ht : 0 < t) (x : ℝ) : t * gaussKernel t (t * x) = gaussKernel 1 x` |
| `geom_iteratedDeriv` | a96A06 | `(n : ℕ) : iteratedDeriv n (fun z : ℂ => (1 - z)⁻¹) 0 = (n.factorial : ℂ)` |
| `geom_taylor_coeff` | a96A06 | `(n : ℕ) : iteratedDeriv n (fun z : ℂ => (1 - z)⁻¹) 0 / (n.factorial : ℂ) = 1` |
| `geometric_mean_le_quasiNorm_of_integrable_log` | a96A01 | `{f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 1) volume) (hf_pos : ∀ᵐ x ∂(volume.restrict (Icc 0 1)), 0 < ‖f x‖) (hlog : IntegrableOn (fun x => log ‖f x‖) (Icc 0 1) volume) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) : exp (∫ x in Icc (0 : ℝ) 1, log ‖f x‖ ∂volume) ≤ quasiNorm f p` |
| `grid_count_converges_to_measure` | a97J02 | `(A : Set ℝ) (hA_closed : IsClosed A) (hA_subset : A ⊆ Icc 0 1) : Tendsto (fun N : ℕ ↦ (b A N : ℝ) / N) atTop (𝓝 (volume A).toReal)` |
| `hasDerivAt_argStar_comp` | a02J07 | `{γ : ℝ → ℂ} (hγ : SlitPath γ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt (fun s => argStar (γ s)) (deriv γ t / γ t).im t` |
| `hasDerivAt_cauchyKernel` | a01A11 | `(t : ℝ) (z : ℂ) (hz : (t : ℂ) ≠ z) : HasDerivAt (fun w : ℂ ↦ (1 : ℂ) / ((t : ℂ) - w)) (((t : ℂ) - z)⁻¹ ^ 2) z` |
| `hasDerivAt_G` | a94A06 | `(x : ℝ) : HasDerivAt G (x^7 / (1 + x^12)) x` |
| `hasDerivAt_H` | a94A06 | `(u : ℝ) (hu : 0 ≤ u) : HasDerivAt H (u / (1 + u^3)) u` |
| `hasDerivAt_integral_iterate_heatKernel` | a96A04 | `{t : ℝ} (ht : 0 < t) (n : ℕ) {f : ℝ → ℝ} (hf : MemLp f 2 volume) (x₀ : ℝ) : HasDerivAt (fun x => ∫ y, (deriv^[n] (heatKernel t)) (x - y) * f y ∂volume) (∫ y, (deriv^[n + 1] (heatKernel t)) (x₀ - y) * f y ∂volume) x₀` |
| `hasDerivAt_integrand` | a00J05 | `(t : ℝ) (z₀ : ℂ) (hz : (t : ℂ) ≠ z₀) : HasDerivAt (fun w : ℂ => ((t : ℂ) - w)⁻¹) (((t : ℂ) - z₀)⁻¹ ^ 2) z₀` |
| `hasDerivAt_logStar` | a02J07 | `{z : ℂ} (hz : z ∈ posSlitPlane) : HasDerivAt logStar z⁻¹ z` |
| `hasDerivAt_logStar_comp` | a02J07 | `{γ : ℝ → ℂ} (hγ : SlitPath γ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt (fun s => logStar (γ s)) (deriv γ t / γ t) t` |
| `hasFiniteIntegral_indicator_lift` | LIB: ConstructionTargets.LpRepresentative | `{Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X] {ν : Measure Y} {μ : Measure X} [SFinite ν] [SFinite μ] {p : ENNReal} [Fact (1 ≤ p)] {φ : Y × X → ℝ} (hφ : AEStronglyMeasurable φ (ν.prod μ)) {F : Y → Lp ℝ p μ} (hF : Integrable F ν) (hFφ : ∀ᵐ y ∂ν, (F y : X → ℝ) =ᵐ[μ] fun x => φ (y, x)) (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) : HasFiniteIntegral (fun z : Y × X => s.indicator (fun x => φ (z.1, x)) z.2) (ν.prod μ)` |
| `heat_translation_average_tendsto_L2` | a96A04 | `{f : ℝ → ℝ} (hf : MemLp f 2 volume) : let τ : ℝ → C(ℝ, ℝ)` |
| `heat_translation_average_toLp` | a96A04 | `{t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : MemLp f 2 volume) : let τ : ℝ → C(ℝ, ℝ)` |
| `heatConv_contDiff` | a96A04 | `{t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : MemLp f 2 volume) : ContDiff ℝ ∞ (heatConv t f)` |
| `heatConv_eq_integral_translation` | a96A04 | `(t : ℝ) (f : ℝ → ℝ) (x : ℝ) : heatConv t f x = ∫ y, heatKernel t y * f (x - y) ∂volume` |
| `heatConv_eq_integral_unitKernel` | a96A04 | `{t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) (x : ℝ) : heatConv t f x = ∫ z, heatKernel 1 z * f (x - Real.sqrt t * z) ∂volume` |
| `heatConv_L2_le` | a96A04 | `{t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : MemLp f 2 volume) : eLpNorm (heatConv t f) 2 volume ≤ eLpNorm f 2 volume` |
| `heatConv_memLp` | a96A04 | `{t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : MemLp f 2 volume) : MemLp (heatConv t f) 2 volume` |
| `heatConv_tendsto_L2` | a96A04 | `{f : ℝ → ℝ} (hf : MemLp f 2 volume) : Tendsto (fun t => eLpNorm (fun x => heatConv t f x - f x) 2 volume) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)` |
| `heatKernel_contDiff` | a96A04 | `{t : ℝ} (_ht : 0 < t) : ContDiff ℝ ∞ (heatKernel t)` |
| `heatKernel_deriv` | a96A04 | `{t x : ℝ} (ht : 0 < t) : deriv (heatKernel t) x = -(x / (2 * t)) * heatKernel t x` |
| `heatKernel_deriv_integrable` | a96A04 | `{t : ℝ} (ht : 0 < t) : Integrable (fun x => -(x / (2 * t)) * heatKernel t x) volume` |
| `heatKernel_deriv_memLp_two` | a96A04 | `{t : ℝ} (ht : 0 < t) : MemLp (fun x => -(x / (2 * t)) * heatKernel t x) 2 volume` |
| `heatKernel_deriv_mul_integrable` | a96A04 | `{t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : MemLp f 2 volume) (x : ℝ) : Integrable (fun y => (-((x - y) / (2 * t)) * heatKernel t (x - y)) * f y) volume` |
| `heatKernel_hasDerivAt` | a96A04 | `{t x : ℝ} (_ht : 0 < t) : HasDerivAt (heatKernel t) (-(x / (2 * t)) * heatKernel t x) x` |
| `heatKernel_integrable` | a96A04 | `{t : ℝ} (ht : 0 < t) : Integrable (heatKernel t) volume` |
| `heatKernel_integral` | a96A04 | `{t : ℝ} (ht : 0 < t) : ∫ x : ℝ, heatKernel t x ∂volume = 1` |
| `heatKernel_iterate_deriv_eq_polynomial_gaussian` | a96A04 | `{t : ℝ} (_ht : 0 < t) (n : ℕ) (x : ℝ) : deriv^[n] (heatKernel t) x = (heatKernelDerivPoly t n).eval x * Real.exp (-x ^ 2 / (4 * t))` |
| `heatKernel_iterate_deriv_local_envelope` | a96A04 | `{t : ℝ} (ht : 0 < t) (n : ℕ) (x₀ : ℝ) {f : ℝ → ℝ} (hf : MemLp f 2 volume) : ∃ bound : ℝ → ℝ, Integrable bound volume ∧ ∀ y, ∀ x ∈ Metric.ball x₀ 1, ‖(deriv^[n] (heatKernel t)) (x - y) * f y‖ ≤ bound y` |
| `heatKernel_iterate_deriv_memLp_two` | a96A04 | `{t : ℝ} (ht : 0 < t) (n : ℕ) : MemLp (deriv^[n] (heatKernel t)) 2 volume` |
| `heatKernel_iterate_deriv_polynomial_bound` | a96A04 | `{t : ℝ} (ht : 0 < t) (n : ℕ) : ∃ P : Polynomial ℝ, (∀ i, 0 ≤ P.coeff i) ∧ ∀ u, \|deriv^[n] (heatKernel t) u\| ≤ P.eval \|u\| * Real.exp (-u ^ 2 / (4 * t))` |
| `heatKernel_memLp_two` | a96A04 | `{t : ℝ} (ht : 0 < t) : MemLp (heatKernel t) 2 volume` |
| `heatKernel_nonneg` | a96A04 | `{t : ℝ} (ht : 0 < t) (x : ℝ) : 0 ≤ heatKernel t x` |
| `heatKernel_scale` | a96A04 | `{t : ℝ} (ht : 0 < t) (x : ℝ) : Real.sqrt t * heatKernel t (Real.sqrt t * x) = heatKernel 1 x` |
| `holder_from_sq` | a96A02 | `{z d : ℝ} (hz : 0 ≤ z) (_hd : 0 ≤ d) (h : z ^ 2 ≤ 4 * d) : z ≤ 2 * d ^ ((1 : ℝ) / 2)` |
| `holder_to_left` | a96A02 | `{f : ℝ → ℝ} (hf : SpikeFunctionSpec f) (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : x ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) : \|f x\| ≤ 2 * (x - 1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 2)` |
| `holder_to_right` | a96A02 | `{f : ℝ → ℝ} (hf : SpikeFunctionSpec f) (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : x ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) : \|f x\| ≤ 2 * (1 / (n : ℝ) - x) ^ ((1 : ℝ) / 2)` |
| `holder_within_spike` | a96A02 | `{f : ℝ → ℝ} (hf : SpikeFunctionSpec f) (n : ℕ) (hn : 0 < n) {x y : ℝ} (hx : x ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) (hy : y ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) : \|f x - f y\| ^ 2 ≤ 4 * \|x - y\|` |
| `homeomorph_of_compact_to_T2` | t92J02 | `{X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {f : X → Y} (hcompact : IsCompact (Set.univ : Set X)) (hf : Continuous f) (hbij : Function.Bijective f) : ∃ h : X ≃ₜ Y, h.toContinuousMap = ⟨f, hf⟩` |
| `hw_eq` | a96J01 | `(n : ℕ) : hw n = (2 : ℝ)⁻¹ ^ (n + 2)` |
| `hw_pos` | a96J01 | `(n : ℕ) : 0 < hw n` |
| `im_apply_star_eq_neg` | LIB: ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f) (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (z : ℂ) : (f (star z)).im = -(f z).im` |
| `im_image_mul_pos_of_im_pos` | a94A10 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f) (hreal : RealIffReal f) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) : 0 < (f z).im * (f w).im` |
| `im_linear_growth_of_entire_pick` | LIB: ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f) (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (hpos : ∀ z : ℂ, 0 < z.im → 0 < (f z).im) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, \|(f z).im\| ≤ C * (1 + ‖z‖)` |
| `im_neg_of_im_neg` | LIB: ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f) (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (hpos : ∀ z : ℂ, 0 < z.im → 0 < (f z).im) {z : ℂ} (hz : z.im < 0) : (f z).im < 0` |
| `image_Icc_eq_Icc` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b) : f '' Icc a b = Icc (f a) (f b)` |
| `image_of_compact_isCompact` | t92J02 | `{X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {K : Set X} {f : X → Y} (hK : IsCompact K) (hf : Continuous f) : IsCompact (f '' K)` |
| `indicator_bound` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ) (hφ : ∀ (a b : ℝ), a < b → \|∫ x in Set.Icc a b, φ x\| ≤ M * (b - a) / (1 + (b - a))) (a b : ℝ) (hab : a < b) (k : ℝ) (hk : 0 < k) : \|scaledIntOp φ (Set.indicator (Set.Icc a b) (fun _ => 1)) k\| ≤ M * (b - a) / (1 + k * (b - a))` |
| `indicator_case` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ) (hM : 0 < M) (hφ : ∀ (a b : ℝ), a < b → \|∫ x in Set.Icc a b, φ x\| ≤ M * (b - a) / (1 + (b - a))) (a b : ℝ) (hab : a < b) : Tendsto (fun k : ℝ => scaledIntOp φ (Set.indicator (Set.Icc a b) (fun _ => 1)) k) atTop (nhds 0)` |
| `indicator_not_riemann_integrable` | a95A01 | `(K : Set ℝ) (hK : IsCompact K) (hK_sub : K ⊆ Icc 0 1) (hK_meas : 0 < volume K) (hK_int : interior K = ∅) : lowerRiemannIntegral (K.indicator (fun _ => (1:ℝ))) < upperRiemannIntegral (K.indicator (fun _ => (1:ℝ)))` |
| `inf_indicator_eq_zero` | a95A01 | `(K : Set ℝ) (hK_int : interior K = ∅) {a b : ℝ} (hab : a < b) : sInf ((K.indicator (fun _ => (1:ℝ))) '' Icc a b) = 0` |
| `infDist_pos_of_not_mem_image` | a01A11 | `(hK' : IsCompact K) (hKne' : K.Nonempty) (z : ℂ) (hz : z ∉ ofReal '' K) : 0 < infDist z (ofReal '' K)` |
| `inflate5_center` | a95J07 | `(α β : ℝ) (_hab : α < β) : (3 * α - 2 * β + (3 * β - 2 * α)) / 2 = (α + β) / 2` |
| `inflate5_length` | a95J07 | `(α β : ℝ) (_hab : α < β) : (3 * β - 2 * α) - (3 * α - 2 * β) = 5 * (β - α)` |
| `intCast_zeroCountInClosedBall` | LIB: ConstructionTargets.Rouche | `(f : ℂ → ℂ) (c : ℂ) (R : ℝ) : (zeroCountInClosedBall f c R : ℂ) = ∑ᶠ z, (divisor f (closedBall c R) z : ℂ)` |
| `integrable_convolution_at` | a03J03 | `{p q : ℝ} (hpq : p.HolderConjugate q) {f : ℝ → ℝ} {g : ℝ → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal q) volume) (x : ℝ) : Integrable (fun y => f (x - y) * g y) volume` |
| `integrable_damped_cos_prod` | LIB: ConstructionTargets.Sinc | `{a : ℝ} (ha : 0 < a) : Integrable (Function.uncurry fun t x : ℝ => Real.exp (-a * x) * Real.cos (t * x)) ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioi (0 : ℝ))))` |
| `integrable_indicator_of_finite_measure` | a96J02 | `(s : Set ℝ) (hs : MeasurableSet s) (hsfin : volume s < ⊤) : Integrable (indicator s (1 : ℝ → ℝ)) volume` |
| `integrable_iterate_deriv_standardGaussian` | a96A04 | `(n : ℕ) : Integrable (deriv^[n] (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))) volume` |
| `integrable_kernel_smul_of_norm_le` | LIB: ConstructionTargets.KernelAverage | `{Y E : Type*} [MeasurableSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E] {ν : Measure Y} {k : Y → ℝ} {F : Y → E} (hk : Integrable k ν) (hF : AEStronglyMeasurable F ν) {C : ℝ} (hC : ∀ᵐ y ∂ν, ‖F y‖ ≤ C) : Integrable (fun y ↦ k y • F y) ν` |
| `integrable_polynomial_mul_exp_neg_mul_sq` | a96A04 | `(p : Polynomial ℝ) {b : ℝ} (hb : 0 < b) : Integrable (fun x : ℝ => p.eval x * Real.exp (-b * x ^ 2)) volume` |
| `integrable_posPart_log_norm` | a96A01 | `{f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 1) volume) : Integrable (fun x => (log ‖f x‖)⁺) (volume.restrict (Icc 0 1))` |
| `integrable_pow_mul_exp_neg_mul_sq` | a96A04 | `(n : ℕ) {b : ℝ} (hb : 0 < b) : Integrable (fun x : ℝ => x ^ n * Real.exp (-b * x ^ 2)) volume` |
| `integrable_radial_R3_iff` | LIB: ConstructionTargets.RadialIntegrationR3 | `{g : ℝ → ℝ} : Integrable (fun x : E => g ‖x‖) volume ↔ IntegrableOn (fun r : ℝ => r ^ 2 * g r) (Ioi 0)` |
| `integrableOn_exp_neg_mul_sinc_Ioi` | LIB: ConstructionTargets.Sinc | `{a : ℝ} (ha : 0 < a) : IntegrableOn (fun x : ℝ => Real.exp (-a * x) * Real.sinc x) (Set.Ioi (0 : ℝ))` |
| `integral_abs_rpow_eq_eLpNorm_rpow` | a02J02 | `{α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ} (hp : 0 < p) {h : α → ℝ} (hh : MemLp h (ENNReal.ofReal p) μ) : (∫ x, \|h x\| ^ p ∂μ) = (eLpNorm h (ENNReal.ofReal p) μ).toReal ^ p` |
| `integral_arctan_tendsto_of_tendstoInMeasure` | a95J05 | `{f : ℕ → Ω → ℝ} (hf : ∀ n, Measurable (f n)) (hconv : TendstoInMeasureZero f μ) : Tendsto (fun n => ∫ x, \|arctan (f n x)\| ∂μ) atTop (𝓝 0)` |
| `integral_closedBall_eq_area_smul` | a01A07 | `{g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hg : DifferentiableOn ℂ g (closedBall z₀ r)) : ∫ w in closedBall z₀ r, g w = (Real.pi * r ^ 2 : ℝ) • g z₀` |
| `integral_closedBall_eq_translate` | a01A07 | `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (q : ℂ → E) (z₀ : ℂ) (r : ℝ) : ∫ w in closedBall z₀ r, q w = ∫ w in closedBall (0 : ℂ) r, q (w + z₀)` |
| `integral_closedBall_zero_eq_area_smul` | a01A07 | `{g : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hg : DifferentiableOn ℂ g (closedBall (0 : ℂ) r)) : ∫ w in closedBall (0 : ℂ) r, g w = (Real.pi * r ^ 2 : ℝ) • g 0` |
| `integral_closedBall_zero_eq_polar` | a01A07 | `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (q : ℂ → E) {r : ℝ} (hr : 0 < r) : ∫ w in closedBall (0 : ℂ) r, q w = ∫ p in Set.Ioc (0 : ℝ) r ×ˢ Set.Ioo (-Real.pi) Real.pi, p.1 • q (Complex.polarCoord.symm p)` |
| `integral_cos_mul_eq_sinc` | LIB: ConstructionTargets.Sinc | `(x : ℝ) : ∫ t in (0 : ℝ)..1, Real.cos (t * x) = Real.sinc x` |
| `integral_eq_rational` | a94J06 | `{z : ℂ} : (∮ ζ in C(0, 1), starRingEnd ℂ ζ / (ζ - z)) = ∮ ζ in C(0, 1), ((ζ * (ζ - z))⁻¹ : ℂ)` |
| `integral_exp_neg_mul_cos_Ioi` | LIB: ConstructionTargets.Sinc | `{a : ℝ} (ha : 0 < a) (t : ℝ) : ∫ x in Set.Ioi (0 : ℝ), Real.exp (-a * x) * Real.cos (t * x) = a / (a ^ 2 + t ^ 2)` |
| `integral_exp_neg_mul_sinc_Ioi` | LIB: ConstructionTargets.Sinc | `{a : ℝ} (ha : 0 < a) : ∫ x in Set.Ioi (0 : ℝ), Real.exp (-a * x) * Real.sinc x = Real.arctan (1 / a)` |
| `integral_inv_one_plus_sq` | a95A03 | `: ∫ r in Ioi (0:ℝ), (1 + r ^ 2)⁻¹ ∂volume = π / 2` |
| `integral_inv_one_plus_x` | a93J02 | `: ∫ x in (0:ℝ)..1, 1 / (1 + x) = log 2` |
| `integral_inv_sq_half` | a01A10 | `{a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : (∫ x in a..b, 1 / (2 * x ^ 2)) = 1 / (2 * a) - 1 / (2 * b)` |
| `integral_inv_two_plus_cos` | a92J06 | `: ∫ θ in (0 : ℝ)..2 * π, 1 / (2 + Real.cos θ) = 2 * π / sqrt 3` |
| `integral_le_bound_mul_measure` | a94J01 | `{f : (Fin n → ℝ) → ℝ} {M : ℝ} (hM : 0 ≤ M) {E : Set (Fin n → ℝ)} (hE : MeasurableSet E) (hfinite : volume E < ⊤) (hbound : ∀ x ∈ E, ‖f x‖ ≤ M) : ∫ x in E, ‖f x‖ ∂volume ≤ M * (volume E).toReal` |
| `integral_norm_rpow_tendsto_measure_support` | a96A01 | `{f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 1) volume) : Tendsto (fun p : ℝ => ∫ x in Icc (0 : ℝ) 1, ‖f x‖ ^ p ∂volume) (nhdsWithin 0 (Ioi 0)) (nhds ((volume.restrict (Icc 0 1)) {x \| 0 < ‖f x‖}).toReal)` |
| `integral_one_div_sq` | LIB: ConstructionTargets.Sinc | `{a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : ∫ x in a..b, 1 / x ^ 2 = 1 / a - 1 / b` |
| `integral_partial_fractions` | a94J06 | `{z : ℂ} (hz0 : z ≠ 0) (hz1 : ‖z‖ ≠ 1) : (∮ ζ in C(0, 1), ((ζ * (ζ - z))⁻¹ : ℂ)) = ∮ ζ in C(0, 1), (z⁻¹ * ((ζ - z)⁻¹ - ζ⁻¹) : ℂ)` |
| `integral_poissonLayerWeight_Ioi` | LIB: ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) (t : ℝ) : ∫ s in Ioi \|t\|, poissonLayerWeight y s ∂volume = poissonKernel y t` |
| `integral_sin_pow_even_doubleFactorial` | a01A04 | `(k : ℕ) : (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ (2 * k + 2)) = Real.pi * (Nat.doubleFactorial (2 * k + 1) : ℝ) / (Nat.doubleFactorial (2 * k + 2) : ℝ)` |
| `integral_sin_pow_odd_doubleFactorial` | a01A04 | `(k : ℕ) : (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ (2 * k + 1)) = 2 * (Nat.doubleFactorial (2 * k) : ℝ) / (Nat.doubleFactorial (2 * k + 1) : ℝ)` |
| `integral_sinc_eq_cos_div_sub` | LIB: ConstructionTargets.Sinc | `{a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : ∫ x in a..b, Real.sinc x = Real.cos a / a - Real.cos b / b - ∫ x in a..b, Real.cos x / x ^ 2` |
| `integral_spike` | a01J01 | `(n : ℕ) : ∫ t, spike n t = 1` |
| `integral_sub_center_inv` | a94J06 | `: (∮ ζ in C(0, 1), (ζ⁻¹ : ℂ)) = 2 * π * I` |
| `integral_sub_inv_eq_zero` | a94J06 | `{w : ℂ} (hw : 1 < ‖w‖) : (∮ ζ in C(0, 1), (ζ - w)⁻¹) = 0` |
| `integral_sub_inv_of_mem` | a94J06 | `{w : ℂ} (hw : ‖w‖ < 1) : (∮ ζ in C(0, 1), (ζ - w)⁻¹) = 2 * π * I` |
| `integral_translate_norm` | a95J08 | `{f : ℝ → ℝ} (hf : Integrable f volume) (y : ℝ) : ∫ x, ‖f (x - y)‖ ∂volume = ∫ x, ‖f x‖ ∂volume` |
| `integral_univ_inv_one_plus_sq_eq` | a95A03 | `: ∫ (x : ℝ), (1 + x ^ 2)⁻¹ ∂volume = π` |
| `integral_x7_over_1_plus_x12` | a94A06 | `: ∫ x in Ioi (0:ℝ), x^7 / (1 + x^12) = Real.sqrt 3 * π / 18` |
| `integral_zero_to_dyadic_eq` | a95A04 | `{f : ℝ → ℝ} (hf : IntegrableOn f (Icc (0 : ℝ) 1) volume) (hsym : SymmetricMeanValue f) (j k : ℕ) (hk : k ≤ 2 ^ j) : ∫ t in (0 : ℝ)..((k : ℝ) / 2 ^ j), f t = (k : ℝ) * (∫ t in (0 : ℝ)..1, f t) / 2 ^ j` |
| `integral_zero_to_eq_mul` | a95A04 | `{f : ℝ → ℝ} (hf : IntegrableOn f (Icc (0 : ℝ) 1) volume) (hsym : SymmetricMeanValue f) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : ∫ t in (0 : ℝ)..x, f t = x * ∫ t in (0 : ℝ)..1, f t` |
| `integrand_eq_rational` | a94J06 | `{ζ z : ℂ} (hζ : ‖ζ‖ = 1) (hne : ζ ≠ z) : starRingEnd ℂ ζ / (ζ - z) = (ζ * (ζ - z))⁻¹` |
| `integrand_one_sub_neg` | a96J08 | `(ω : ℂ) (x : ℝ) : integrand (1 - ω) (-x) = -integrand ω x` |
| `intervalIntegral_zero_two_pi_eq_add_reflection` | LIB: ConstructionTargets.HerglotzRigidity | `(q : ℝ → ℝ) (hq : Continuous q) : (∫ θ in (0 : ℝ)..2 * Real.pi, q θ) = ∫ θ in (0 : ℝ)..Real.pi, (q θ + q (2 * Real.pi - θ))` |
| `inv_le_one_of_le_one` | a94J08 | `{a : ℝ} (ha : 1 ≤ a) : a⁻¹ ≤ 1` |
| `isBounded_sublevel` | LIB: ConstructionTargets.LemniscateComponents | `(hp : 0 < p.natDegree) : IsBounded (sublevel p)` |
| `isBounded_sublevel` | a00J04 | `(hp : 0 < p.natDegree) : IsBounded (sublevel p)` |
| `isBounded_sublevel` | a01A08 | `(hp : 0 < p.natDegree) : IsBounded (sublevel p)` |
| `isClosed_lemniscate` | LIB: ConstructionTargets.LemniscateComponents | `: IsClosed (lemniscate p)` |
| `isClosed_lemniscate` | a00J04 | `: IsClosed (lemniscate p)` |
| `isClosed_lemniscate` | a01A08 | `: IsClosed (lemniscate p)` |
| `isCompact_prod` | t91A03 | `(hX : IsCompact (univ : Set X)) (hY : IsCompact (univ : Set Y)) : IsCompact (univ : Set (X × Y))` |
| `isOpen_ordConnectedComponent_of_isOpen` | LIB: ConstructionTargets.LusinN | `{U : Set ℝ} (hU : IsOpen U) (x : ℝ) : IsOpen (ordConnectedComponent U x)` |
| `isOpen_ordConnectedComponent_of_isOpen` | a95A02 | `{U : Set ℝ} (hU : IsOpen U) (x : ℝ) : IsOpen (ordConnectedComponent U x)` |
| `isPathConnected_univ_of_connected` | t94A05 | `(M : Type*) [TopologicalSpace M] [LocPathConnectedSpace M] [ConnectedSpace M] : IsPathConnected (Set.univ : Set M)` |
| `IsPolynomialMap.differentiable` | a03J02 | `{n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} (hf : IsPolynomialMap f) : Differentiable ℝ f` |
| `isPreconnected_subset_superlevel_or_sublevel` | LIB: ConstructionTargets.LemniscateComponents | `{S : Set ℂ} (hS : IsPreconnected S) (hSL : Disjoint S (lemniscate p)) : S ⊆ superlevel p ∨ S ⊆ sublevel p` |
| `isPreconnected_subset_superlevel_or_sublevel` | a00J04 | `{S : Set ℂ} (hS : IsPreconnected S) (hSL : Disjoint S (lemniscate p)) : S ⊆ superlevel p ∨ S ⊆ sublevel p` |
| `isPreconnected_subset_superlevel_or_sublevel` | a01A08 | `{S : Set ℂ} (hS : IsPreconnected S) (hSL : Disjoint S (lemniscate p)) : S ⊆ superlevel p ∨ S ⊆ sublevel p` |
| `iterate_deriv_heatConv_eq_integral` | a96A04 | `{t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : MemLp f 2 volume) (n : ℕ) (x : ℝ) : (deriv^[n] (heatConv t f)) x = ∫ y, (deriv^[n] (heatKernel t)) (x - y) * f y ∂volume` |
| `iUnion` | a95J06 | `{f : ℝ → ℝ} {s : ℕ → Set ℝ} (h : ∀ n, LusinConditionN f (s n)) : LusinConditionN f (⋃ n, s n)` |
| `iUnion_ordConnectedComponents_eq` | LIB: ConstructionTargets.LusinN | `{U : Set ℝ} : ⋃ x ∈ ordConnectedSection U, ordConnectedComponent U x = U` |
| `iUnion_ordConnectedComponents_eq` | a95A02 | `{U : Set ℝ} : ⋃ x ∈ ordConnectedSection U, ordConnectedComponent U x = U` |
| `L1_disk_convergence_analytic_upgrade` | a01A07 | `{f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} (hΩ : IsOpen Ω) (hf : ∀ n, DifferentiableOn ℂ (f n) Ω) (hF : ContinuousOn F Ω) (hconv : L1ConvergesOnDisks f F Ω) : DifferentiableOn ℂ F Ω ∧ (∀ K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn f F atTop K) ∧ (∀ K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn (fun n z => deriv (f n) z) (deriv F) atTop K)` |
| `lacunary_majorant_summable` | a95A06 | `: Summable (fun n : ℕ => (1 : ℝ) / ↑n.factorial)` |
| `lacunary_term_bound` | a95A06 | `(n : ℕ) (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) : ‖lacunaryTerm n z‖ ≤ (1 : ℝ) / ↑n.factorial` |
| `lacunarySeries_continuousOn` | a95A06 | `: ContinuousOn lacunarySeries (closedBall (0 : ℂ) 1)` |
| `lacunarySeries_differentiableOn` | a95A06 | `: DifferentiableOn ℂ lacunarySeries (ball (0 : ℂ) 1)` |
| `lacunarySeries_has_disconnected_extension` | a95A06 | `: ∃ (U : Set ℂ) (F : ℂ → ℂ), IsOpen U ∧ ball (0 : ℂ) 1 ⊂ U ∧ DifferentiableOn ℂ F U ∧ ∀ z ∈ ball (0 : ℂ) 1, F z = lacunarySeries z` |
| `lacunarySeries_hasDerivAt_of_norm_lt_one` | a95A06 | `{z : ℂ} (hz : ‖z‖ < 1) : HasDerivAt lacunarySeries (∑' n : ℕ, z ^ (n.factorial - 1)) z` |
| `lacunarySeries_natural_boundary` | a95A06 | `: ¬∃ (U : Set ℂ) (F : ℂ → ℂ), IsOpen U ∧ IsConnected U ∧ ball (0 : ℂ) 1 ⊂ U ∧ DifferentiableOn ℂ F U ∧ ∀ z ∈ ball (0 : ℂ) 1, F z = lacunarySeries z` |
| `lacunaryTerm_continuousOn` | a95A06 | `(n : ℕ) : ContinuousOn (lacunaryTerm n) (closedBall (0 : ℂ) 1)` |
| `lacunaryTerm_differentiableOn` | a95A06 | `(n : ℕ) : DifferentiableOn ℂ (lacunaryTerm n) (ball (0 : ℂ) 1)` |
| `lacunaryTerm_hasDerivAt` | a95A06 | `(n : ℕ) (z : ℂ) : HasDerivAt (lacunaryTerm n) (z ^ (n.factorial - 1)) z` |
| `ladderConnected_of_connected` | t94J01 | `(h : IsPreconnected (Set.univ : Set X)) : LadderConnectedSpace X` |
| `ladderConnected_of_subsingleton` | t94J01 | `(X : Type*) [TopologicalSpace X] [Subsingleton X] : LadderConnectedSpace X` |
| `laplace_deriv_bound_integrable` | a01A09 | `(data : LaplaceData) {a : ℝ} (ha : 0 < a) : Integrable (fun t : ℝ => ‖data.f t‖ * (t * Real.exp (-a * t))) «μ₊»` |
| `laplace_integrand_integrable` | a01A09 | `(data : LaplaceData) {z : ℂ} (hz : 0 < z.re) : Integrable (fun t => data.f t * laplaceKernel z t) «μ₊»` |
| `laplace_transform_analytic` | a01A09 | `(data : LaplaceData) : AnalyticOn ℂ (laplaceTransform data.f) rightHalfPlane` |
| `laplace_transform_entire_of_compact_support` | a01A09 | `(f : ℝ → ℂ) (hf : compactSupportOnHalfLine f) : AnalyticOn ℂ (fun z => laplaceTransform f z) Set.univ` |
| `le_of_lt_of_interval` | a96J01 | `{n m : ℕ} (hnm : n < m) : b n ≤ a m` |
| `limit_ge_geometric_mean` | a96A01 | `{f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 1) volume) (hf_pos : ∀ᵐ x ∂(volume.restrict (Icc 0 1)), 0 < ‖f x‖) {L : ℝ} (hL : 0 < L) (hLim : Tendsto (quasiNorm f) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) : exp (∫ x in Set.Icc (0:ℝ) 1, log ‖f x‖ ∂volume) ≤ L` |
| `linear_growth_of_entire_of_im_growth` | LIB: ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f) {C : ℝ} (hC : 0 ≤ C) (him : ∀ z : ℂ, \|(f z).im\| ≤ C * (1 + ‖z‖)) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, ‖f z‖ ≤ K * (1 + ‖z‖)` |
| `linear_growth_of_entire_pick` | LIB: ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f) (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (hpos : ∀ z : ℂ, 0 < z.im → 0 < (f z).im) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖f z‖ ≤ C * (1 + ‖z‖)` |
| `lintegral_eq_ofReal_mul_lintegral_comp_mul` | LIB: ConstructionTargets.RadialMajorantAE | `{F : ℝ → ℝ≥0∞} (hF : Measurable F) {y : ℝ} (hy : 0 < y) : (∫⁻ s, F s ∂volume) = ENNReal.ofReal y * ∫⁻ u, F (y * u) ∂volume` |
| `lintegral_mul_le_lintegral_rpow` | LIB: ConstructionTargets.YoungConvolution | `{α : Type*} [MeasurableSpace α] {μ : Measure α} {w v : α → ℝ≥0∞} (hw : AEMeasurable w μ) (hv : AEMeasurable v μ) {r : ℝ} (hr : 1 < r) : (∫⁻ x, w x * v x ∂μ) ≤ (∫⁻ x, w x ∂μ) ^ (1 - 1 / r) * (∫⁻ x, w x * v x ^ r ∂μ) ^ (1 / r)` |
| `lintegral_mul_radial_layerCake` | LIB: ConstructionTargets.RadialMajorantAE | `{g w φ : ℝ → ℝ≥0∞} (hg : Measurable g) (hw : Measurable w) (hφ : ∀ t, φ t = ∫⁻ s in Ici \|t\|, w s ∂volume) : ∫⁻ t, g t * φ t ∂volume = ∫⁻ s, w s * (∫⁻ t in Icc (-s) s, g t ∂volume) ∂volume` |
| `lintegral_poissonKernel_mul_enorm_sub_eq_radialLaverage` | LIB: ConstructionTargets.RadialMajorantAE | `{f : ℝ → ℝ} (hfm : Measurable f) (x : ℝ) {y : ℝ} (hy : 0 < y) : (∫⁻ t, ENNReal.ofReal (poissonKernel y t) * ‖f (x - t) - f x‖ₑ ∂volume) = ∫⁻ u, ENNReal.ofReal (poissonLayerDensity u) * radialLaverage f x (y * u) ∂volume` |
| `lintegral_poissonLayerWeight_Ici` | LIB: ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) (t : ℝ) : ∫⁻ s in Ici \|t\|, ENNReal.ofReal (poissonLayerWeight y s) ∂volume = ENNReal.ofReal (poissonKernel y t)` |
| `liouville_bounded` | a94J05 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f) (M : ℝ) (hM : ∀ z, ‖f z‖ ≤ M) : ∃ c : ℂ, ∀ z, f z = c` |
| `liouville_re_bounded_below` | a94J05 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f) (C : ℝ) (hC : ∀ z, -C ≤ (f z).re) : ∃ c : ℂ, ∀ z, f z = c` |
| `lipschitz_implies_ac` | a93A04 | `{f : ℝ → ℝ} (h : LipschitzOn01 f) : AbsolutelyContinuousOnInterval f 0 1` |
| `lipschitz_V_limit_implies_ac` | a93A04 | `{f : ℝ → ℝ} {fₙ : ℕ → ℝ → ℝ} (hlip : ∀ n, LipschitzOn01 (fₙ n)) (hconv : Tendsto (fun n => totalVariation (fun x => fₙ n x - f x)) atTop (𝓝 0)) : AbsolutelyContinuousOnInterval f 0 1` |
| `logDeriv_factorizedRational_eq_finsum` | LIB: ConstructionTargets.Rouche | `{U : Set ℂ} (D : Function.locallyFinsuppWithin U ℤ) (hD : D.support.Finite) {x : ℂ} (hx : x ∉ D.support) : logDeriv (∏ᶠ u, (· - u) ^ D u) x = ∑ᶠ u, (D u : ℂ) / (x - u)` |
| `logIntegral_im_bounds` | a02J07 | `{γ : ℝ → ℂ} (hγ : SlitPath γ) : 0 < \|(logIntegral γ).im\| ∧ \|(logIntegral γ).im\| < 2 * π` |
| `logIntegral_im_eq_argStar_diff` | a02J07 | `{γ : ℝ → ℂ} (hγ : SlitPath γ) : (logIntegral γ).im = argStar (γ 1) - limUnder (𝓝[>] 0) (fun t => argStar (γ t))` |
| `logStar_im` | a02J07 | `(z : ℂ) : (logStar z).im = argStar z` |
| `lower_bound` | a00J01 | `{f : ℝ → ℝ} (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 1))) (α : ℝ≥0∞) (hα : α < eLpNorm f ⊤ (volume.restrict (Icc 0 1))) : ∀ᶠ p in atTop, α ≤ eLpNorm f p (volume.restrict (Icc 0 1))` |
| `lowerQuantile_maps` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) {y : ℝ} (hy : y ∈ Icc (f 0) (f 1)) : f (lowerQuantile f y) = y` |
| `lowerQuantile_mem` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) {y : ℝ} (hy : y ≤ f 1) : lowerQuantile f y ∈ Icc (0 : ℝ) 1` |
| `lowerQuantile_mono` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (hy₂ : y₂ ≤ f 1) : lowerQuantile f y₁ ≤ lowerQuantile f y₂` |
| `m03J03_abs_eval_not_distribution` | m03J03 | `: ¬ ∃ T : Distribution (⊤ : Opens ℝ) ℝ ⊤, ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤, T φ = \|φ 0\|` |
| `m03J03_heaviside_sin_integral_deriv` | m03J03 | `(φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) : -(∫ x : ℝ, m03J03Heaviside x * Real.sin x * deriv φ x) = ∫ x : ℝ, m03J03Heaviside x * Real.cos x * φ x` |
| `m03J03_integral_heaviside_mul` | m03J03 | `(g : ℝ → ℝ) : (∫ x : ℝ, m03J03Heaviside x * g x) = ∫ x in Ioi (0 : ℝ), g x` |
| `m03J05MixedEigenfunction_deriv_one` | m03J05 | `(n : ℕ) : deriv (m03J05MixedEigenfunction n) 1 = 0` |
| `m03J05MixedEigenfunction_hasDerivAt` | m03J05 | `(n : ℕ) (x : ℝ) : HasDerivAt (m03J05MixedEigenfunction n) (((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2 * Real.cos ((((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2) * x)) x` |
| `m03J05MixedEigenfunction_neg_deriv_deriv` | m03J05 | `(n : ℕ) (x : ℝ) : -deriv (deriv (m03J05MixedEigenfunction n)) x = m03J05MixedEigenvalue n * m03J05MixedEigenfunction n x` |
| `m03J05MixedEigenfunction_zero` | m03J05 | `(n : ℕ) : m03J05MixedEigenfunction n 0 = 0` |
| `m03J05MixedEigenvalue_injective` | m03J05 | `: Function.Injective m03J05MixedEigenvalue` |
| `m03J05MixedEigenvalue_pos` | m03J05 | `(n : ℕ) : 0 < m03J05MixedEigenvalue n` |
| `m03J05MixedEigenvalue_strictMono` | m03J05 | `: StrictMono m03J05MixedEigenvalue` |
| `m03J05MixedFrequency_pos` | m03J05 | `(n : ℕ) : 0 < ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2` |
| `m03J05MixedFrequency_strictMono` | m03J05 | `: StrictMono (fun n : ℕ ↦ ((2 * n + 1 : ℕ) : ℝ) * Real.pi / 2)` |
| `m95A01_left_residual` | m95A01 | `{𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] (A B₀ : X →L[𝕜] X) (n : ℕ) : 1 - A * m95A01Iterates A B₀ n = (1 - A * B₀) ^ (2 ^ n)` |
| `m95A01_right_residual` | m95A01 | `{𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] (A B₀ : X →L[𝕜] X) (n : ℕ) : 1 - m95A01Iterates A B₀ n * A = (1 - B₀ * A) ^ (2 ^ n)` |
| `m95A02_tendsto_coord_of_weak` | m95A02 | `(f : ℕ → m95A02H) (g : m95A02H) (h : Tendsto (fun n ↦ toWeakSpace ℂ m95A02H (f n)) atTop (nhds (toWeakSpace ℂ m95A02H g))) (j : ℤ) : Tendsto (fun n ↦ f n j) atTop (nhds (g j))` |
| `m95A02MaxDist_le_of_forall` | m95A02 | `(f g : m95A02H) (C : ℝ) (hC : 0 ≤ C) (h : ∀ x ∈ Icc (0 : ℝ) (2 * Real.pi), dist (m95A02Value f x) (m95A02Value g x) ≤ C) : m95A02MaxDist f g ≤ C` |
| `m95A02MaxDist_self` | m95A02 | `(f : m95A02H) : m95A02MaxDist f f = 0` |
| `m95A02Value_single` | m95A02 | `(n : ℤ) (x : ℝ) : m95A02Value (lp.single 2 n 1 : m95A02H) x = m95A02BasisFunction n x` |
| `m95A02Value_zero` | m95A02 | `(x : ℝ) : m95A02Value (0 : m95A02H) x = 0` |
| `m96A01_eigenspace_eq_ker` | m96A01 | `{X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (L : X →L[ℂ] X) (eigenvalue : ℂ) : Module.End.eigenspace L.toLinearMap eigenvalue = LinearMap.ker (L.toLinearMap - eigenvalue • LinearMap.id)` |
| `m99A02_derivative_sq_le_radial` | m99A02 | `(i : Fin 2) {x : m99A02Point} (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) : (m99A02Derivative i x) ^ 2 ≤ 1 / (9 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (4 / 3 : ℝ))` |
| `m99A02_neg_log_norm_pos` | m99A02 | `{x : m99A02Point} (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) : 0 < -Real.log ‖x‖` |
| `m99A02_sum_derivative_sq` | m99A02 | `{x : m99A02Point} (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) : ∑ i : Fin 2, (m99A02Derivative i x) ^ 2 = 1 / (9 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (4 / 3 : ℝ))` |
| `m99A02Derivative_measurable` | m99A02 | `(i : Fin 2) : Measurable (m99A02Derivative i)` |
| `m99A02Function_measurable` | m99A02 | `: Measurable m99A02Function` |
| `m99A02Function_pos` | m99A02 | `{x : m99A02Point} (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) : 0 < m99A02Function x` |
| `m99A03_firstBlock_separated` | m99A03 | `(n m : ℕ) (hnm : n ≠ m) : 1 ≤ dist ((lp.single 2 n 1, 0, 0) : m99A03ExampleSpace) (lp.single 2 m 1, 0, 0)` |
| `m99A03_not_isCompactOperator_of_separated_unit` | m99A03 | `(A : m99A03ExampleSpace →L[ℂ] m99A03ExampleSpace) (u : ℕ → m99A03ExampleSpace) (hu : ∀ n, ‖u n‖ ≤ 1) (hsep : ∀ n m, n ≠ m → 1 ≤ dist (A (u n)) (A (u m))) : ¬ IsCompactOperator A` |
| `m99A03Shift_cube` | m99A03 | `: m99A03Shift ^ 3 = 0` |
| `m99A03Shift_sq_apply` | m99A03 | `(x : m99A03ExampleSpace) : (m99A03Shift ^ 2) x = (x.2.2, 0, 0)` |
| `m99A06_convolution_eLpNorm_le` | m99A06 | `{f g : ℝ → ℝ} (hf : Integrable f volume) (hg : Integrable g volume) : eLpNorm (fun x : ℝ ↦ ∫ y : ℝ, f (x - y) * g y) 1 volume ≤ eLpNorm f 1 volume * eLpNorm g 1 volume` |
| `m99A06_fixedPointMap_integrable` | m99A06 | `(ε : ℝ) {f : ℝ → ℝ} (hf : Integrable f volume) : Integrable (fun x : ℝ => ε * Real.exp (-\|x\| ^ 2) - Real.sin x * m99A06SelfConvolution f x) volume` |
| `m99A06_gaussian_integrable` | m99A06 | `: Integrable (fun x : ℝ => Real.exp (-\|x\| ^ 2)) volume` |
| `m99A06_quadraticTerm_eLpNorm_le` | m99A06 | `{f : ℝ → ℝ} (hf : Integrable f volume) : eLpNorm (fun x : ℝ ↦ Real.sin x * m99A06SelfConvolution f x) 1 volume ≤ eLpNorm f 1 volume ^ 2` |
| `m99A06_selfConvolution_eLpNorm_le` | m99A06 | `{f : ℝ → ℝ} (hf : Integrable f volume) : eLpNorm (m99A06SelfConvolution f) 1 volume ≤ eLpNorm f 1 volume ^ 2` |
| `m99A06_selfConvolution_integrable` | m99A06 | `{f : ℝ → ℝ} (hf : Integrable f volume) : Integrable (m99A06SelfConvolution f) volume` |
| `m99A06_sin_mul_eLpNorm_le` | m99A06 | `(p : ENNReal) (g : ℝ → ℝ) : eLpNorm (fun x : ℝ ↦ Real.sin x * g x) p volume ≤ eLpNorm g p volume` |
| `m99A06_sin_mul_selfConvolution_integrable` | m99A06 | `{f : ℝ → ℝ} (hf : Integrable f volume) : Integrable (fun x : ℝ => Real.sin x * m99A06SelfConvolution f x) volume` |
| `maps_upper_halfPlane_one_side` | a94A10 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f) (hreal : RealIffReal f) : (∀ z : ℂ, 0 < z.im → 0 < (f z).im) ∨ (∀ z : ℂ, 0 < z.im → (f z).im < 0)` |
| `measurable_ballSlice` | a01A04 | `: Measurable ballSlice` |
| `measurable_function_ae_eq_borel` | a01J02 | `{f : Set.Icc (0 : ℝ) 1 → ℝ} (hf : NullMeasurable f (volume : Measure (Set.Icc (0 : ℝ) 1))) : ∃ g : Set.Icc (0 : ℝ) 1 → ℝ, @Measurable (Set.Icc (0 : ℝ) 1) ℝ (MeasurableSpace.comap Subtype.val (borel ℝ)) (borel ℝ) g ∧ f =ᵐ[(volume : Measure (Set.Icc (0 : ℝ) 1))] g` |
| `measurable_quantile` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) : Measurable (quantile f)` |
| `measurable_set_ae_eq_borel` | a01J02 | `{A : Set ℝ} (hA : NullMeasurableSet A volume) : ∃ B : Set ℝ, @MeasurableSet ℝ (borel ℝ) B ∧ AlmostEqualVolume A B` |
| `measurable_subset_Icc_eq_sigmaCompact_union_null` | LIB: ConstructionTargets.LusinN | `{E : Set ℝ} (hE_meas : MeasurableSet E) (hE_sub : E ⊆ Icc (0:ℝ) 1) : ∃ (K : ℕ → Set ℝ) (N : Set ℝ), (∀ n, IsCompact (K n)) ∧ volume N = 0 ∧ E = (⋃ n, K n) ∪ N` |
| `measurable_subset_Icc_eq_sigmaCompact_union_null` | a95A02 | `{E : Set ℝ} (hE_meas : MeasurableSet E) (hE_sub : E ⊆ Icc (0:ℝ) 1) : ∃ (K : ℕ → Set ℝ) (N : Set ℝ), (∀ n, IsCompact (K n)) ∧ volume N = 0 ∧ E = (⋃ n, K n) ∪ N` |
| `measurable_sum_contains_interval` | a96J02 | `(A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) (hAint : Integrable (indicator A (1 : ℝ → ℝ)) volume) (hBint : Integrable (indicator B (1 : ℝ → ℝ)) volume) (hApos : 0 < volume A) (hBpos : 0 < volume B) (hAfin : volume A ≠ ∞) (hBfin : volume B ≠ ∞) : ∃ a b : ℝ, a < b ∧ Ioo a b ⊆ A + B` |
| `measure_image_critical_set_eq_zero` | a94A05 | `(I : Set ℝ) (hI : IsOpen I) {f : ℝ → ℝ} {C : Set ℝ} (hC : C ⊆ I) (hf_diff : ∀ x ∈ C, DifferentiableAt ℝ f x) (hf_crit : ∀ x ∈ C, deriv f x = 0) : volume (f '' C) = 0` |
| `measure_image_criticalSet_eq_zero` | a95J07 | `{f : ℝ → ℝ} : volume (f '' criticalSet f) = 0` |
| `measure_symmDiff_eq_zero` | a01J02 | `{A B : Set ℝ} (h : volume ((A \ B) ∪ (B \ A)) = 0) : volume (A ∆ B) = 0` |
| `mem_posSlitPlane_iff` | a02J07 | `{z : ℂ} : z ∈ posSlitPlane ↔ ¬(z.im = 0 ∧ 0 ≤ z.re)` |
| `memLp_limit_of_ae_tendsto_bounded` | a96A03 | `{f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (hf_meas : ∀ n, AEStronglyMeasurable (f n) volume) (hf_bdd : ∀ n, eLpNorm (f n) 2 volume ≤ 1) (hae : ∀ᵐ x ∂volume, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : MemLp g 2 volume ∧ eLpNorm g 2 volume ≤ 1` |
| `memLp_radial_R3_iff` | LIB: ConstructionTargets.RadialIntegrationR3 | `{g : ℝ → ℝ} {p : ℝ≥0∞} (hg : AEStronglyMeasurable (fun x : E => g ‖x‖) volume) (hp0 : p ≠ 0) (hp_top : p ≠ ∞) : MemLp (fun x : E => g ‖x‖) p volume ↔ IntegrableOn (fun r : ℝ => r ^ 2 * ‖g r‖ ^ p.toReal) (Ioi 0)` |
| `memLp_two_iterate_deriv_standardGaussian` | a96A04 | `(n : ℕ) : MemLp (deriv^[n] (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))) 2 volume` |
| `memLp_two_polynomial_abs_add_one_gaussian` | a96A04 | `(p : Polynomial ℝ) {b : ℝ} (hb : 0 < b) : MemLp (fun x : ℝ => p.eval (\|x\| + 1) * Real.exp (-b * x ^ 2)) 2 volume` |
| `mid_add_hw` | a96J01 | `(n : ℕ) : mid n + hw n = b n` |
| `mid_le_b` | a96J01 | `(n : ℕ) : mid n ≤ b n` |
| `mid_mem` | a96J01 | `(n : ℕ) : mid n ∈ Set.Icc (0:ℝ) 1` |
| `mid_sub_hw` | a96J01 | `(n : ℕ) : mid n - hw n = a n` |
| `mono` | a95J06 | `{f : ℝ → ℝ} {s t : Set ℝ} (h : LusinConditionN f s) (hts : t ⊆ s) : LusinConditionN f t` |
| `monotone_clamp01` | LIB: ConstructionTargets.BanachZarecki | `: Monotone clamp01` |
| `monotone_image_Icc` | a96J04 | `(f : ℝ → ℝ) (hf : MonotoneOn f (Icc 0 1)) {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (_hab : a ≤ b) : f '' Icc a b ⊆ Icc (f a) (f b)` |
| `monotone_image_interval` | a96J04 | `(f : ℝ → ℝ) (hf : MonotoneOn f (Icc 0 1)) {a b x : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hx : x ∈ Icc 0 1) (hax : a ≤ x) (hxb : x ≤ b) : f a ≤ f x ∧ f x ≤ f b` |
| `monotone_monotoneExtension` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf : MonotoneOn f (Icc (0 : ℝ) 1)) : Monotone (monotoneExtension f)` |
| `monotone_of_homeomorphism` | a95J06 | `{f : ℝ → ℝ} (hf_bij : BijOn f (Icc 0 1) (Icc 0 1)) (hf_cont : ContinuousOn f (Icc 0 1)) : MonotoneOn f (Icc 0 1) ∨ AntitoneOn f (Icc 0 1)` |
| `monotone_of_homeomorphism_fixing_cantor` | a95J06 | `{f : ℝ → ℝ} (hf_bij : BijOn f (Icc 0 1) (Icc 0 1)) (hf_cont : ContinuousOn f (Icc 0 1)) (hf_fix : ∀ x ∈ cantorSet, f x = x) : MonotoneOn f (Icc 0 1)` |
| `monotone_quantile` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) : Monotone (quantile f)` |
| `monotoneExtension_eq_self` | LIB: ConstructionTargets.BanachZarecki | `(f : ℝ → ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : monotoneExtension f x = f x` |
| `MvPolynomial.eval_differentiable` | a03J02 | `{n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Differentiable ℝ (fun x : Fin n → ℝ => MvPolynomial.eval x p)` |
| `nat_tsum_decomp` | a03J01 | `(n : ℕ) : ((n : ℕ) : ENNReal) = ∑' j : ℕ, ((j + 1 : ℕ) : ENNReal) * (if (n = (j + 1 : ℕ)) then (1 : ENNReal) else 0)` |
| `neg_mem_slitPlane_of_posSlitPlane` | a02J07 | `{z : ℂ} (hz : z ∈ posSlitPlane) : -z ∈ slitPlane` |
| `no_entire_lower_bound_three_halves` | a94J08 | `: ¬∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ∀ z : ℂ, ‖z‖ ^ ((3:ℝ)/2) ≤ ‖f z‖` |
| `nonconstant_of_realIffReal` | a94A10 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f) (hreal : RealIffReal f) : ∃ z₁ z₂ : ℂ, f z₁ ≠ f z₂` |
| `nonempty_nested_inter` | t91J04 | `{a b : ℕ → ℝ} (ha : Monotone a) (hb : Antitone b) (hAB : ∀ n, a n ≤ b n) : (⋂ n, Set.Icc (a n) (b n)).Nonempty` |
| `nonzero_of_lower_bound` | a94J08 | `(f : ℂ → ℂ) (hbound : ∀ z, ‖z‖ ^ ((3:ℝ)/2) ≤ ‖f z‖) (z : ℂ) (hz : z ≠ 0) : f z ≠ 0` |
| `norm_comp_eq` | a00J03 | `{φ : X → X} (hφ : MeasurePreserving φ μ μ) {f : X → E} (hf : AEStronglyMeasurable f μ) : eLpNorm (f ∘ φ) p μ = eLpNorm f p μ` |
| `norm_damped_fresnel_le_one` | a01A10 | `{ε x : ℝ} (hε : 0 ≤ ε) : ‖cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)‖ ≤ 1` |
| `norm_exp_le_e` | a94J07 | `{z : ℂ} (hz : ‖z‖ ≤ 1) : ‖cexp z‖ ≤ Real.exp 1` |
| `norm_integral_damped_fresnel_le_inv` | a01A10 | `{ε a b : ℝ} (hε : 0 ≤ ε) (ha : 0 < a) (hab : a ≤ b) : ‖∫ x in a..b, cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)‖ ≤ 1 / a` |
| `norm_integral_fresnel_le_inv` | a01A10 | `{a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : ‖∫ x in a..b, cexp (Complex.I * (x : ℂ) ^ 2)‖ ≤ 1 / a` |
| `norm_integral_Ioi_damped_fresnel_le_inv` | a01A10 | `{ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) : ‖∫ x in Set.Ioi a, cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)‖ ≤ 1 / a` |
| `norm_integral_kernel_smul_le` | LIB: ConstructionTargets.KernelAverage | `{Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X] {ν : Measure Y} {μ : Measure X} {p : ENNReal} [Fact (1 ≤ p)] {k : Y → ℝ} (hk : ∀ᵐ y ∂ν, 0 ≤ k y) (F : Y → Lp ℝ p μ) : ‖∫ y, k y • F y ∂ν‖ ≤ ∫ y, k y * ‖F y‖ ∂ν` |
| `norm_inv_le_one_of_lower_bound` | a94J08 | `(f : ℂ → ℂ) (hf_ne : ∀ z, f z ≠ 0) (hbound : ∀ z, ‖z‖ ^ ((3:ℝ)/2) ≤ ‖f z‖) (z : ℂ) (hz : 1 ≤ ‖z‖) : ‖(f z)⁻¹‖ ≤ 1` |
| `norm_le_area_integral_div_area` | a01A07 | `{g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hg : DifferentiableOn ℂ g (closedBall z₀ r)) : ‖g z₀‖ ≤ (1 / (Real.pi * r ^ 2)) * ∫ w in closedBall z₀ r, ‖g w‖` |
| `norm_le_area_integral_div_area_of_integral_eq` | a01A07 | `{g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hmean : ∫ w in closedBall z₀ r, g w = (Real.pi * r ^ 2 : ℝ) • g z₀) : ‖g z₀‖ ≤ (1 / (Real.pi * r ^ 2)) * ∫ w in closedBall z₀ r, ‖g w‖` |
| `norm_le_circleAverage_norm` | a01A07 | `{g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hg : DifferentiableOn ℂ g (closedBall z₀ r)) : ‖g z₀‖ ≤ Real.circleAverage (fun w ↦ ‖g w‖) z₀ r` |
| `norm_le_liminf_of_weak` | a93A03 | `[CompleteSpace H] {h : ℕ → H} {x : H} (hweak : WeakTendsto h x) : ‖x‖ ≤ liminf (fun n => (‖h n‖ : ℝ)) atTop` |
| `norm_pow_of_norm_one` | a92J05 | `(z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) : ‖z ^ n‖ = 1` |
| `norm_quadraticQuotient_le` | a94J08 | `(f : ℂ → ℂ) (hbound : ∀ z : ℂ, ‖z‖ ^ ((3 : ℝ) / 2) ≤ ‖f z‖) (z : ℂ) : ‖quadraticQuotient f z‖ ≤ ‖z‖ ^ ((1 : ℝ) / 2)` |
| `norm_smul_pow_of_norm_one` | a92J05 | `(z : ℂ) (hz : ‖z‖ = 1) (c : ℂ) (n : ℕ) : ‖c * z ^ n‖ = ‖c‖` |
| `norm_spike` | a01J01 | `(n : ℕ) (x : ℝ) : ‖spike n x‖ = spike n x` |
| `norm_sub_le_area_integral_div_area` | a01A07 | `{g : ℂ → ℂ} {z₀ c : ℂ} {r : ℝ} (hr : 0 < r) (hg : DifferentiableOn ℂ g (closedBall z₀ r)) : ‖g z₀ - c‖ ≤ (1 / (Real.pi * r ^ 2)) * ∫ w in closedBall z₀ r, ‖g w - c‖` |
| `norm_sub_tendsto_zero_of_weak_and_norm` | a93A03 | `{h : ℕ → H} {x : H} (hweak : WeakTendsto h x) (hnorm : Tendsto (fun n => ‖h n‖) atTop (𝓝 ‖x‖)) : Tendsto (fun n => ‖h n - x‖) atTop (𝓝 0)` |
| `normalizedQuotient_differentiable` | a95J02 | `{f g : ℂ → ℂ} {n : ℕ} (hf : Differentiable ℂ f) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 ≠ 0) (hfg : f =ᶠ[nhds 0] fun z => z ^ n * g z) (hzero : ∀ z, z ≠ 0 → f z ≠ 0) : Differentiable ℂ (fun z => if z = 0 then (g 0)⁻¹ else z ^ n / f z)` |
| `not_bounded_isOpen_superlevel_frontier_lemniscate` | LIB: ConstructionTargets.LemniscateComponents | `{U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ superlevel p) (hF : frontier U ⊆ lemniscate p) (hnonempty : U.Nonempty) : False` |
| `not_bounded_isOpen_superlevel_frontier_lemniscate` | a00J04 | `{U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ superlevel p) (hF : frontier U ⊆ lemniscate p) (hnonempty : U.Nonempty) : False` |
| `not_bounded_isOpen_superlevel_frontier_lemniscate` | a01A08 | `{U : Set ℂ} (hU : IsOpen U) (hB : IsBounded U) (hS : U ⊆ superlevel p) (hF : frontier U ⊆ lemniscate p) (hnonempty : U.Nonempty) : False` |
| `not_fresnel_integral_statement` | a01A10 | `: ¬ ((∫ x in Set.Ioi (0 : ℝ), cexp (Complex.I * (x : ℂ)^2)) = (1 + Complex.I) * (√π) / (2 * (√2)))` |
| `not_isBounded_componentSet_of_subset_superlevel` | LIB: ConstructionTargets.LemniscateComponents | `(x : ↥((lemniscate p)ᶜ)) (hsuper : componentSet x ⊆ superlevel p) : ¬ IsBounded (componentSet x)` |
| `not_isBounded_componentSet_of_subset_superlevel` | a00J04 | `(x : ↥((lemniscate p)ᶜ)) (hsuper : componentSet x ⊆ superlevel p) : ¬ IsBounded (componentSet x)` |
| `not_isBounded_componentSet_of_subset_superlevel` | a01A08 | `(x : ↥((lemniscate p)ᶜ)) (hsuper : componentSet x ⊆ superlevel p) : ¬ IsBounded (componentSet x)` |
| `odd_ball_volume_exact` | a01A04 | `(k : ℕ) : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * k + 1))) 1)).toReal = 2 ^ (k + 1) * Real.pi ^ k / (Nat.doubleFactorial (2 * k + 1) : ℝ)` |
| `odd_ball_volume_le` | a01A04 | `(k : ℕ) : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * k + 1))) 1)).toReal ≤ 2 * Real.pi ^ k / k.factorial` |
| `ofReal_poissonLayerWeight_mul_radialLIntegral_scale` | LIB: ConstructionTargets.RadialMajorantAE | `(f : ℝ → ℝ) (x : ℝ) {y : ℝ} (hy : 0 < y) (u : ℝ) : ENNReal.ofReal y * (ENNReal.ofReal (poissonLayerWeight y (y * u)) * radialLIntegral f x (y * u)) = ENNReal.ofReal (poissonLayerDensity u) * radialLaverage f x (y * u)` |
| `one_le_norm_damping` | a01A10 | `{ε : ℝ} (hε : 0 ≤ ε) : (1 : ℝ) ≤ ‖(ε : ℂ) - I‖` |
| `one_le_of_uniform_bound` | a96A05 | `(P : Polynomial ℂ) {C : ℝ} (hC : ∀ z ∈ sphere (0 : ℂ) 1, ‖z⁻¹ - Polynomial.aeval z P‖ ≤ C) : 1 ≤ C` |
| `open_mem_unit_sphere_contains_rational_angle` | a95A06 | `{U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hzU : z ∈ U) (hz_norm : ‖z‖ = 1) : ∃ θ : ℚ, circleMap 0 1 (2 * Real.pi * (θ : ℝ)) ∈ U` |
| `openComponent_endpoints_mem_Icc` | a96J04 | `(U : Set ℝ) (hUI : U ⊆ Ioo 0 1) (c : ConnectedComponents U) : openComponentLeft U c ∈ Icc 0 1 ∧ openComponentRight U c ∈ Icc 0 1 ∧ openComponentLeft U c ≤ openComponentRight U c` |
| `openComponent_image_subset` | a96J04 | `(f : ℝ → ℝ) (hf : MonotoneOn f (Icc 0 1)) (U : Set ℝ) (hU : IsOpen U) (hUI : U ⊆ Ioo 0 1) (c : ConnectedComponents U) : f '' openComponentSet U c ⊆ Icc (f (openComponentLeft U c)) (f (openComponentRight U c))` |
| `openComponentRat_injective` | a96J04 | `(U : Set ℝ) (hU : IsOpen U) : Function.Injective (openComponentRat U hU)` |
| `openComponentRat_mem` | a96J04 | `(U : Set ℝ) (hU : IsOpen U) (c : ConnectedComponents U) : (openComponentRat U hU c : ℝ) ∈ openComponentSet U c` |
| `openComponentSet_eq_endpoints` | a96J04 | `(U : Set ℝ) (hU : IsOpen U) (hUI : U ⊆ Ioo 0 1) (c : ConnectedComponents U) : openComponentSet U c = Ioo (openComponentLeft U c) (openComponentRight U c)` |
| `openComponentSet_eq_Ioo` | a96J04 | `(U : Set ℝ) (hU : IsOpen U) (hUI : U ⊆ Ioo 0 1) (c : ConnectedComponents U) : openComponentSet U c = Ioo (sInf (openComponentSet U c)) (sSup (openComponentSet U c))` |
| `openComponentSet_exists_rat` | a96J04 | `(U : Set ℝ) (hU : IsOpen U) (c : ConnectedComponents U) : ∃ q : ℚ, (q : ℝ) ∈ openComponentSet U c` |
| `openComponentSet_injective` | a96J04 | `(U : Set ℝ) : Function.Injective (openComponentSet U)` |
| `openComponentSet_nonempty` | a96J04 | `(U : Set ℝ) (c : ConnectedComponents U) : (openComponentSet U c).Nonempty` |
| `openComponentSet_open` | a96J04 | `(U : Set ℝ) (hU : IsOpen U) (c : ConnectedComponents U) : IsOpen (openComponentSet U c)` |
| `openComponentSet_pairwiseDisjoint` | a96J04 | `(U : Set ℝ) : Pairwise (fun c d => Disjoint (openComponentSet U c) (openComponentSet U d))` |
| `openComponentSet_preconnected` | a96J04 | `(U : Set ℝ) (c : ConnectedComponents U) : IsPreconnected (openComponentSet U c)` |
| `openComponentSet_subset` | a96J04 | `(U : Set ℝ) (c : ConnectedComponents U) : openComponentSet U c ⊆ U` |
| `ordConnectedSection_pairwiseDisjoint` | LIB: ConstructionTargets.LusinN | `(U : Set ℝ) : (ordConnectedSection U).PairwiseDisjoint (ordConnectedComponent U)` |
| `ordConnectedSection_pairwiseDisjoint` | a95A02 | `(U : Set ℝ) : (ordConnectedSection U).PairwiseDisjoint (ordConnectedComponent U)` |
| `order_ge_two_of_deriv_zero` | a94A10 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f) (x₀ : ℝ) (hcrit : deriv f (↑x₀) = 0) : 2 ≤ analyticOrderAt (fun z => f z - f (↑x₀)) (↑x₀)` |
| `orlicz_bound_not_implies_L2` | a01A06 | `: ∃ (g : ℝ → ℝ) (A : ℝ), 0 < A ∧ OrliczBound g A ∧ ¬ IntegrableOn (fun x => g x ^ 2) (Icc (0 : ℝ) 1) volume` |
| `orthogonal_to_polynomials` | a94A04 | `{f : ℝ → ℝ} {μ : Measure ℝ} (hint : ∀ n : ℕ, Integrable (fun x => x ^ n * f x) (μ.restrict (Icc (0 : ℝ) 1))) (horth : ∀ n : ℕ, ∫ x in Icc (0:ℝ) 1, x ^ n * f x ∂μ = 0) (p : Polynomial ℝ) : ∫ x in Icc (0:ℝ) 1, Polynomial.eval x p * f x ∂μ = 0` |
| `p_card_roots` | a92J05 | `: p.roots.card = 10` |
| `p_monic` | a92J05 | `: p.Monic` |
| `p_natDegree` | a92J05 | `: p.natDegree = 10` |
| `p_no_roots_on_circle` | a92J05 | `(z : ℂ) (hz : ‖z‖ = 1) : aeval z p ≠ 0` |
| `partial_fractions` | a94J06 | `{ζ z : ℂ} (hζ : ζ ≠ 0) (hz : z ≠ 0) (hζz : ζ ≠ z) : (ζ * (ζ - z))⁻¹ = z⁻¹ * ((ζ - z)⁻¹ - ζ⁻¹)` |
| `periodic_int_aux` | a93J05 | `{f : ℂ → ℂ} (ω : ℂ) (hper : ∀ z, f (z + ω) = f z) (z : ℂ) : ∀ n : ℤ, f (z + n * ω) = f z` |
| `pointwiseSum_monotone` | a01J03 | `(fns : ℕ → ℝ → ℝ) (hmono : ∀ n, Monotone (fns n)) (hsummable : ∀ x, Summable fun n => fns n x) : Monotone (pointwiseSum fns)` |
| `poisson_translation_average_tendsto_L2` | a94J04 | `{f : ℝ → ℝ} (hf : MemLp f 2 volume) : let τ : ℝ → C(ℝ, ℝ)` |
| `poisson_translation_average_toLp` | a94J04 | `{y : ℝ} (hy : 0 < y) {f : ℝ → ℝ} (hf : MemLp f 2 volume) : let τ : ℝ → C(ℝ, ℝ)` |
| `poissonConv_aestronglyMeasurable` | a94J04 | `(y : ℝ) (hy : 0 < y) (f : ℝ → ℝ) (hfm : AEStronglyMeasurable f volume) : AEStronglyMeasurable (poissonConv y f) volume` |
| `poissonConv_eq_integral_translation` | a94J04 | `(y : ℝ) (f : ℝ → ℝ) (x : ℝ) : poissonConv y f x = ∫ t, poissonKernel y t * f (x - t) ∂volume` |
| `poissonConv_eq_integral_unitKernel` | a94J04 | `{y : ℝ} (hy : 0 < y) (f : ℝ → ℝ) (x : ℝ) : poissonConv y f x = ∫ z, poissonKernel 1 z * f (x - y * z) ∂volume` |
| `poissonConv_L2_contraction` | a94J04 | `(y : ℝ) (hy : 0 < y) (f : ℝ → ℝ) (hf : MemLp f 2 volume) : eLpNorm (poissonConv y f) 2 volume ≤ eLpNorm f 2 volume` |
| `poissonConv_memLp` | a94J04 | `(y : ℝ) (hy : 0 < y) (f : ℝ → ℝ) (hf : MemLp f 2 volume) : MemLp (poissonConv y f) 2 volume` |
| `poissonConv_tendsto_ae` | a94J04 | `(f : ℝ → ℝ) (hf : MemLp f 2 volume) (hfm : AEStronglyMeasurable f volume) : ∀ᵐ x ∂volume, Tendsto (fun y => poissonConv y f x) (nhdsWithin 0 (Ioi 0)) (𝓝 (f x))` |
| `poissonConv_tendsto_ae_of_memLp` | LIB: ConstructionTargets.RadialMajorantAE | `{f : ℝ → ℝ} (hf : MemLp f 2 volume) : ∀ᵐ x ∂volume, Tendsto (fun y => ∫ t, poissonKernel y t * f (x - t) ∂volume) (𝓝[>] 0) (𝓝 (f x))` |
| `poissonConv_tendsto_at_of_memLp` | LIB: ConstructionTargets.RadialMajorantAE | `{f : ℝ → ℝ} (hfm : Measurable f) (hf : MemLp f 2 volume) {x : ℝ} (hx : Tendsto (radialLaverage f x) (𝓝[>] 0) (𝓝 0)) : Tendsto (fun y => ∫ t, poissonKernel y t * f (x - t) ∂volume) (𝓝[>] 0) (𝓝 (f x))` |
| `poissonConv_tendsto_L2` | a94J04 | `(f : ℝ → ℝ) (hf : MemLp f 2 volume) (hfm : AEStronglyMeasurable f volume) : Tendsto (fun y => eLpNorm (fun x => poissonConv y f x - f x) 2 volume) (nhdsWithin 0 (Ioi 0)) (𝓝 0)` |
| `poissonKernel_dilation` | LIB: ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) (t : ℝ) : poissonKernel y t = y⁻¹ * poissonKernel 1 (t / y)` |
| `poissonKernel_even` | LIB: ConstructionTargets.RadialMajorantAE | `(y t : ℝ) : poissonKernel y (-t) = poissonKernel y t` |
| `poissonKernel_hasDerivAt` | LIB: ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) (s : ℝ) : HasDerivAt (poissonKernel y) (-poissonLayerWeight y s) s` |
| `poissonKernel_inner_nonneg` | a94J04 | `(y : ℝ) (hy : 0 < y) (x : ℝ) : 0 ≤ y / (y ^ 2 + x ^ 2)` |
| `poissonKernel_integrable` | LIB: ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) : Integrable (poissonKernel y) volume` |
| `poissonKernel_integrable` | a94J04 | `(y : ℝ) (hy : 0 < y) : Integrable (poissonKernel y) volume` |
| `poissonKernel_integral` | LIB: ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) : ∫ t : ℝ, poissonKernel y t ∂volume = 1` |
| `poissonKernel_integral_Ioo` | a94J04 | `(y : ℝ) (hy : 0 < y) (δ : ℝ) (hδ : 0 < δ) : ∫ t in Ioo (-δ) δ, poissonKernel y t ∂volume = (1 / π) * (arctan (δ / y) - arctan (-δ / y))` |
| `poissonKernel_integral_one` | a94J04 | `(y : ℝ) (hy : 0 < y) : ∫ x, poissonKernel y x ∂volume = 1` |
| `poissonKernel_nonneg` | LIB: ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) (t : ℝ) : 0 ≤ poissonKernel y t` |
| `poissonKernel_nonneg` | a94J04 | `(y : ℝ) (hy : 0 < y) (x : ℝ) : 0 ≤ poissonKernel y x` |
| `poissonKernel_one_abs_mono` | LIB: ConstructionTargets.RadialMajorantAE | `{s t : ℝ} (hst : \|s\| ≤ \|t\|) : poissonKernel 1 t ≤ poissonKernel 1 s` |
| `poissonKernel_one_antitoneOn` | LIB: ConstructionTargets.RadialMajorantAE | `: AntitoneOn (poissonKernel 1) (Ici 0)` |
| `poissonKernel_one_integral` | LIB: ConstructionTargets.RadialMajorantAE | `: ∫ t : ℝ, poissonKernel 1 t ∂volume = 1` |
| `poissonKernel_scale` | a94J04 | `{y : ℝ} (hy : 0 < y) (z : ℝ) : y * poissonKernel y (y * z) = poissonKernel 1 z` |
| `poissonKernel_sub_star` | LIB: ConstructionTargets.HerglotzRigidity | `{w z : ℂ} (hzw : ‖w‖ < ‖z‖) : poissonKernel 0 w z - poissonKernel 0 w (star z) = (‖z‖ ^ 2 - ‖w‖ ^ 2) * (4 * z.im * w.im) / (‖z - w‖ ^ 2 * ‖star z - w‖ ^ 2)` |
| `poissonKernel_sub_star_ge` | LIB: ConstructionTargets.HerglotzRigidity | `{R : ℝ} {w z : ℂ} (hR : 1 < R) (hz : ‖z‖ = R) ( hw : ‖w‖ ≤ 1) (hwi : 0 ≤ w.im) (hzi : 0 ≤ z.im) : (R ^ 2 - ‖w‖ ^ 2) * (4 * z.im * w.im) / (R + 1) ^ 4 ≤ poissonKernel 0 w z - poissonKernel 0 w (star z)` |
| `poissonKernel_sub_star_le` | LIB: ConstructionTargets.HerglotzRigidity | `{R : ℝ} {w z : ℂ} (hR : 0 < R) (hz : ‖z‖ = R) (hw : ‖w‖ ≤ R / 2) (hwi : 0 ≤ w.im) (hzi : 0 ≤ z.im) : 0 ≤ poissonKernel 0 w z - poissonKernel 0 w (star z) ∧ poissonKernel 0 w z - poissonKernel 0 w (star z) ≤ 64 * w.im * z.im / R ^ 2` |
| `poissonKernel_tail_tendsto` | a94J04 | `(δ : ℝ) (hδ : 0 < δ) : Tendsto (fun y => ∫ t in {t \| δ ≤ \|t\|}, poissonKernel y t ∂volume) (nhdsWithin 0 (Ioi 0)) (𝓝 0)` |
| `poissonKernel_tendsto_atTop` | LIB: ConstructionTargets.RadialMajorantAE | `{y : ℝ} (_hy : 0 < y) : Tendsto (poissonKernel y) atTop (𝓝 0)` |
| `poissonLayerDensity_eq` | LIB: ConstructionTargets.RadialMajorantAE | `(u : ℝ) : poissonLayerDensity u = 4 * u ^ 2 / (π * (1 + u ^ 2) ^ 2)` |
| `poissonLayerDensity_integrable` | LIB: ConstructionTargets.RadialMajorantAE | `: Integrable poissonLayerDensity volume` |
| `poissonLayerDensity_lintegral_ne_top` | LIB: ConstructionTargets.RadialMajorantAE | `: (∫⁻ u, ENNReal.ofReal (poissonLayerDensity u) ∂volume) ≠ ∞` |
| `poissonLayerDensity_nonneg` | LIB: ConstructionTargets.RadialMajorantAE | `(u : ℝ) : 0 ≤ poissonLayerDensity u` |
| `poissonLayerWeight_nonneg` | LIB: ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ poissonLayerWeight y s` |
| `poissonLayerWeight_scale` | LIB: ConstructionTargets.RadialMajorantAE | `{y : ℝ} (hy : 0 < y) (u : ℝ) : y * poissonLayerWeight y (y * u) * (2 * (y * u)) = poissonLayerDensity u` |
| `polynomial_eval_mono_of_coeff_nonneg` | a96A04 | `{p : Polynomial ℝ} (hp : ∀ i, 0 ≤ p.coeff i) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : p.eval x ≤ p.eval y` |
| `polynomial_eval_nonneg_of_coeff_nonneg` | a96A04 | `{p : Polynomial ℝ} (hp : ∀ i, 0 ≤ p.coeff i) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ p.eval x` |
| `polynomial_map_image_null` | a03J02 | `{n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} (hf : IsPolynomialMap f) {E : Set (Fin n → ℝ)} (hE : volume E = 0) : volume (f '' E) = 0` |
| `polynomialAbsCoeff_coeff_nonneg` | a96A04 | `(p : Polynomial ℝ) (n : ℕ) : 0 ≤ (polynomialAbsCoeff p).coeff n` |
| `pos_quad` | a94A06 | `(u : ℝ) : 0 < u^2 - u + 1` |
| `positive_convolution_exists` | a96J02 | `(A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) (hAint : Integrable (indicator A (1 : ℝ → ℝ)) volume) (hBint : Integrable (indicator B (1 : ℝ → ℝ)) volume) (hApos : 0 < volume A) (hBpos : 0 < volume B) (hAfin : volume A ≠ ∞) (hBfin : volume B ≠ ∞) : ∃ x : ℝ, 0 < ((indicator A (1 : ℝ → ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (indicator B (1 : ℝ → ℝ))) x` |
| `posSlitPlane_ne_zero` | a02J07 | `{z : ℂ} (hz : z ∈ posSlitPlane) : z ≠ 0` |
| `pow_half_pos` | a96J01 | `(n : ℕ) : 0 < (2 : ℝ)⁻¹ ^ n` |
| `proj_idempotent` | m96J01 | `(V : ClosedSubmodule ℝ H) : (proj V).comp (proj V) = proj V` |
| `proj_isSelfAdjoint` | m96J01 | `(V : ClosedSubmodule ℝ H) : IsSelfAdjoint (proj V)` |
| `proj_linear` | m96J01 | `(V : ClosedSubmodule ℝ H) : (proj V 0 = 0) ∧ (∀ x y, proj V (x + y) = proj V x + proj V y) ∧ (∀ r : ℝ, ∀ x, proj V (r • x) = r • proj V x)` |
| `proj_norm_one` | m96J01 | `(V : ClosedSubmodule ℝ H) (hV : (V : Submodule ℝ H) ≠ ⊥) : ‖proj V‖ = 1` |
| `projection_properties` | m96J01 | `(V : ClosedSubmodule ℝ H) (hV : (V : Submodule ℝ H) ≠ ⊥) : let F` |
| `quadratic_bound` | a02J06 | `(data : SchwarzData) {z : ℂ} (hz : z ∈ unitDisk) : ‖data.f z‖ ≤ ‖z‖ ^ 2` |
| `quadratic_factor` | a92J06 | `(z : ℂ) : z ^ 2 + 4 * z + 1 = (z - ((-2 : ℂ) + (sqrt 3 : ℂ))) * (z - ((-2 : ℂ) - (sqrt 3 : ℂ)))` |
| `quadraticQuotient_continuousAt_zero` | a94J08 | `(f : ℂ → ℂ) (hbound : ∀ z : ℂ, ‖z‖ ^ ((3 : ℝ) / 2) ≤ ‖f z‖) : ContinuousAt (quadraticQuotient f) 0` |
| `quadraticQuotient_differentiable` | a94J08 | `(f : ℂ → ℂ) (hf_diff : Differentiable ℂ f) (hbound : ∀ z : ℂ, ‖z‖ ^ ((3 : ℝ) / 2) ≤ ‖f z‖) : Differentiable ℂ (quadraticQuotient f)` |
| `quantile_le_iff` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) {a y : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (f 0) (f 1)) : quantile f y ≤ a ↔ y ≤ f a` |
| `quantile_maps` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) {y : ℝ} (hy : y ∈ Icc (f 0) (f 1)) : f (quantile f y) = y` |
| `quantile_mem_Ioc_iff` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) {a b y : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (f 0) (f 1)) : quantile f y ∈ Ioc a b ↔ y ∈ Ioc (f a) (f b)` |
| `quantile_mem_unit` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) {y : ℝ} (hy : y ∈ Icc (f 0) (f 1)) : quantile f y ∈ Icc (0 : ℝ) 1` |
| `quantileMeasure_Iic` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) (a : ℝ) : quantileMeasure f (Iic a) = ENNReal.ofReal (monotoneExtension f a - f 0)` |
| `quantileMeasure_Ioc` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) : quantileMeasure f (Ioc a b) = ENNReal.ofReal (f b - f a)` |
| `quasiNorm_antitone` | a96A01 | `{f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 1) volume) {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) : quasiNorm f p ≤ quasiNorm f q` |
| `quasiNorm_eq_lpNorm` | a96A01 | `{f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 1) volume) {p : ℝ} (hp : 0 < p) : quasiNorm f p = lpNorm f (ENNReal.ofReal p) (volume.restrict (Icc 0 1))` |
| `quasiNorm_tendsto_exists` | a96A01 | `{f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 1) volume) : ∃ L : ℝ, Tendsto (quasiNorm f) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)` |
| `radial_integral_R3` | LIB: ConstructionTargets.RadialIntegrationR3 | `{g : ℝ → ℝ} (_hg : Integrable (fun x : E => g ‖x‖) volume) : ∫ x : E, g ‖x‖ ∂volume = 4 * π * ∫ r in Ioi (0 : ℝ), g r * r ^ 2 ∂volume` |
| `radial_integral_R3` | a95A03 | `{g : ℝ → ℝ} (hg : Integrable (fun x : E => g ‖x‖) volume) : ∫ x : E, g ‖x‖ ∂volume = 4 * π * ∫ r in Ioi (0:ℝ), g r * r ^ 2 ∂volume` |
| `radialLaverage_le_of_memLp` | LIB: ConstructionTargets.RadialMajorantAE | `{f : ℝ → ℝ} (hf : MemLp f 2 volume) (x : ℝ) {δ s : ℝ} (hδ : 0 < δ) (hδs : δ ≤ s) : radialLaverage f x s ≤ 1 + (∫⁻ z, ‖f z‖ₑ ^ (2 : ℕ) ∂volume) / ENNReal.ofReal (2 * δ) + ENNReal.ofReal \|f x\|` |
| `radialLaverage_measurable` | LIB: ConstructionTargets.RadialMajorantAE | `(f : ℝ → ℝ) (x : ℝ) : Measurable (radialLaverage f x)` |
| `radialLIntegral_eq_lintegral_closedBall` | LIB: ConstructionTargets.RadialMajorantAE | `(f : ℝ → ℝ) (x s : ℝ) : radialLIntegral f x s = ∫⁻ z in Metric.closedBall x s, ‖f z - f x‖ₑ ∂volume` |
| `radialLIntegral_measurable` | LIB: ConstructionTargets.RadialMajorantAE | `(f : ℝ → ℝ) (x : ℝ) : Measurable (radialLIntegral f x)` |
| `radialLIntegral_monotone` | LIB: ConstructionTargets.RadialMajorantAE | `(f : ℝ → ℝ) (x : ℝ) : Monotone (radialLIntegral f x)` |
| `radius_gt_one_of_summable` | a00J06 | `(ha : ∀ n, 0 ≤ a n) {ε : ℝ} (he : 0 < ε) (h : Summable fun n => a n * (1 + ε) ^ n) : (1 : ENNReal) < (p a).radius` |
| `radius_gt_one_of_summable_aux` | a00J06 | `(ha : ∀ n, 0 ≤ a n) {ε : ℝ} (he : 0 < ε) (h : Summable fun n => a n * (1 + ε) ^ n) : (1 : ENNReal) < (p a).radius` |
| `radon_riesz` | a02J02 | `{p : ℝ} (hp1 : 1 < p) {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (hf : ∀ n, MemLp (f n) (ENNReal.ofReal p) (volume.restrict (Icc 0 1))) (hg : MemLp g (ENNReal.ofReal p) (volume.restrict (Icc 0 1))) (hae : ∀ᵐ x ∂(volume.restrict (Icc 0 1)), Tendsto (fun n => f n x) atTop (nhds (g x))) (hnorm : Tendsto (fun n => eLpNorm (f n) (ENNReal.ofReal p) (volume.restrict (Icc 0 1))) atTop (nhds (eLpNorm g (ENNReal.ofReal p) (volume.restrict (Icc 0 1))))) : Tendsto (fun n => eLpNorm (f n - g) (ENNReal.ofReal p) (volume.restrict (Icc 0 1))) atTop (nhds 0)` |
| `range_inter_quantile_preimage_Iic` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) : Icc (f 0) (f 1) ∩ quantile f ⁻¹' Iic a = Icc (f 0) (f a)` |
| `range_inter_quantile_preimage_Ioc` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) : Icc (f 0) (f 1) ∩ quantile f ⁻¹' Ioc a b = Ioc (f a) (f b)` |
| `rational_angle_factorial_pow_eq_one` | a95A06 | `(θ : ℚ) {n : ℕ} (hn : θ.den ≤ n) : circleMap 0 1 (2 * Real.pi * (θ : ℝ)) ^ n.factorial = 1` |
| `riemann_lebesgue_sandwich` | a95A01 | `(f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∃ M, ∀ x ∈ Icc (0:ℝ) 1, \|f x\| ≤ M) : (lowerRiemannIntegral f ≤ ∫ x in Icc (0:ℝ) 1, f x ∂volume) ∧ (∫ x in Icc (0:ℝ) 1, f x ∂volume ≤ upperRiemannIntegral f)` |
| `rigidity` | a02J06 | `(data : SchwarzData) {w : ℂ} (hw : w ∈ unitDisk) (hne : w ≠ 0) (heq : ‖data.f w‖ = ‖w‖ ^ 2) : ∃ β : ℂ, ‖β‖ = 1 ∧ ∀ z ∈ unitDisk, data.f z = β * z ^ 2` |
| `roots_inside_add_outside` | a92J05 | `: p.roots.filter (fun z => ‖z‖ < 1) + p.roots.filter (fun z => 1 < ‖z‖) = p.roots` |
| `roots_outside_card_eq_of_inside_card_eq` | a92J05 | `(hinside : (p.roots.filter (fun z => ‖z‖ < 1)).card = 3) : (p.roots.filter (fun z => 1 < ‖z‖)).card = 7` |
| `roots_outside_unit_disk` | a92J05 | `: (p.roots.filter (fun z => 1 < ‖z‖)).card = 7` |
| `rouche_condition` | a92J05 | `(z : ℂ) (hz : ‖z‖ = 1) : ‖aeval z h‖ < ‖aeval z g‖` |
| `rouche_deriv_bound` | a94J07 | `{z : ℂ} (hz : ‖z‖ = 1) : ‖cexp z + 3 * z ^ 2‖ < 8` |
| `rouche_f_bound` | a94J07 | `{z : ℂ} (hz : ‖z‖ = 1) : ‖cexp z + z ^ 3‖ < ‖(8 : ℂ) * z‖` |
| `rouche_homotopy_analyticOnNhd` | LIB: ConstructionTargets.Rouche | `{f g : ℂ → ℂ} {s : Set ℂ} (hf : AnalyticOnNhd ℂ f s) (hg : AnalyticOnNhd ℂ g s) (t : ℝ) : AnalyticOnNhd ℂ (fun z ↦ f z + (t : ℂ) * g z) s` |
| `rouche_homotopy_analyticOnNhd_and_ne_zero` | LIB: ConstructionTargets.Rouche | `{f g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hfg : ∀ z ∈ sphere c R, ‖g z‖ < ‖f z‖) (t : Set.Icc (0 : ℝ) 1) : AnalyticOnNhd ℂ (fun z ↦ f z + (t.1 : ℂ) * g z) (closedBall c R) ∧ ∀ z ∈ sphere c R, f z + (t.1 : ℂ) * g z ≠ 0` |
| `rouche_homotopy_ne_zero_on_circle` | a92J05 | `(t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (z : ℂ) (hz : ‖z‖ = 1) : aeval z g + (t : ℂ) * aeval z h ≠ 0` |
| `rouche_homotopy_ne_zero_on_sphere` | LIB: ConstructionTargets.Rouche | `{f g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hfg : ∀ z ∈ sphere c R, ‖g z‖ < ‖f z‖) : ∀ t : Set.Icc (0 : ℝ) 1, ∀ z ∈ sphere c R, f z + (t.1 : ℂ) * g z ≠ 0` |
| `rpow_le_one_add` | a96A01 | `{t : ℝ} (ht : 0 ≤ t) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) : t ^ p ≤ 1 + t` |
| `rpow_sub_le` | a02J02 | `{p : ℝ} (hp : 1 ≤ p) (a b : ℝ) : \|a - b\| ^ p ≤ 2 ^ (p - 1) * (\|a\| ^ p + \|b\| ^ p)` |
| `rpow_sub_one_div_posPart_le` | a96A01 | `{t p : ℝ} (ht : 0 ≤ t) (hp : 0 < p) (hp1 : p ≤ 1) : ((t ^ p - 1) / p)⁺ ≤ t` |
| `scaled_integral_vanishes` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ) (hM : 0 < M) (hφloc : LocallyIntegrable φ volume) (hφ : ∀ (a b : ℝ), a < b → \|∫ x in Set.Icc a b, φ x\| ≤ M * (b - a) / (1 + (b - a))) (f : ℝ → ℝ) (hf : Integrable f volume) : Tendsto (fun k : ℝ => scaledIntOp φ f k) atTop (nhds 0)` |
| `scaled_integral_vanishes_of_compact_continuous` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ) (hM : 0 < M) (hφloc : LocallyIntegrable φ volume) (hφ : ∀ (a b : ℝ), a < b → \|∫ x in Set.Icc a b, φ x\| ≤ M * (b - a) / (1 + (b - a))) (hcore : ∀ (g : ℝ → ℝ), HasCompactSupport g → Continuous g → Integrable g volume → Tendsto (fun k : ℝ => scaledIntOp φ g k) atTop (nhds 0)) (f : ℝ → ℝ) (hf : Integrable f volume) : Tendsto (fun k : ℝ => scaledIntOp φ f k) atTop (nhds 0)` |
| `scaled_integral_vanishes_of_compact_smooth` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ) (hM : 0 < M) (hφloc : LocallyIntegrable φ volume) (hφ : ∀ (a b : ℝ), a < b → \|∫ x in Set.Icc a b, φ x\| ≤ M * (b - a) / (1 + (b - a))) (g : ℝ → ℝ) (hg_support : HasCompactSupport g) (hg_smooth : ContDiff ℝ ∞ g) : Tendsto (fun k : ℝ => scaledIntOp φ g k) atTop (nhds 0)` |
| `scaled_intervalIntegral_bound` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ) (hφ : ∀ (a b : ℝ), a < b → \|∫ x in Set.Icc a b, φ x\| ≤ M * (b - a) / (1 + (b - a))) (a b : ℝ) (k : ℝ) (hk : 0 < k) : \|∫ x in a..b, φ (k * x)\| ≤ M * \|b - a\| / (1 + k * \|b - a\|)` |
| `scaled_intervalIntegral_bound_div` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hφ : ∀ (a b : ℝ), a < b → \|∫ x in Set.Icc a b, φ x\| ≤ M * (b - a) / (1 + (b - a))) (a b : ℝ) (k : ℝ) (hk : 0 < k) : \|∫ x in a..b, φ (k * x)\| ≤ M / k` |
| `scaled_setIntegral_bound` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ) (hφ : ∀ (a b : ℝ), a < b → \|∫ x in Set.Icc a b, φ x\| ≤ M * (b - a) / (1 + (b - a))) (a b : ℝ) (hab : a < b) (k : ℝ) (hk : 0 < k) : \|∫ x in Set.Icc a b, φ (k * x)\| ≤ M * (b - a) / (1 + k * (b - a))` |
| `schur_fubini` | a02J01 | `(k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (u : (Fin d → ℝ) → ℝ) (hk_meas : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => k p.1 p.2)) (hcol_int : ∀ᵐ y ∂volume, Integrable (fun x => ‖k x y‖) volume) (hcol : ∀ᵐ y ∂volume, ∫ x, ‖k x y‖ ≤ 1) (hu : MemLp u 2 volume) : ∫ x, (∫ y, ‖k x y‖ * (u y) ^ 2) ≤ ∫ y, (u y) ^ 2` |
| `schur_pointwise` | a02J01 | `(k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (u : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (hrow_int : Integrable (fun y => ‖k x y‖) volume) (hweighted_int : Integrable (fun y => ‖k x y‖ * (u y) ^ 2) volume) (hrow : ∫ y, ‖k x y‖ ≤ 1) : (integralOp k u x) ^ 2 ≤ ∫ y, ‖k x y‖ * (u y) ^ 2` |
| `schur_test` | a02J01 | `(k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (hk_meas : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => k p.1 p.2)) (hrow_int : ∀ᵐ x ∂volume, Integrable (fun y => ‖k x y‖) volume) (hcol_int : ∀ᵐ y ∂volume, Integrable (fun x => ‖k x y‖) volume) (hrow : ∀ᵐ x ∂volume, ∫ y, ‖k x y‖ ≤ 1) (hcol : ∀ᵐ y ∂volume, ∫ x, ‖k x y‖ ≤ 1) (u : (Fin d → ℝ) → ℝ) (hu : MemLp u 2 volume) : eLpNorm (integralOp k u) 2 volume ≤ eLpNorm u 2 volume` |
| `schur_weight_integrable` | a02J01 | `(k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (u : (Fin d → ℝ) → ℝ) (hk_meas : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => k p.1 p.2)) (hcol_int : ∀ᵐ y ∂volume, Integrable (fun x => ‖k x y‖) volume) (hcol : ∀ᵐ y ∂volume, ∫ x, ‖k x y‖ ≤ 1) (hu : MemLp u 2 volume) : Integrable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => ‖k p.1 p.2‖ * (u p.2) ^ 2) (volume.prod volume)` |
| `schwarz_deriv_bound` | a95J01 | `{h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball 0 1)) (hh_maps : MapsTo h (ball 0 1) (ball 0 1)) (hh_zero : h 0 = 0) : ‖deriv h 0‖ ≤ 1` |
| `schwarz_equality` | a95J01 | `{h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball 0 1)) (hh_maps : MapsTo h (ball 0 1) (ball 0 1)) (hh_zero : h 0 = 0) (heq : ‖deriv h 0‖ = 1) : ∃ α : ℝ, ∀ z ∈ ball (0 : ℂ) 1, h z = exp (I * ↑α) * z` |
| `schwarz_second_order_bound` | a93J06 | `{f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1)) (hf0 : f 0 = 0) (hf'0 : deriv f 0 = 0) (hbound : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖deriv f z‖ ≤ 1) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) : ‖f z‖ ≤ ‖z‖ ^ 2 / 2` |
| `second_deriv_bound` | a02J06 | `(data : SchwarzData) : ‖deriv (deriv data.f) 0‖ ≤ 2` |
| `separate_closed_sets` | t94A02 | `{A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B) (hdisj : Disjoint A B) : ∃ f : ℝ → ℝ, Continuous f ∧ f '' Set.univ ⊆ Set.Icc (0 : ℝ) 1 ∧ f ⁻¹' {0} = A ∧ f ⁻¹' {1} = B` |
| `sepFun_den_ne_zero` | t94A02 | `{A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B) (hdisj : Disjoint A B) (x : ℝ) : distTo A x + distTo B x ≠ 0` |
| `sepFun_eq_one_iff` | t94A02 | `{A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B) (hdisj : Disjoint A B) (x : ℝ) : sepFun A B x = 1 ↔ x ∈ B` |
| `sepFun_eq_zero_iff` | t94A02 | `{A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B) (hdisj : Disjoint A B) (x : ℝ) : sepFun A B x = 0 ↔ x ∈ A` |
| `sepFun_mem_Icc` | t94A02 | `{A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B) (hdisj : Disjoint A B) (x : ℝ) : sepFun A B x ∈ Set.Icc (0 : ℝ) 1` |
| `setIntegralCLM_apply` | LIB: ConstructionTargets.LpRepresentative | `{X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ENNReal} [Fact (1 ≤ p)] (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (f : Lp ℝ p μ) : setIntegralCLM s hs hμs f = ∫ x in s, f x ∂μ` |
| `singular_at_one` | a00J06 | `(ha : ∀ n, 0 ≤ a n) (h_radius : (p a).radius = 1) : ¬ ∃ ρ : ℝ, 0 < ρ ∧ AnalyticAt ℝ (f a) 1` |
| `solves_problem` | a02J06 | `(data : SchwarzData) : (∀ z ∈ unitDisk, ‖data.f z‖ ≤ ‖z‖ ^ 2) ∧ ‖deriv (deriv data.f) 0‖ ≤ 2 ∧ (∀ ⦃w : ℂ⦄, w ∈ unitDisk → w ≠ 0 → ‖data.f w‖ = ‖w‖ ^ 2 → ∃ β : ℂ, ‖β‖ = 1 ∧ ∀ z ∈ unitDisk, data.f z = β * z ^ 2)` |
| `spike_base_length` | a96A02 | `(n : ℕ) (hn : 0 < n) : 1 / ↑n - 1 / (↑n + 1 : ℝ) = 1 / (↑n * (↑n + 1))` |
| `spike_height_slope_bound` | a96A02 | `(n : ℕ) (hn : 0 < n) : (1 / (↑n : ℝ)) * (2 * (↑n + 1)) ≤ 4` |
| `spike_lipschitz` | a96A02 | `{f : ℝ → ℝ} (hf : SpikeFunctionSpec f) (n : ℕ) (hn : 0 < n) {x y : ℝ} (hx : x ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) (hy : y ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) : \|f x - f y\| ≤ 2 * ((n : ℝ) + 1) * \|x - y\|` |
| `spike_nonneg` | a01J01 | `(n : ℕ) (x : ℝ) : 0 ≤ spike n x` |
| `spike_value_bounds` | a96A02 | `{f : ℝ → ℝ} (hf : SpikeFunctionSpec f) (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : x ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) : 0 ≤ f x ∧ f x ≤ 1 / (n : ℝ)` |
| `spikeFunction_at_left` | a96A02 | `(n : ℕ) (hn : 0 < n) : spikeFunction (1 / ((n : ℝ) + 1)) = 0` |
| `spikeFunction_holderWith` | a96A02 | `: SpikeFunctionSpec spikeFunction → ∃ A : ℝ, 0 < A ∧ ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, \|spikeFunction x - spikeFunction y\| ≤ A * \|x - y\| ^ ((1:ℝ) / 2)` |
| `spikeFunction_not_absolutelyContinuous` | a96A02 | `: SpikeFunctionSpec spikeFunction → ∃ ε > 0, ∀ δ > 0, ∃ (n : ℕ) (a b : Fin n → ℝ), (∀ i, a i ∈ Icc 0 1) ∧ (∀ i, b i ∈ Icc 0 1) ∧ (∀ i, a i ≤ b i) ∧ (∀ i j, i < j → b i ≤ a j) ∧ ∑ i, (b i - a i) < δ ∧ ε ≤ ∑ i, \|spikeFunction (b i) - spikeFunction (a i)\|` |
| `spikeFunction_spec` | a96A02 | `: SpikeFunctionSpec spikeFunction` |
| `SpikeFunctionSpec.at_inv_nat` | a96A02 | `{f : ℝ → ℝ} (hf : SpikeFunctionSpec f) (n : ℕ) (hn : 0 < n) : f (1 / (n : ℝ)) = 0` |
| `SpikeFunctionSpec.at_midpoint` | a96A02 | `{f : ℝ → ℝ} (hf : SpikeFunctionSpec f) (n : ℕ) (hn : 0 < n) : f (spikeMidpoint n) = 1 / (n : ℝ)` |
| `spikeIndex_at_left` | a96A02 | `(n : ℕ) (hn : 0 < n) : spikeIndex (1 / ((n : ℝ) + 1)) = n + 1` |
| `spikeIndex_eq_of_mem_of_ne_left` | a96A02 | `(n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))) (hne : x ≠ 1 / ((n : ℝ) + 1)) : spikeIndex x = n` |
| `spikeMidpoint_mem` | a96A02 | `(n : ℕ) (hn : 0 < n) : spikeMidpoint n ∈ Icc (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))` |
| `spikeWidth_le_one` | a01J01 | `(n : ℕ) : spikeWidth n ≤ 1` |
| `sq_integral_le` | a02J01 | `{α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℝ) : (∫ x, f x ∂μ) ^ 2 ≤ (∫ x, ‖f x‖ ∂μ) ^ 2` |
| `sq_sqrt3` | a94A06 | `: (Real.sqrt 3 : ℝ)^2 = 3` |
| `sq_sqrt_three_complex` | a92J06 | `: (sqrt 3 : ℂ) ^ 2 = 3` |
| `sqrt_three_gt_one` | a92J06 | `: 1 < sqrt 3` |
| `stieltjesFunction_monotoneExtension_eq` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) (x : ℝ) : (monotone_monotoneExtension hf_mono).stieltjesFunction x = monotoneExtension f x` |
| `stieltjesMeasure_absolutelyContinuous_of_maps_null` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) (hf_N : ∀ E ⊆ Icc (0 : ℝ) 1, volume E = 0 → volume (f '' E) = 0) : stieltjesMeasure f hf_mono ≪ volume` |
| `stieltjesMeasure_compl_Icc` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) : stieltjesMeasure f hf_mono (Icc (0 : ℝ) 1)ᶜ = 0` |
| `stieltjesMeasure_eq_quantileMeasure` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) : stieltjesMeasure f hf_mono = quantileMeasure f` |
| `stieltjesMeasure_Iic` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) (a : ℝ) : stieltjesMeasure f hf_mono (Iic a) = ENNReal.ofReal (monotoneExtension f a - f 0)` |
| `stieltjesMeasure_Ioc` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) : stieltjesMeasure f hf_mono (Ioc a b) = ENNReal.ofReal (f b - f a)` |
| `stieltjesMeasure_Ioc_eq_volume_image_Icc` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b) : stieltjesMeasure f hf_mono (Ioc a b) = volume (f '' Icc a b)` |
| `stieltjesMeasure_isFinite` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) : IsFiniteMeasure (stieltjesMeasure f hf_mono)` |
| `stieltjesMeasure_le_volume_image` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) {E : Set ℝ} (hE : MeasurableSet E) (hE_sub : E ⊆ Icc (0 : ℝ) 1) : stieltjesMeasure f hf_mono E ≤ volume (f '' E)` |
| `stieltjesMeasure_singleton` | LIB: ConstructionTargets.BanachZarecki | `{f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) (x : ℝ) : stieltjesMeasure f hf_mono {x} = 0` |
| `subordination_deriv_eq` | a95J01 | `{f g : ℂ → ℂ} (hf_holo : DifferentiableOn ℂ f (ball 0 1)) (hg_holo : DifferentiableOn ℂ g (ball 0 1)) (hf_inj : InjOn f (ball 0 1)) (hg_inj : InjOn g (ball 0 1)) (hfg_zero : f 0 = g 0) (hfg_sub : f '' ball 0 1 ⊆ g '' ball 0 1) (heq : ‖deriv f 0‖ = ‖deriv g 0‖) (hg_ne : deriv g 0 ≠ 0) : ∃ α : ℝ, ∀ z ∈ ball (0 : ℂ) 1, f z = g (exp (I * ↑α) * z)` |
| `subordination_deriv_le` | a95J01 | `{f g : ℂ → ℂ} (hf_holo : DifferentiableOn ℂ f (ball 0 1)) (hg_holo : DifferentiableOn ℂ g (ball 0 1)) (hf_inj : InjOn f (ball 0 1)) (hg_inj : InjOn g (ball 0 1)) (hfg_zero : f 0 = g 0) (hfg_sub : f '' ball 0 1 ⊆ g '' ball 0 1) : ‖deriv f 0‖ ≤ ‖deriv g 0‖` |
| `subordination_deriv_le_of_deriv_ne_zero` | a95J01 | `{f g : ℂ → ℂ} (hf_holo : DifferentiableOn ℂ f (ball 0 1)) (hg_holo : DifferentiableOn ℂ g (ball 0 1)) (hg_inj : InjOn g (ball 0 1)) (hfg_zero : f 0 = g 0) (hfg_sub : f '' ball 0 1 ⊆ g '' ball 0 1) (hg_deriv : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0) : ‖deriv f 0‖ ≤ ‖deriv g 0‖` |
| `sum_edist_le_eVariationOn_of_mem_disjWithin` | a93A04 | `{g : ℝ → ℝ} {n : ℕ} {I : ℕ → ℝ × ℝ} (hE : (n, I) ∈ AbsolutelyContinuousOnInterval.disjWithin (0 : ℝ) 1) : (∑ i ∈ Finset.range n, edist (g (I i).1) (g (I i).2)) ≤ eVariationOn g (uIcc (0 : ℝ) 1)` |
| `sum_inv_sq_eq_pi_sq_div_six` | a95A07 | `: HasSum (fun n : ℕ => 1 / (↑(n + 1) : ℝ) ^ 2) (π ^ 2 / 6)` |
| `sum_setIntegral_partition` | a95A01 | `(f : ℝ → ℝ) (n : ℕ) (t : Fin (n + 2) → ℝ) (ht : ∀ i : Fin (n + 1), t i.castSucc < t i.succ) (hf : IntegrableOn f (Icc (t 0) (t (Fin.last (n + 1)))) volume) : ∑ i : Fin (n + 1), ∫ x in Icc (t i.castSucc) (t i.succ), f x ∂volume = ∫ x in Icc (t 0) (t (Fin.last (n + 1))), f x ∂volume` |
| `summable_inv_sq` | a95A07 | `: Summable (fun n : ℕ => 1 / (↑(n + 1) : ℝ) ^ 2)` |
| `summable_lacunary_deriv_terms_of_norm_lt_one` | a95A06 | `{w : ℂ} (hw0 : 0 < ‖w‖) (hw1 : ‖w‖ < 1) : Summable (fun n : ℕ => w ^ (n.factorial - 1))` |
| `summable_lacunaryTerm_of_mem_closedBall` | a95A06 | `{z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) : Summable (fun n => lacunaryTerm n z)` |
| `sup_inv_sub_polynomial_ge_one` | a96A05 | `(P : Polynomial ℂ) : 1 ≤ ⨆ z ∈ sphere (0 : ℂ) 1, ‖z⁻¹ - Polynomial.aeval z P‖` |
| `surjective_surfaceQuotient` | LIB: ConstructionTargets.Surfaces | `(orientable : Bool) (genus : ℕ) : Function.Surjective (surfaceQuotient orientable genus)` |
| `symmetric_split` | a95A04 | `{f : ℝ → ℝ} (hsym : SymmetricMeanValue f) {a b : ℝ} (hab : a < b) (h_sub : Icc a b ⊆ Icc (0:ℝ) 1) (hf_int : IntervalIntegrable f volume a b) : ∫ t in a..((a + b) / 2), f t = (1 / 2 : ℝ) * ∫ t in a..b, f t` |
| `t91A08_timesFive_homotopic_of_g_homotopic` | t91A08 | `(h : ContinuousMap.Homotopic t91A08g (ContinuousMap.id T91A08Torus)) : ContinuousMap.Homotopic t91A08TimesFive (ContinuousMap.id UnitAddCircle)` |
| `t91A08_timesFive_isAddQuotientCoveringMap` | t91A08 | `: IsAddQuotientCoveringMap (5 • · : UnitAddCircle → UnitAddCircle) (nsmulAddMonoidHom (α` |
| `t91A08_timesFive_not_injective` | t91A08 | `: ¬Function.Injective (5 • · : UnitAddCircle → UnitAddCircle)` |
| `t91A08Cover_surjective` | t91A08 | `: Function.Surjective t91A08Cover` |
| `t91A08Integral_induced` | t91A08 | `(beta : T91A08Form2) (hbeta : t91A08IsInduced beta) : t91A08Integral beta = 3` |
| `t91A08Integral_pullback` | t91A08 | `(beta gamma : T91A08Form2) (hbeta : t91A08IsInduced beta) (hgamma : t91A08IsPullback gamma beta) : t91A08Integral gamma = 21` |
| `t93A02H.cauchySeq_toCloseds` | t93A02 | `{X : Type*} [MetricSpace X] (A : ℕ → t93A02H X) (hA : IsT93A02HausdorffCauchy A) : CauchySeq (fun n => (A n).toCloseds)` |
| `t93A02H.edist_toCloseds_eq_ofReal_hausdorffDist` | t93A02 | `{X : Type*} [MetricSpace X] (A B : t93A02H X) : edist A.toCloseds B.toCloseds = ENNReal.ofReal (Metric.hausdorffDist A.1 B.1)` |
| `t93A02H.exists_closeds_limit` | t93A02 | `{X : Type*} [MetricSpace X] [CompleteSpace X] (A : ℕ → t93A02H X) (hA : IsT93A02HausdorffCauchy A) : ∃ L : TopologicalSpace.Closeds X, Tendsto (fun n => (A n).toCloseds) atTop (nhds L)` |
| `t93A02H.hausdorffEDist_ne_top` | t93A02 | `{X : Type*} [PseudoMetricSpace X] (A B : t93A02H X) : Metric.hausdorffEDist A.1 B.1 ≠ ⊤` |
| `t94J07_integral_deriv_eq_zero_of_periodic` | t94J07 | `(q : ℝ → ℝ) (hq : ContDiff ℝ 1 q) (hperiod : q (2 * Real.pi) = q 0) : ∫ θ in (0 : ℝ)..2 * Real.pi, deriv q θ = 0` |
| `t94J07CirclePoint_norm` | t94J07 | `(θ : ℝ) : ‖t94J07CirclePoint θ‖ = 1` |
| `t94J07CirclePoint_two_pi` | t94J07 | `: t94J07CirclePoint (2 * Real.pi) = t94J07CirclePoint 0` |
| `t94J07CircleVelocity_tangent` | t94J07 | `(θ : ℝ) : inner ℝ (t94J07CirclePoint θ) (t94J07CircleVelocity θ) = 0` |
| `t94J07CircleVelocity_two_pi` | t94J07 | `: t94J07CircleVelocity (2 * Real.pi) = t94J07CircleVelocity 0` |
| `t94J07HomotopySliceIntegrand_two_pi` | t94J07 | `(alpha : T94J07Form1) (H : T94J07E2 × ℝ → T94J07E2) (t : ℝ) : t94J07PullbackCircleIntegrand alpha (fun x ↦ H (x, t)) (2 * Real.pi) = t94J07PullbackCircleIntegrand alpha (fun x ↦ H (x, t)) 0` |
| `t94J07PullbackCircleIntegrand_two_pi` | t94J07 | `(alpha : T94J07Form1) (f : T94J07E2 → T94J07E2) : t94J07PullbackCircleIntegrand alpha f (2 * Real.pi) = t94J07PullbackCircleIntegrand alpha f 0` |
| `t94J08Antipodal_comp_self` | t94J08 | `{k : ℕ} : (t94J08Antipodal : C(T94J08Sphere k, T94J08Sphere k)).comp t94J08Antipodal = ContinuousMap.id _` |
| `t94J08Antipodal_ne_self` | t94J08 | `{k : ℕ} (x : T94J08Sphere k) : t94J08Antipodal x ≠ x` |
| `t94J08HasDegree.comp` | t94J08 | `{n : ℕ} {g h : C(T94J08Sphere (n + 1), T94J08Sphere (n + 1))} {m d : ℤ} (hg : t94J08HasDegree n g m) (hh : t94J08HasDegree n h d) : t94J08HasDegree n (g.comp h) (m * d)` |
| `t94J08HasDegree_with_orientation` | t94J08 | `{n : ℕ} {f : C(T94J08Sphere (n + 1), T94J08Sphere (n + 1))} {d : ℤ} (h : t94J08HasDegree n f d) (orientation : T94J08TopHomology n ≅ ModuleCat.of ℤ ℤ) : ∀ a : T94J08TopHomology n, orientation.hom (t94J08TopHomologyMap n f a) = d * orientation.hom a` |
| `t94J08NormalizedLink_neg` | t94J08 | `{m : ℕ} (v : T94J08Euclidean (m + 1) → T94J08Euclidean (m + 1)) (p : T94J08Euclidean (m + 1)) (r : ℝ) (hlink : ∀ x : T94J08Sphere (m + 1), v (p + r • x.1) ≠ 0) (hlinkNeg : ∀ x : T94J08Sphere (m + 1), (-v (p + r • x.1)) ≠ 0) (x : T94J08Sphere (m + 1)) : t94J08NormalizedLink (fun y ↦ -v y) p r hlinkNeg x = t94J08Antipodal (t94J08NormalizedLink v p r hlink x)` |
| `t95J02CollapseARaw_continuous` | t95J02 | `: Continuous t95J02CollapseARaw` |
| `t95J02CollapseARaw_eqvGen` | t95J02 | `{p q : ℝ × ℝ} (h : Relation.EqvGen t95J02KleinRel p q) : t95J02CollapseARaw p = t95J02CollapseARaw q` |
| `t95J02CollapseARaw_generator` | t95J02 | `{p q : ℝ × ℝ} (h : t95J02KleinRel p q) : t95J02CollapseARaw p = t95J02CollapseARaw q` |
| `t95J02QuotientPoint_glide` | t95J02 | `(x y : ℝ) : t95J02QuotientPoint (x, y) = t95J02QuotientPoint (x + 1, -y)` |
| `t95J02QuotientPoint_glide_twice` | t95J02 | `(x y : ℝ) : t95J02QuotientPoint (x, y) = t95J02QuotientPoint (x + 2, y)` |
| `t95J02QuotientPoint_glide_vertical_inverse` | t95J02 | `(x y : ℝ) : t95J02QuotientPoint (x, y + 1) = t95J02QuotientPoint (x + 1, -y - 1)` |
| `t95J02QuotientPoint_vertical` | t95J02 | `(x y : ℝ) : t95J02QuotientPoint (x, y) = t95J02QuotientPoint (x, y + 1)` |
| `t95J02RetractionA_comp_inclusion` | t95J02 | `: t95J02InclusionA ≫ t95J02RetractionA = 𝟙 t95J02CircleA` |
| `t95J04_contractibleSpace_sphere_complement` | t95J04 | `(n : ℕ) (q : T95J04Sphere n) : ContractibleSpace {y : T95J04Sphere n // y ≠ q}` |
| `t95J04_nullHomotopic_of_not_surjective` | t95J04 | `{X : Type*} [TopologicalSpace X] (n : ℕ) (f : X → T95J04Sphere n) (hf : Continuous f) (hnot_surj : ¬ Function.Surjective f) : t95J04NullHomotopic f hf` |
| `t95J04_sphere_nonempty` | t95J04 | `(n : ℕ) : Nonempty (T95J04Sphere n)` |
| `t95J04_sphereSix_nonempty` | t95J04 | `: Nonempty T95J04SphereSix` |
| `t95J04_sphereThreeThree_nonempty` | t95J04 | `: Nonempty T95J04SphereThreeThree` |
| `t95J04_sphereTwoFour_nonempty` | t95J04 | `: Nonempty T95J04SphereTwoFour` |
| `t95J05_existsUnique_projectiveThreeForm` | t95J05 | `: ∃! η : T95J05ProjectiveThreeForm, t95J05ProjectionPullback η = t95J05InclusionPullback` |
| `t95J05_hausdorffIntegral_eq_zero_of_isometry_odd` | t95J05 | `{X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (d : ℝ) (e : X ≃ᵢ X) (f : X → ℝ) (hodd : ∀ x, f (e x) = -f x) : (∫ x, f x ∂Measure.hausdorffMeasure d) = 0` |
| `t95J05InclusionPullback_antipodal` | t95J05 | `(x : t95J05SphereThree) : t95J05InclusionPullback (t95J05Antipode x) = t95J05InclusionPullback x` |
| `t95J05InclusionPullback_expand` | t95J05 | `(x : t95J05SphereThree) : t95J05InclusionPullback x = x.1 1 ^ 3 * x.1 0 - 4 * x.1 0 ^ 2` |
| `t95J05Integral_eq_neg_pi_sq_of_sphereIntegral` | t95J05 | `(η : T95J05ProjectiveThreeForm) (hη : t95J05ProjectionPullback η = t95J05InclusionPullback) (hsphere : (∫ x, t95J05InclusionPullback x ∂Measure.hausdorffMeasure 3) = -2 * Real.pi ^ 2) : t95J05Integral η = -Real.pi ^ 2` |
| `t95J05Integral_eq_sphereIntegral` | t95J05 | `(η : T95J05ProjectiveThreeForm) (hη : t95J05ProjectionPullback η = t95J05InclusionPullback) : t95J05Integral η = (1 / 2 : ℝ) * ∫ x, t95J05InclusionPullback x ∂Measure.hausdorffMeasure 3` |
| `t97A04HasHomologicalData.of_maps` | t97A04 | `(h0 : T97A04Homology 0 ≅ ModuleCat.of ℤ ℤ) (h1 : T97A04Homology 1 ≅ ModuleCat.of ℤ apm_t97a04_IntPlane) (h2 : T97A04Homology 2 ≅ ModuleCat.of ℤ ℤ) (H0 : ∀ a : T97A04Homology 0, h0.hom (t97A04HomologyMap 0 apm_t97a04_Lbar a) = h0.hom a) (H1 : ∀ a : T97A04Homology 1, h1.hom (t97A04HomologyMap 1 apm_t97a04_Lbar a) = apm_t97a04_matrix.mulVec (h1.hom a)) (H2 : ∀ a : T97A04Homology 2, h2.hom (t97A04HomologyMap 2 apm_t97a04_Lbar a) = 3 * h2.hom a) : t97A04HasHomologicalData apm_t97a04_Lbar apm_t97a04_matrix 3 1` |
| `t97A04HomologyMap_comp` | t97A04 | `(k : ℕ) (g f : C(apm_t97a04_Torus, apm_t97a04_Torus)) : t97A04HomologyMap k (g.comp f) = t97A04HomologyMap k f ≫ t97A04HomologyMap k g` |
| `t97A04HomologyMap_id` | t97A04 | `(k : ℕ) : t97A04HomologyMap k (ContinuousMap.id apm_t97a04_Torus) = 𝟙 _` |
| `t97J06_circle_identity_homotopic_of_map_homotopic_const` | t97J06 | `(q : T97J06Torus) (h : ContinuousMap.Homotopic t97J06Map (ContinuousMap.const T97J06Torus q)) : ContinuousMap.Homotopic (ContinuousMap.id Circle) (ContinuousMap.const Circle q.2)` |
| `t97J06_contractibleCircle_of_map_homotopic_const` | t97J06 | `(q : T97J06Torus) (h : ContinuousMap.Homotopic t97J06Map (ContinuousMap.const T97J06Torus q)) : ContractibleSpace Circle` |
| `t97J06_determinant_integral_zero` | t97J06 | `: (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, Matrix.det !![2 * Real.pi * Real.cos (2 * Real.pi * x + 4 * Real.pi * y), 4 * Real.pi * Real.cos (2 * Real.pi * x + 4 * Real.pi * y); (1 : ℝ), 1]) = 0` |
| `t97J06_not_homotopic_const_of_not_contractibleCircle` | t97J06 | `(hCircle : ¬ ContractibleSpace Circle) : ∀ q : T97J06Torus, ¬ ContinuousMap.Homotopic t97J06Map (ContinuousMap.const T97J06Torus q)` |
| `t97J06Map_on_cover` | t97J06 | `(x y : ℝ) : t97J06Map (Circle.exp (2 * Real.pi * x), Circle.exp (2 * Real.pi * y)) = (Circle.exp (2 * Real.pi * Real.sin (2 * Real.pi * x + 4 * Real.pi * y)), Circle.exp (2 * Real.pi * (x + y)))` |
| `t97J07IsolatedPoint_not_mem` | t97J07 | `: t97J07IsolatedPoint ∉ t97J07FixedLine` |
| `t97J07LineChart_map` | t97J07 | `(a u : ℂ) : t97J07Map (t97J07LineChart a u) = t97J07LineChart a (t97J07LineLocal u)` |
| `t97J07LineContribution_eq` | t97J07 | `: t97J07LineContribution = 2` |
| `t97J07LineIndex_eq` | t97J07 | `: t97J07IndexFromDet t97J07LineNormalDet = 1` |
| `t97J07LineLocal_fderiv` | t97J07 | `: fderiv ℂ t97J07LineLocal 0 1 = 3` |
| `t97J07LineNormalDet_eq` | t97J07 | `: t97J07LineNormalDet = 4` |
| `t97J07PointChart_map` | t97J07 | `(w : Fin 2 → ℂ) : t97J07Map (t97J07PointChart w) = t97J07PointChart (t97J07PointLocal w)` |
| `t97J07PointDet_eq` | t97J07 | `: t97J07PointDet = (16 : ℝ) / 81` |
| `t97J07PointIndex_eq` | t97J07 | `: t97J07IndexFromDet t97J07PointDet = 1` |
| `t97J07PointLocal_fderiv` | t97J07 | `(i : Fin 2) : fderiv ℂ t97J07PointLocal 0 (Pi.single i 1) = Pi.single i (1 / 3)` |
| `t97J07TotalContribution_eq` | t97J07 | `: t97J07LineContribution + t97J07IndexFromDet t97J07PointDet = 3` |
| `t97J08_norm_normalizedLoop` | t97J08 | `{f : ℝ → ℂ} (hf : ∀ t, f t ≠ 0) (t : ℝ) : ‖t97J08NormalizedLoop f t‖ = 1` |
| `t97J08_normalizedLoop_periodic` | t97J08 | `{f : ℝ → ℂ} (hf : ∀ t, f (t + 2 * Real.pi) = f t) (t : ℝ) : t97J08NormalizedLoop f (t + 2 * Real.pi) = t97J08NormalizedLoop f t` |
| `t97J08_sqRadius_ne_zero` | t97J08 | `{z : ℂ} (hz : z ≠ 0) : z.re ^ 2 + z.im ^ 2 ≠ 0` |
| `t97J08Beta_differentiableAt_coordinates` | t97J08 | `(z : ℂ) (hz : z ≠ 0) : DifferentiableAt ℝ (fun w : ℂ ↦ t97J08Beta w 1) z ∧ DifferentiableAt ℝ (fun w : ℂ ↦ t97J08Beta w Complex.I) z` |
| `t98A01_circleFive_isAddQuotientCoveringMap` | t98A01 | `: IsAddQuotientCoveringMap (5 • · : UnitAddCircle → UnitAddCircle) (nsmulAddMonoidHom (α` |
| `t98A01_circleFive_isCoveringMap` | t98A01 | `: IsCoveringMap (5 • · : UnitAddCircle → UnitAddCircle)` |
| `t98A01_circleFive_surjective` | t98A01 | `: Function.Surjective (5 • · : UnitAddCircle → UnitAddCircle)` |
| `t98A01_orientable_genus_arithmetic` | t98A01 | `(g h : ℕ) (hgh : g = h) (hχ : eulerCharacteristic true g = 5 * eulerCharacteristic true h) : g = 1 ∧ h = 1` |
| `t98A01PrintedSurface_eulerCharacteristic` | t98A01 | `: eulerCharacteristic t98A01PrintedSurfaceData.1 t98A01PrintedSurfaceData.2 = -9` |
| `t98A01PrintedSurface_homeomorph` | t98A01 | `: Nonempty (T98A01PrintedSurface ≃ₜ Surface false 11)` |
| `t98A01PrintedSurfaceData_eq` | t98A01 | `: t98A01PrintedSurfaceData = (false, 11)` |
| `t98A02_boundary_identified` | t98A02 | `{X₁ X₂ : Type} (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) (s : T98A02Sphere) (h₁ : φ₁ (t98A02SphereInDisk s) ∉ φ₁ '' {u : T98A02Disk \| ‖(u : T98A02E4)‖ < 1}) (h₂ : φ₂ (t98A02SphereInDisk s) ∉ φ₂ '' {u : T98A02Disk \| ‖(u : T98A02E4)‖ < 1}) : t98A02_leftInclusion φ₁ φ₂ ⟨φ₁ (t98A02SphereInDisk s), h₁⟩ = t98A02_rightInclusion φ₁ φ₂ ⟨φ₂ (t98A02SphereInDisk s), h₂⟩` |
| `t98A02_continuous_leftInclusion` | t98A02 | `{X₁ X₂ : Type} [TopologicalSpace X₁] [TopologicalSpace X₂] (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) : Continuous (t98A02_leftInclusion φ₁ φ₂)` |
| `t98A02_continuous_quotientMap` | t98A02 | `{X₁ X₂ : Type} [TopologicalSpace X₁] [TopologicalSpace X₂] (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) : Continuous (t98A02QuotientMap φ₁ φ₂)` |
| `t98A02_continuous_rightInclusion` | t98A02 | `{X₁ X₂ : Type} [TopologicalSpace X₁] [TopologicalSpace X₂] (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) : Continuous (t98A02_rightInclusion φ₁ φ₂)` |
| `t98A02_gluedDesc_respects` | t98A02 | `{X₁ X₂ Z : Type} [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Z] (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) (f : C(T98A02Punctured X₁ φ₁, Z)) (g : C(T98A02Punctured X₂ φ₂, Z)) (hfg : ∀ (s : T98A02Sphere) (h₁ : φ₁ (t98A02SphereInDisk s) ∉ φ₁ '' {u : T98A02Disk \| ‖(u : T98A02E4)‖ < 1}) (h₂ : φ₂ (t98A02SphereInDisk s) ∉ φ₂ '' {u : T98A02Disk \| ‖(u : T98A02E4)‖ < 1}), f ⟨φ₁ (t98A02SphereInDisk s), h₁⟩ = g ⟨φ₂ (t98A02SphereInDisk s), h₂⟩) {x y} (hxy : Relation.EqvGen (T98A02GlueRel φ₁ φ₂) x y) : Sum.elim f g x = Sum.elim f g y` |
| `t98A02_gluedDesc_unique` | t98A02 | `{X₁ X₂ Z : Type} [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Z] (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) (f : C(T98A02Punctured X₁ φ₁, Z)) (g : C(T98A02Punctured X₂ φ₂, Z)) (hfg) (u : C(T98A02ConnectedSum φ₁ φ₂, Z)) (hul : ∀ x, u (t98A02_leftInclusion φ₁ φ₂ x) = f x) (hur : ∀ x, u (t98A02_rightInclusion φ₁ φ₂ x) = g x) : u = t98A02_gluedDesc φ₁ φ₂ f g hfg` |
| `t98A02_surjective_quotientMap` | t98A02 | `{X₁ X₂ : Type} (φ₁ : T98A02Disk → X₁) (φ₂ : T98A02Disk → X₂) : Function.Surjective (t98A02QuotientMap φ₁ φ₂)` |
| `tail_integral_tendsto_zero` | a94J01 | `{f : (Fin n → ℝ) → ℝ} (hf : Integrable f volume) : Tendsto (fun M : ℝ => ∫ x in {x \| M < ‖f x‖}, ‖f x‖ ∂volume) atTop (nhds 0)` |
| `tendsto_arctan_one_div_nhdsWithin` | LIB: ConstructionTargets.Sinc | `: Filter.Tendsto (fun a : ℝ => Real.arctan (1 / a)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (π / 2))` |
| `tendsto_argStar_nhdsGT_zero_or_two_pi` | a02J07 | `{γ : ℝ → ℂ} (hγ : SlitPath γ) : Tendsto (fun t => argStar (γ t)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∨ Tendsto (fun t => argStar (γ t)) (𝓝[>] (0 : ℝ)) (𝓝 (2 * π))` |
| `tendsto_argStar_nhdsLT_one` | a02J07 | `{γ : ℝ → ℂ} (hγ : SlitPath γ) : Tendsto (fun t => argStar (γ t)) (𝓝[<] (1 : ℝ)) (𝓝 (argStar (γ 1)))` |
| `tendsto_bound_zero` | a02J03 | `(M c : ℝ) (hc : 0 < c) : Tendsto (fun k : ℝ => M * c / (1 + k * c)) atTop (nhds 0)` |
| `tendsto_damped_fresnel_closed_form` | a01A10 | `: Filter.Tendsto (fun ε : ℝ => ((π : ℂ) / ((ε : ℂ) - I)) ^ (1 / 2 : ℂ) / 2) (𝓝[>] 0) (𝓝 ((1 + I) * √π / (2 * √2)))` |
| `tendsto_eLpNorm_atTop` | a93J04 | `{α : Type*} [MeasurableSpace α] {f : α → ℝ} {μ : Measure α} (hf : AEStronglyMeasurable f μ) (hf_bdd : eLpNorm f ⊤ μ ≠ ⊤) (hμ_fin : μ Set.univ < ⊤) : Tendsto (fun p : ℝ => eLpNorm f (ENNReal.ofReal p) μ) atTop (𝓝 (eLpNorm f ⊤ μ))` |
| `tendsto_eLpNorm_indicator_sub_iff_tendsto_measure_symmDiff` | a94A01 | `{Eₙ : ℕ → Set ℝ} {E : Set ℝ} (hm : ∀ n, MeasurableSet (Eₙ n)) (hE : MeasurableSet E) {p : ENNReal} (hp : 1 ≤ p) (hp_top : p ≠ ⊤) : Tendsto (fun n => eLpNorm ((Eₙ n).indicator (fun _ => (1 : ℝ)) - E.indicator (fun _ => (1 : ℝ))) p volume) atTop (nhds 0) ↔ Tendsto (fun n => volume (Eₙ n ∆ E)) atTop (nhds 0)` |
| `tendsto_G_atTop` | a94A06 | `: Tendsto G atTop (nhds (Real.sqrt 3 * π / 24))` |
| `tendsto_gamma_nhdsGT_zero` | a02J07 | `{γ : ℝ → ℂ} (hγ : SlitPath γ) : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi : ℂ))` |
| `tendsto_integral_abs_sub_of_nonneg` | a02J02 | `{α : Type*} [MeasurableSpace α] {μ : Measure α} {u : ℕ → α → ℝ} {v : α → ℝ} (hu_int : ∀ n, Integrable (u n) μ) (hv_int : Integrable v μ) (hu_nonneg : ∀ n, 0 ≤ᵐ[μ] u n) (hv_nonneg : 0 ≤ᵐ[μ] v) (huv : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (nhds (v x))) (hint : Tendsto (fun n => ∫ x, u n x ∂μ) atTop (nhds (∫ x, v x ∂μ))) : Tendsto (fun n => ∫ x, \|u n x - v x\| ∂μ) atTop (nhds 0)` |
| `tendsto_integral_damped_fresnel_interval` | a01A10 | `(a : ℝ) : Filter.Tendsto (fun ε : ℝ => ∫ x in (0 : ℝ)..a, cexp (-((ε : ℂ) - I) * (x : ℂ) ^ 2)) (𝓝[>] (0 : ℝ)) (nhds (∫ x in (0 : ℝ)..a, cexp (I * (x : ℂ) ^ 2)))` |
| `tendsto_integral_exp_neg_mul_sinc_nhdsWithin` | LIB: ConstructionTargets.Sinc | `{L : ℝ} (hL : Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sinc x) Filter.atTop (nhds L)) : Filter.Tendsto (fun a : ℝ => ∫ x in Set.Ioi (0 : ℝ), Real.exp (-a * x) * Real.sinc x) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)` |
| `tendsto_integral_sinc_pi_div_two` | LIB: ConstructionTargets.Sinc | `: Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sinc x) Filter.atTop (nhds (π / 2))` |
| `tendsto_intervalIntegral_exp_neg_mul_sinc` | LIB: ConstructionTargets.Sinc | `{A : ℝ} (hA : 0 < A) : Filter.Tendsto (fun a : ℝ => ∫ x in (0 : ℝ)..A, Real.exp (-a * x) * Real.sinc x) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (∫ x in (0 : ℝ)..A, Real.sinc x))` |
| `tendsto_lintegral_poissonLayerDensity_mul` | LIB: ConstructionTargets.RadialMajorantAE | `{A : ℝ → ℝ≥0∞} (hA : Measurable A) {C : ℝ≥0∞} (hC : C ≠ ∞) (hbound : ∀ s, A s ≤ C) (hzero : ∀ u, Tendsto (fun y : ℝ => A (y * u)) (𝓝[>] 0) (𝓝 0)) : Tendsto (fun y : ℝ => ∫⁻ u, ENNReal.ofReal (poissonLayerDensity u) * A (y * u) ∂volume) (𝓝[>] 0) (𝓝 0)` |
| `tendsto_measure_rpow_one_div` | a93J04 | `{m : ℝ≥0∞} (hm₀ : m ≠ 0) (hm_top : m ≠ ⊤) : Tendsto (fun p : ℝ => m ^ (1 / (ENNReal.ofReal p).toReal)) atTop (𝓝 1)` |
| `tendsto_monotoneExtension_atBot` | LIB: ConstructionTargets.BanachZarecki | `(f : ℝ → ℝ) : Filter.Tendsto (monotoneExtension f) Filter.atBot (nhds (f 0))` |
| `tendsto_norm_reciprocal_zero` | a03J08 | `{α : Type*} {l : Filter α} {f : α → ℂ} (w₀ : ℂ) (hf : Tendsto (fun z => ‖f z‖) l atTop) : Tendsto (fun z => ‖(f z - w₀)⁻¹‖) l (𝓝 0)` |
| `tendsto_norm_sub_atTop` | a03J08 | `{α : Type*} {l : Filter α} {f : α → ℂ} (w₀ : ℂ) (hf : Tendsto (fun z => ‖f z‖) l atTop) : Tendsto (fun z => ‖f z - w₀‖) l atTop` |
| `tendsto_of_L1ConvergesOnDisks_at` | a01A07 | `{f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : ∀ n, DifferentiableOn ℂ (f n) U) (hF : ContinuousOn F U) (hconv : L1ConvergesOnDisks f F U) {x : ℂ} (hx : x ∈ U) : Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))` |
| `tendsto_radialLaverage_mul` | LIB: ConstructionTargets.RadialMajorantAE | `{f : ℝ → ℝ} {x : ℝ} (hx : Tendsto (radialLaverage f x) (𝓝[>] 0) (𝓝 0)) (u : ℝ) : Tendsto (fun y : ℝ => radialLaverage f x (y * u)) (𝓝[>] 0) (𝓝 0)` |
| `tendsto_rpow_inv_nat_atTop` | a00J01 | `(t : ℝ) (ht : 0 < t) : Tendsto (fun n : ℕ => t ^ (1 / (n : ℝ))) atTop (𝓝 1)` |
| `tendsto_scaled_primitive_bound_zero` | a02J03 | `(M : ℝ) : Tendsto (fun k : ℝ => M / k) atTop (nhds 0)` |
| `tendsto_setIntegral_Icc_zero` | LIB: ConstructionTargets.SetIntegralPrimitive | `(g : ℝ → ℝ) (hg : IntegrableOn g (Icc (0 : ℝ) 1) volume) : Tendsto (fun x => ∫ t in Icc (0 : ℝ) x, g t ∂volume) (nhdsWithin 0 (Ioi 0)) (nhds 0)` |
| `tendsto_setIntegral_Icc_zero` | a00J02 | `(g : ℝ → ℝ) (hg_nn : 0 ≤ g) (hg : IntegrableOn g (Icc (0 : ℝ) 1) volume) : Tendsto (fun x => ∫ t in Icc (0 : ℝ) x, g t ∂volume) (nhdsWithin 0 (Ioi 0)) (nhds 0)` |
| `tendsto_setIntegral_of_indicator_limit` | a94A01 | `{Eₙ : ℕ → Set ℝ} {E : Set ℝ} (hm : ∀ n, MeasurableSet (Eₙ n)) (hE : MeasurableSet E) (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => (Eₙ n).indicator (fun _ => (1 : ℝ)) x) atTop (nhds (E.indicator (fun _ => (1 : ℝ)) x))) {g : ℝ → ℝ} (hg : Integrable g volume) : Tendsto (fun n => ∫ x in Eₙ n, g x ∂volume) atTop (nhds (∫ x in E, g x ∂volume))` |
| `tendsto_sum_alternating_harmonic` | a93J02 | `: Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / (↑i + 1)) atTop (𝓝 (log 2))` |
| `tendstoInMeasure.convergesInMeasure` | a92J02 | `{f : ℕ → α → ℝ} {g : α → ℝ} (htm : TendstoInMeasure μ f atTop g) : ConvergesInMeasure (μ` |
| `tendstoInMeasure_iff_integral_arctan` | a95J05 | `{f : ℕ → Ω → ℝ} (hf : ∀ n, Measurable (f n)) : TendstoInMeasureZero f μ ↔ Tendsto (fun n => ∫ x, \|arctan (f n x)\| ∂μ) atTop (𝓝 0)` |
| `tendstoInMeasure_of_integral_arctan_tendsto` | a95J05 | `{f : ℕ → Ω → ℝ} (hf : ∀ n, Measurable (f n)) (hint : Tendsto (fun n => ∫ x, \|arctan (f n x)\| ∂μ) atTop (𝓝 0)) : TendstoInMeasureZero f μ` |
| `tendstoInMeasureZero_iff_tendstoInMeasure` | a95J05 | `{f : ℕ → Ω → ℝ} : TendstoInMeasureZero f μ ↔ TendstoInMeasure μ f atTop 0` |
| `tendstoUniformlyOn_deriv_of_L1` | a01A07 | `{f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} (hΩ : IsOpen Ω) (hf : ∀ n, DifferentiableOn ℂ (f n) Ω) (hF : ContinuousOn F Ω) (hconv : L1ConvergesOnDisks f F Ω) {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) : TendstoUniformlyOn (fun n z => deriv (f n) z) (deriv F) atTop K` |
| `tendstoUniformlyOn_of_L1_on_disks` | a01A07 | `{f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} (hΩ : IsOpen Ω) (hf : ∀ n, DifferentiableOn ℂ (f n) Ω) (hF : ContinuousOn F Ω) (hconv : L1ConvergesOnDisks f F Ω) {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) : TendstoUniformlyOn f F atTop K` |
| `tensorMulRepresentation_finrank_ker` | b95J03 | `(F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] : Module.finrank F (tensorMulRepresentation F E).ker = (Module.finrank F E) ^ 2 - Module.finrank F E` |
| `tensorMulRepresentation_finrank_ker_of_finrank_eq` | b95J03 | `(F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (n : ℕ) (hfin : Module.finrank F E = n) : Module.finrank F (tensorMulRepresentation F E).ker = n ^ 2 - n` |
| `test_function_admissible` | a01A06 | `{E : Set ℝ} (hE : MeasurableSet E) (hEsub : E ⊆ Icc (0 : ℝ) 1) {c : ℝ} (hc : 0 < c) (hδpos : 0 < μ E) (hδfin : μ E < ⊤) : let δ` |
| `toLp_integral_eq_integral` | LIB: ConstructionTargets.LpRepresentative | `{Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X] {ν : Measure Y} {μ : Measure X} [SFinite ν] [SFinite μ] {p : ENNReal} [Fact (1 ≤ p)] (hp_top : p ≠ ∞) {φ : Y × X → ℝ} (hφ : AEStronglyMeasurable φ (ν.prod μ)) {F : Y → Lp ℝ p μ} (hF : Integrable F ν) (hFφ : ∀ᵐ y ∂ν, (F y : X → ℝ) =ᵐ[μ] fun x => φ (y, x)) (hφ_local : ∀ s : Set X, MeasurableSet s → μ s ≠ ∞ → HasFiniteIntegral (fun z : Y × X => s.indicator (fun x => φ (z.1, x)) z.2) (ν.prod μ)) (hψ : MemLp (fun x => ∫ y, φ (y, x) ∂ν) p μ) : hψ.toLp (fun x => ∫ y, φ (y, x) ∂ν) = ∫ y, F y ∂ν` |
| `totally_bounded_complete_compact` | t95A03 | `(X : Type*) [PseudoMetricSpace X] [CompleteSpace X] (h : TotallyBounded (Set.univ : Set X)) : CompactSpace X` |
| `translation_symmDiff_tendsto_zero` | a96J02 | `(B : Set ℝ) (hB : MeasurableSet B) (hBfin : volume B ≠ ∞) (x : ℝ) : Tendsto (fun y => volume (((subtractionMap y) ⁻¹' B) ∆ ((subtractionMap x) ⁻¹' B))) (𝓝 x) (𝓝 0)` |
| `tsum_alternating_harmonic_mul_pow` | a93J02 | `{x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) : ∑' n : ℕ, ((-1 : ℝ) ^ n / (↑n + 1)) * x ^ n = log (1 + x) / x` |
| `tsum_inv_sq` | a95A07 | `: ∑' n : ℕ, 1 / (↑(n + 1) : ℝ) ^ 2 = π ^ 2 / 6` |
| `tsum_volume_disjoint_le_one` | a95J07 | `{S : ℕ → Set ℝ} (hS_sub : ∀ k, S k ⊆ Ioo 0 1) (hS_meas : ∀ k, NullMeasurableSet (S k) volume) (hS_disj : Pairwise (Function.onFun Disjoint S)) : ∑' k, volume (S k) ≤ 1` |
| `two_le_analyticOrderAt_sub_self` | LIB: ConstructionTargets.UnivalentDeriv | `{g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z) (hderiv : deriv g z = 0) : (2 : ℕ) ≤ analyticOrderAt (fun w => g w - g z) z` |
| `two_pole_contour_eval` | a96J07 | `(f : ℂ → ℂ) (hf : Differentiable ℂ f) (a b : ℂ) (hab : a ≠ b) (R : ℝ) (hR : 0 < R) (haR : ‖a‖ < R) (hbR : ‖b‖ < R) : (∮ z in C((0 : ℂ), R), f z / ((z - a) * (z - b))) = 2 * π * I * (f a - f b) / (a - b)` |
| `two_pole_ml_bound_at_zero` | a96J07 | `(f : ℂ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ z : ℂ, ‖f z‖ ≤ M) (a : ℂ) (R : ℝ) (hR : 0 < R) (haR : ‖a‖ < R) : ‖(2 * π * I : ℂ)⁻¹ • (∮ z in C((0 : ℂ), R), f z / ((z - a) * (z - 0)))‖ ≤ M / (R - ‖a‖)` |
| `unifCont_iff_diffQuot` | a93A01 | `(f : ℝ → ℝ) : UnifContOn01 f ↔ DiffQuotientCondition f` |
| `unifCont_implies_diffQuot` | a93A01 | `{f : ℝ → ℝ} (hf : UnifContOn01 f) : DiffQuotientCondition f` |
| `unifContOn01_bounded` | a93A01 | `{f : ℝ → ℝ} (hf : UnifContOn01 f) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ I01, \|f x\| ≤ B` |
| `unifContOn01_imp` | a93A01 | `(f : ℝ → ℝ) (hf : UnifContOn01 f) : UniformContinuousOn f I01` |
| `uniform_bound` | a02J03 | `(φ : ℝ → ℝ) (M : ℝ) (hφloc : LocallyIntegrable φ volume) (hφ : ∀ (a b : ℝ), a < b → \|∫ x in Set.Icc a b, φ x\| ≤ M * (b - a) / (1 + (b - a))) (f : ℝ → ℝ) (hf : Integrable f volume) (k : ℝ) (hk : 0 < k) : \|scaledIntOp φ f k\| ≤ M * ∫ x, ‖f x‖` |
| `uniform_small_set_of_L3_bound` | a01J01 | `(f : ℕ → ℝ → ℝ) (hmeas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict unitInterval)) (hL3 : ∀ n, eLpNorm (f n) 3 (volume.restrict unitInterval) ≤ 1) : uniformSmallSetProperty f` |
| `uniformCauchySeqOn_closedBall_half` | a01A07 | `{f : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {U : Set ℂ} (hf : ∀ n, DifferentiableOn ℂ (f n) U) (hF : ContinuousOn F U) (hconv : L1ConvergesOnDisks f F U) {x : ℂ} {R : ℝ} (hR : 0 < R) (hRU : closedBall x R ⊆ U) : UniformCauchySeqOn f atTop (closedBall x (R / 2))` |
| `union` | a95J06 | `{f : ℝ → ℝ} {s t : Set ℝ} (hs : LusinConditionN f s) (ht : LusinConditionN f t) : LusinConditionN f (s ∪ t)` |
| `unitParam_eq_circleIntegral` | LIB: ConstructionTargets.CircleParam | `(R : ℝ) (g : ℂ → ℂ) (hg : ContinuousOn g (Metric.sphere 0 \|R\|)) : (∫ t in (0 : ℝ)..1, g (R * Complex.exp (2 * π * I * t)) * deriv (fun u : ℝ ↦ R * Complex.exp (2 * π * I * u)) t) = ∮ z in C(0, R), g z` |
| `upper_bound` | a00J01 | `{f : ℝ → ℝ} {p : ℝ≥0∞} (_hp : 1 ≤ p) (_hp_top : p ≠ ⊤) (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 1))) : eLpNorm f p (volume.restrict (Icc 0 1)) ≤ eLpNorm f ⊤ (volume.restrict (Icc 0 1))` |
| `upperSemicircle_weighted_integral_le` | LIB: ConstructionTargets.HerglotzRigidity | `{f : ℂ → ℂ} (hf : Differentiable ℂ f) (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (hpos : ∀ z : ℂ, 0 < z.im → 0 < (f z).im) {R : ℝ} (hR : 2 ≤ R) : (∫ θ in (0 : ℝ)..Real.pi, (circleMap 0 R θ).im * (f (circleMap 0 R θ)).im) ≤ 4 * Real.pi * (f I).im * R ^ 2` |
| `vitali_covering_5` | a95J07 | `{A : Set (Set ℝ)} (hA : ∀ I ∈ A, ∃ a b, a < b ∧ I = Ioo a b) (hA_sub : ∀ I ∈ A, I ⊆ Ioo 0 1) : ∃ S : ℕ → Set ℝ, (∀ k, S k ∈ A ∨ S k = ∅) ∧ Pairwise (Function.onFun Disjoint S) ∧ ⋃₀ A ⊆ ⋃ k, {y : ℝ \| ∃ a b, S k = Ioo a b ∧ y ∈ inflate5 a b}` |
| `vitali_covering_lemma_5` | a94A05 | `{ι : Type*} (t : Set ι) (c : ι → ℝ) (ρ : ι → ℝ) (R : ℝ) (hρ_bdd : ∀ a ∈ t, ρ a ≤ R) : ∃ u ⊆ t, (u.PairwiseDisjoint fun a => closedBall (c a) (ρ a)) ∧ ⋃ a ∈ t, closedBall (c a) (ρ a) ⊆ ⋃ a ∈ u, closedBall (c a) (5 * ρ a)` |
| `volume_closedBall_toReal` | a01A07 | `{z₀ : ℂ} {r : ℝ} (hr : 0 < r) : (volume (closedBall z₀ r)).toReal = Real.pi * r ^ 2` |
| `weak_convergence_of_ae_tendsto_L2_bounded` | a96A03 | `{f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (hf_meas : ∀ n, AEStronglyMeasurable (f n) volume) (hg_meas : AEStronglyMeasurable g volume) (hf_bdd : ∀ n, eLpNorm (f n) 2 volume ≤ 1) (hae : ∀ᵐ x ∂volume, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {h : ℝ → ℝ} (hh : MemLp h 2 volume) : Tendsto (fun n => ∫ x, f n x * h x ∂volume) atTop (𝓝 (∫ x, g x * h x ∂volume))` |
| `weakL2_implies_L1_bound` | a01A02 | `(f : α → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 < C) (hweak : ∀ t : ℝ, 0 < t → volume {x : α \| t < \|f x\|} ≤ ENNReal.ofReal (C / t ^ 2)) : ∃ C₁ : ℝ, ∀ (E : Set α), MeasurableSet E → 0 < (volume E).toReal → (volume E) < ⊤ → ∫ x in E, \|f x\| ≤ C₁ * Real.sqrt (volume E).toReal` |
| `width_eq` | a96J01 | `(n : ℕ) : b n - a n = (2 : ℝ)⁻¹ ^ (n + 1)` |
| `young_convolution_inequality` | LIB: ConstructionTargets.YoungConvolution | `{f g : ℝ → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hf : Integrable f volume) (hg : MemLp g p volume) : eLpNorm (convolution f g) p volume ≤ eLpNorm f 1 volume * eLpNorm g p volume` |
| `young_convolution_inequality` | a95J08 | `{f g : ℝ → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hf : Integrable f volume) (hg : MemLp g p volume) : eLpNorm (convolution f g) p volume ≤ eLpNorm f 1 volume * eLpNorm g p volume` |
| `young_convolution_inequality_one` | LIB: ConstructionTargets.YoungConvolution | `{f g : ℝ → ℝ} (hf : Integrable f volume) (hg : MemLp g 1 volume) : eLpNorm (convolution f g) 1 volume ≤ eLpNorm f 1 volume * eLpNorm g 1 volume` |
| `young_inequality_L1_L2` | a95A03 | `(φ : E → ℝ) (hφ : Integrable φ volume) (g : E → ℝ) (hg : MemLp g 2 volume) : eLpNorm (fun x => ∫ y, φ (x - y) * g y ∂volume) 2 volume ≤ eLpNorm φ 1 volume * eLpNorm g 2 volume` |
| `z1_norm_lt_one` | a92J06 | `: ‖((-2 : ℂ) + (sqrt 3 : ℂ))‖ < 1` |
| `z2_norm_gt_one` | a92J06 | `: 1 < ‖((-2 : ℂ) - (sqrt 3 : ℂ))‖` |
| `zero_of_orthogonal_to_monomials` | a94A04 | `{f : ℝ → ℝ} {μ : Measure ℝ} [IsFiniteMeasure (μ.restrict (Icc (0 : ℝ) 1))] (hf : MemLp f 2 (μ.restrict (Icc (0:ℝ) 1))) (hfm : AEStronglyMeasurable f (μ.restrict (Icc (0:ℝ) 1))) (horth : ∀ n : ℕ, ∫ x in Icc (0:ℝ) 1, x ^ n * f x ∂μ = 0) : f =ᵐ[μ.restrict (Icc (0:ℝ) 1)] 0` |
| `zero_only_at_origin` | a95J02 | `{f : ℂ → ℂ} {lam : ℝ} (hlam : 0 < lam) (hbound : ∀ z : ℂ, ‖z‖ ^ lam ≤ ‖f z‖) : ∀ z : ℂ, z ≠ 0 → f z ≠ 0` |
| `zeroCountInClosedBall_add_eq` | LIB: ConstructionTargets.Rouche | `{f g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hfg : ∀ z ∈ sphere c R, ‖g z‖ < ‖f z‖) : zeroCountInClosedBall (f + g) c R = zeroCountInClosedBall f c R` |
| `zeroCountInClosedBall_aeval_eq_card_filter` | a92J05 | `(q : ℂ[X]) (hq : q.Monic) (c : ℂ) (R : ℝ) : ConstructionTargets.Rouche.zeroCountInClosedBall (fun z ↦ aeval z q) c R = (q.roots.filter (fun z ↦ dist z c ≤ R)).card` |
| `zeroCountInClosedBall_aeval_eq_card_filter` | a97A08 | `(q : ℂ[X]) (hq : q.Monic) (c : ℂ) (R : ℝ) : ConstructionTargets.Rouche.zeroCountInClosedBall (fun z ↦ aeval z q) c R = (q.roots.filter (fun z ↦ dist z c ≤ R)).card` |
