| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| a95J07 | stronger | Both requested conclusions are stated, and the Vitali theorem also handles the empty collection (the problem assumes it nonempty). | — |
| a95J08 | stronger | The a.e.-integrability and Young inequality are faithful, while part (b) is proved for `1 ≤ p` rather than only `1 < p`. | — |
| a96A01 | faithful | The four declarations encode monotonicity, existence of the right limit, positivity a.e. when `L > 0`, and the geometric-mean bound. | — |
| a96A02 | faithful | The concrete triangular spike is proved to satisfy its exact specification, which is then used for the Hölder and non-AC conclusions. | correction: the bank used the constant-zero placeholder, making its non-AC theorem false; the repair added the exact spike specification, and the later concrete definition discharges it. |
| a96A03 | faithful | The two declarations give membership in the closed `L²` unit ball and convergence against every `L²` test function. | — |
| a96A04 | narrower | The problem asks for the heat kernel on `ℝⁿ`, but the entire encoding specializes to scalar `ℝ` (dimension one). | correction: `ContDiff ℝ ⊤` in the bank meant analytic regularity; changing the order to `∞` correctly states the requested `C^∞` smoothness. |
| a96A05 | faithful | The theorem states exactly the lower bound for every complex polynomial on the unit circle. | — |
| a96A08 | faithful | The Lebesgue integral is proved integrable and equal to `-2π`; values at the two removable singularities are immaterial. | improvement: the bank kept integrability in a separate theorem and its main theorem stated only the integral equality; the current conjunction makes meaningfulness explicit without changing the result. |
| a96J01 | stronger | It constructs the requested example, with each witness continuous on all of `ℝ` rather than merely on `[0,1]`. | — |
| a96J02 | faithful | It states Steinhaus’s conclusion as an explicit nonempty open interval contained in the Minkowski sum. | — |

### a95J07

Graded declarations: `vitali_covering_5` and `measure_image_criticalSet_eq_zero` (there is no `apm_a95J07`). The first says at lines 81–89:

```lean
theorem vitali_covering_5
    {A : Set (Set ℝ)}
    (hA : ∀ I ∈ A, ∃ a b, a < b ∧ I = Ioo a b)
    (hA_sub : ∀ I ∈ A, I ⊆ Ioo 0 1) :
    ∃ S : ℕ → Set ℝ,
      (∀ k, S k ∈ A ∨ S k = ∅) ∧
      Pairwise (Function.onFun Disjoint S) ∧
      ⋃₀ A ⊆ ⋃ k, {y : ℝ | ∃ a b, S k = Ioo a b ∧ y ∈ inflate5 a b} := by
```

This omits the problem’s nonemptiness assumption and hence proves a harmlessly stronger result. The padding by `∅` faithfully represents a possibly finite sequence. The critical-set definition and conclusion at lines 180–190 are:

```lean
def criticalSet (f : ℝ → ℝ) : Set ℝ :=
  {x ∈ Ioo 0 1 | DifferentiableAt ℝ f x ∧ deriv f x = 0}

theorem measure_image_criticalSet_eq_zero
    {f : ℝ → ℝ} :
    volume (f '' criticalSet f) = 0 := by
```

No local axiom, opaque declaration, or sorry occurs. The later null-measurability repair changed only the auxiliary `tsum_volume_disjoint_le_one`, not either graded conclusion.

### a95J08

Graded declarations: `convolution_integrand_integrableAE` and `young_convolution_inequality` (no `apm_a95J08`). Lines 32–39 state:

```lean
theorem convolution_integrand_integrableAE
    {f g : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 1 < p) (hp' : p ≠ ⊤)
    (hf : Integrable f volume)
    (hg : MemLp g p volume) :
    ∀ᵐ x ∂volume,
      Integrable (fun y => f (x - y) * g y) volume := by
```

Lines 77–85 state the requested norm inequality, but under the weaker `hp : 1 ≤ p`, so the result is stronger than requested:

```lean
theorem young_convolution_inequality
    {f g : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hf : Integrable f volume)
    (hg : MemLp g p volume) :
    eLpNorm (convolution f g) p volume ≤
      eLpNorm f 1 volume * eLpNorm g p volume :=
```

No local axiom, opaque declaration, or sorry occurs.

### a96A01

Graded declarations are `quasiNorm_antitone`, `quasiNorm_tendsto_exists`, `ae_pos_of_limit_pos`, and `limit_ge_geometric_mean` (no `apm_a96A01`). The encoding of the norm is at lines 33–34:

```lean
def quasiNorm (f : ℝ → ℝ) (p : ℝ) : ℝ :=
  (∫ x in Set.Icc (0:ℝ) 1, ‖f x‖ ^ p ∂volume) ^ (1 / p)
```

The final two conclusions are stated at lines 236–242 and 359–367:

```lean
theorem ae_pos_of_limit_pos ...
    (hLim : Tendsto (quasiNorm f) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    ∀ᵐ x ∂(volume.restrict (Icc 0 1)), 0 < ‖f x‖ := by

theorem limit_ge_geometric_mean ...
    (hLim : Tendsto (quasiNorm f) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    exp (∫ x in Set.Icc (0:ℝ) 1, log ‖f x‖ ∂volume) ≤ L := by
```

The positivity hypothesis of the last theorem is exactly the preceding proved conclusion, not an unproved carrier of the core. The commit titled “Narrow ... frontier” changed proof structure, not this theorem type. No local axiom, opaque declaration, or sorry occurs.

### a96A02

Graded declarations: `spikeFunction_spec`, `spikeFunction_holderWith`, and `spikeFunction_not_absolutelyContinuous` (no `apm_a96A02`). The current `spikeFunction` is a concrete `noncomputable def` at lines 48–58, not opaque. Its exact piecewise-linear behavior is captured by `SpikeFunctionSpec` at lines 64–75 and proved at line 153:

```lean
theorem spikeFunction_spec : SpikeFunctionSpec spikeFunction := by
```

The requested conclusions at lines 383–388 and 474–483 take that exact specification:

```lean
theorem spikeFunction_holderWith :
    SpikeFunctionSpec spikeFunction →
    ∃ A : ℝ, 0 < A ∧ ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      |spikeFunction x - spikeFunction y| ≤ A * |x - y| ^ ((1:ℝ) / 2) := by

theorem spikeFunction_not_absolutelyContinuous :
    SpikeFunctionSpec spikeFunction →
    ∃ ε > 0, ∀ δ > 0, ∃ (n : ℕ) (a b : Fin n → ℝ), ... := by
```

Because `spikeFunction_spec` supplies the premise, it does not carry unproved core content. In the bank, `def spikeFunction : ℝ → ℝ := 0`; its asserted non-absolute-continuity conclusion was false. The repair was therefore a correction. No current local axiom, opaque declaration, or sorry occurs.

### a96A03

Graded declarations: `memLp_limit_of_ae_tendsto_bounded` and `weak_convergence_of_ae_tendsto_L2_bounded` (no `apm_a96A03`). Lines 25–31 give the first conclusion:

```lean
theorem memLp_limit_of_ae_tendsto_bounded ...
    (hf_bdd : ∀ n, eLpNorm (f n) 2 volume ≤ 1)
    (hae : ∀ᵐ x ∂volume, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    MemLp g 2 volume ∧ eLpNorm g 2 volume ≤ 1 := by
```

Lines 65–75 quantify over every `h` in `L²` and state convergence of the pairings. Its `hg_meas` premise follows from the first result’s `MemLp g 2`, so the two-declaration encoding does not impose an extra mathematical restriction. No local axiom, opaque declaration, or sorry occurs.

### a96A04

Graded declarations: `heatConv_contDiff`, `heatConv_L2_le`, and `heatConv_tendsto_L2` (no `apm_a96A04`). The representation boundary is already one-dimensional at the definitions (`heatKernel (t : ℝ) (x : ℝ)` and `heatConv ... (x : ℝ)`), and the theorem types remain on `ℝ`. For example lines 701–706 say:

```lean
theorem heatConv_contDiff
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) :
    ContDiff ℝ ∞ (heatConv t f) := by
```

Thus it proves only the `n = 1` case of the stated `ℝⁿ` problem. The smoothness order `∞` is correctly `C^∞`; the bank’s bare `⊤` was analytic, so that historical change is a correction. No local axiom, opaque declaration, or sorry occurs.

### a96A05

Graded declaration: `sup_inv_sub_polynomial_ge_one` (no `apm_a96A05`). Lines 91–93 state exactly:

```lean
theorem sup_inv_sub_polynomial_ge_one (P : Polynomial ℂ) :
    1 ≤ ⨆ z ∈ sphere (0 : ℂ) 1, ‖z⁻¹ - Polynomial.aeval z P‖ := by
```

This is the requested supremum inequality with the standard `Polynomial ℂ` representation. No local axiom, opaque declaration, or sorry occurs.

### a96A08

The registered declaration is named `apm_a96a08` (lowercase `a`), not `apm_a96A08`. Lines 22–23 define the exact integrand, and lines 166–169 state:

```lean
theorem apm_a96a08 :
    Integrable apm_a96A08_integrand volume ∧
      (∫ x : ℝ, apm_a96A08_integrand x ∂volume) = -(2 * Real.pi) := by
```

Absolute Lebesgue integrability makes this a faithful, meaningful encoding of the improper integral. The bank had the same equality in `a96A08`, with integrability proved separately as `a96A08_integrable`; combining them is an improvement in the registered statement, not a narrowing. No local axiom, opaque declaration, or sorry occurs.

### a96J01

Lines 295–304 state the registered `apm_a96J01`:

```lean
theorem apm_a96J01 :
    ∃ (f : ℕ → ℝ → ℝ),
      (∀ n, Continuous (f n)) ∧
      (∀ n, ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ f n x) ∧
      (∃ (g : ℝ → ℝ), TendstoUniformlyOn ... (Set.Icc 0 1)) ∧
      ¬ Summable (fun n => ⨆ x : Set.Icc (0:ℝ) 1, f n x.1) := by
```

The global `Continuous (f n)` requirement is stronger than continuity only on `[0,1]`; the remaining clauses match the example requested. No local axiom, opaque declaration, or sorry occurs.

### a96J02

The declaration is named `a96J02`, not `apm_a96J02`. Lines 211–214 state:

```lean
theorem a96J02 (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hApos : 0 < volume A) (hBpos : 0 < volume B) :
    ∃ a b : ℝ, a < b ∧ Set.Ioo a b ⊆ (A + B : Set ℝ) := by
```

This is exactly the claimed nonempty open interval in `A + B`. No local axiom, opaque declaration, or sorry occurs.
