| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| a94J03 | faithful | Exactly states that a continuous open map `ℝ → ℝ` is strictly increasing or strictly decreasing. | — |
| a94J04 | narrower | The representative-level contraction and convergence results are present, but no declaration constructs the requested bounded linear operator `L²(ℝ) → L²(ℝ)` or states its linearity. | — |
| a94J05 | narrower | The two Liouville conclusions are formalized, but the separate request to state Cauchy’s contour-integral formula is omitted. | — |
| a94J06 | faithful | Gives the correct values inside and outside the unit circle and states non-integrability when the pole lies on the circle. | correction: the bank declarations handled only the off-circle evaluations and did not formally state the requested on-circle case; the added umbrella theorem fixes that omission. |
| a94J07 | faithful | States injectivity of exactly `exp z + 8z + z³` on the open unit disk. | — |
| a94J08 | faithful | States that no entire complex function satisfies the given global `|z|^(3/2)` lower bound. | — |
| a95A01 | narrower | Part (a) is faithful, but part (b) proves non-Riemann-integrability only for the literal indicator `χ_K`, not for every bounded measurable `f` equal to it almost everywhere as printed. | — |
| a95A02 | faithful | States the classical absolute-continuity definition, the requested outer-measure estimate with non-strict input bound, and preservation of Lebesgue measurability. | correction: the repair changes Borel `MeasurableSet` to completed/Lebesgue `NullMeasurableSet` and changes the auxiliary strict outer-measure premise to the requested `≤`; both fix mismatches with the prelim. |
| a95A03 | narrower | The `Lᵖ` range and integral are correct and the convolution norm bound is explicit, but the convolution theorem does not itself assert that the convolution is `MemLp ... 2`, as part (c) asks. | — |
| a95A04 | faithful | The hypothesis is the stated symmetric-integral property and the conclusion is equality almost everywhere on `[0,1]` to the full integral. | — |

### Evidence

#### a94J03

The registered theorem is lines 68–69:
```lean
theorem apm_a94j03 (f : ℝ → ℝ) (hf : Continuous f) (hopen : IsOpenMap f) :
    StrictMono f ∨ StrictAnti f := by
```
This is exactly strict monotonicity, with both orientations allowed. No `axiom`, `opaque`, or sorry-typed dependency was found.

#### a94J04

There is no `apm_a94j04`; the graded declarations are `poissonConv_L2_contraction`, `poissonConv_tendsto_L2`, and `poissonConv_tendsto_ae`. Lines 200–204 give
```lean
theorem poissonConv_L2_contraction ...
    (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    eLpNorm (poissonConv y f) 2 volume ≤ eLpNorm f 2 volume
```
and lines 503–507 and 533–538 state convergence in `L²` and a.e. convergence as `y → 0⁺`. These faithfully cover the estimate and both convergence questions. However, the file contains no continuous/bounded linear map declaration for `P_y`, nor any theorem stating linearity or independence of representatives in `Lp`; hence it does not state the “extends to a bounded linear operator” portion of (a). No axiom/opaque/sorry dependency was found.

#### a94J05

There is no `apm_a94j05`; the graded declarations are `liouville_bounded` and `liouville_re_bounded_below`. Lines 55–59 state
```lean
(f : ℂ → ℂ) (hf : Differentiable ℂ f)
(M : ℝ) (hM : ∀ z, ‖f z‖ ≤ M) :
∃ c : ℂ, ∀ z, f z = c
```
and lines 71–75 give the same conclusion from a lower bound on `Re f`. Those are faithful encodings of parts (a) and (b), but no declaration states the Cauchy integral formula requested in the opening sentence; the module comment explicitly says it uses packaged Liouville instead. No axiom/opaque/sorry dependency was found.

#### a94J06

Lines 214–222 state all cases:
```lean
‖z‖ < 1 → (∮ ζ in C(0, 1), apm_a94J06_integrand z ζ) = 0
1 < ‖z‖ → ... = -(2 * Real.pi * Complex.I) / z
‖z‖ = 1 → ¬CircleIntegrable (apm_a94J06_integrand z) 0 1
```
and line 19 defines the integrand as `starRingEnd ℂ ζ / (ζ - z)`. The bank had only the named inside/outside component theorems and explicitly left the on-circle behavior informal. The current umbrella theorem adds exactly that missing source clause, so this is a correction. No axiom/opaque/sorry dependency was found.

#### a94J07

There is no `apm_a94j07`; the graded declaration is `f_poly_exp_injective_on_disk`. Line 21 defines
```lean
noncomputable def f_poly_exp (z : ℂ) : ℂ := cexp z + 8 * z + z ^ 3
```
and lines 88–89 state
```lean
theorem f_poly_exp_injective_on_disk :
    Set.InjOn f_poly_exp (ball (0 : ℂ) 1) := by
```
This exactly matches the open unit disk claim. No axiom/opaque/sorry dependency was found.

#### a94J08

There is no `apm_a94j08`; the graded declaration is `no_entire_lower_bound_three_halves`. Lines 216–218 state
```lean
¬∃ f : ℂ → ℂ, Differentiable ℂ f ∧
  ∀ z : ℂ, ‖z‖ ^ ((3:ℝ)/2) ≤ ‖f z‖
```
which is the prelim verbatim modulo `Differentiable ℂ f` as the standard encoding of entire. No axiom/opaque/sorry dependency was found.

#### a95A01

There is no `apm_a95a01`; the graded declarations are `riemann_lebesgue_sandwich` and `indicator_not_riemann_integrable`. Lines 168–174 state the requested lower/Lebesgue/upper inequalities for every measurable function bounded on `[0,1]`. But lines 291–295 conclude only
```lean
lowerRiemannIntegral (K.indicator (fun _ => (1:ℝ))) <
  upperRiemannIntegral (K.indicator (fun _ => (1:ℝ)))
```
under the hypotheses on `K`. The prelim quantifies a general bounded measurable `f` satisfying `f = χ_K` a.e.; that a.e.-representative clause is absent, so part (b) is a genuine special case. No axiom/opaque/sorry dependency was found.

#### a95A02

There is no `apm_a95a02`; the graded declarations are `acOnUnitInterval_iff`, `ac_lusin_condition_N`, and `ac_maps_measurable_to_measurable`. Lines 76–84 give the finite-disjoint-interval ε–δ definition. Lines 509–515 state
```lean
∃ δ > 0, ∀ E ⊆ Icc (0:ℝ) 1,
  volume.toOuterMeasure E ≤ ENNReal.ofReal δ →
  volume.toOuterMeasure (f '' E) ≤ ENNReal.ofReal ε
```
and lines 547–552 use `NullMeasurableSet` for both the Lebesgue-measurable input and image. The bank used a strict `< δ` premise and Borel `MeasurableSet`; the repair commit changes these to exactly the source’s non-strict outer-measure condition and Lebesgue measurability, so it is a correction. No axiom/opaque/sorry dependency was found.

#### a95A03

There is no `apm_a95a03`; the graded declarations are `f_radial_memLp_iff`, `f_radial_not_memLp_top`, `f_radial_integral`, and `f_radial_conv_L2_bound`. Lines 145–147 state
```lean
MemLp f_radial (ENNReal.ofReal p) ... ↔ 3/4 < p ∧ p < 3/2
```
and lines 339 onward exclude `p = ∞`; lines 99–100 compute the integral as `2 * π ^ 2`. Lines 547–552 give the sharp requested Young bound
```lean
eLpNorm (fun x => ∫ y, f_radial (x-y) * g y ...) 2 ... ≤
  ENNReal.ofReal (2 * π ^ 2) * eLpNorm g 2 volume
```
but the conclusion contains no `MemLp` assertion for that convolution. A finite `eLpNorm` inequality alone does not state the strong-measurability component of `MemLp`, so the explicit membership request is omitted. No axiom/opaque/sorry dependency was found.

#### a95A04

There is no `apm_a95a04`; the graded declaration is `constant_of_symmetric_mean_value`. Lines 42–45 define
```lean
∀ x h : ℝ, 0 < h → Icc (x-h) (x+h) ⊆ Icc 0 1 →
  ∫ t in (x-h)..x, f t = ∫ t in x..(x+h), f t
```
and lines 355–360 conclude
```lean
f =ᵐ[volume.restrict (Icc (0:ℝ) 1)]
  fun _ => ∫ t in (0:ℝ)..1, f t
```
from integrability on `[0,1]`. This is precisely the requested a.e. conclusion. No axiom/opaque/sorry dependency was found.
