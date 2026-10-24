| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| m99J03 | narrower | The three distributional limits are correct, but the test class uses `ContDiff ℝ (⊤ : ℕ∞)`, i.e. analytic (`ω`), rather than all compactly supported smooth functions. | — |
| m99J04 | faithful | States the compact self-adjoint spectral basis, compact/self-adjoint conjugate, the generalized eigenbasis, its weighted orthonormality, and exactly when the transported basis is orthonormal. | — |
| a00J01 | faithful | Proves the finite essential-supremum limit of the `eLpNorm`s on `[0,1]`; Mathlib's `eLpNorm f ⊤` is the requested essential-supremum norm. | — |
| a00J02 | faithful | Under absolute continuity, `f(0)=0`, and integrability of `|f'|²`, proves `f(x)/√x → 0` from the right. | — |
| a00J03 | narrower | Isometry is proved from measure preservation, but surjectivity assumes separately that the measurable inverse is measure preserving instead of deriving it from the problem's hypotheses. | — |
| a00J05 | faithful | Defines the stated Cauchy transform and proves holomorphicity off `K`, nonexistence of an entire extension agreeing there, and limit `z f(z) → -m(K)`. | correction: `dcf668ab9` repaired the earlier harvested/misparsed statement to the actual three-part Cauchy-transform problem. |
| a00J06 | stronger | Uses a real power-series sum and proves there is no real-analytic germ at `1`; this is stronger than merely excluding a complex analytic continuation across `1`, and implies the requested singularity. | — |
| a01A01 | faithful | Gives explicit nonnegative sequences with pointwise cofinal unboundedness and integrals tending to zero on `[0,1]` and every positive-dimensional Euclidean space. | — |
| a01A02 | faithful | Formalizes the intended weak-`L²` tail estimate for every positive threshold and proves the local `L¹` bound with constant `2√C` for every measurable finite positive-measure set. | correction: `dcf668ab9` replaces a vacuous `.toReal` tail bound (infinite superlevel measure mapped to zero) by the intended `ENNReal` measure inequality. |
| a01A03 | faithful | For every compactly supported `C∞` test function, the convolution identity implies `g` equals `χ[-h,h]` almost everywhere. | correction: `dcf668ab9` fixed the original overbroad/unsatisfiable test class but used analytic `⊤`; `46cf80962` corrects that new defect to smooth order `∞`. The file includes a compiled counterexample to the intermediate analytic-test statement. |

### Evidence

#### m99J03

The prose asks for convergence in `𝒟'(ℝ)`, hence testing against all `C_c^∞` functions. The dependency is instead
`def apm_m99j03_IsTestFunction ... := ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ` (lines 21–22). Here `⊤ : ℕ∞` is analytic order `ω`, not smooth order `∞`, so this is a strict test-class restriction. The registered theorem otherwise gives the correct limits: triangle to `φ 0`, dipole to `-deriv φ 0`, and dilation to `ψ 0 * ∫ φ` (lines 455–468). No `axiom`, `opaque`, or sorry-typed dependency was found.

#### m99J04

`apm_m99j04_HasEigenHilbertBasis` is an actual `HilbertBasis` of real-eigenvalue eigenvectors (lines 40–47). The theorem assumes precisely compactness and self-adjointness (lines 217–223), proves these for `A*TA` (224–227), and supplies the generalized equation `T (A (w i)) = eigenvalue i • weight A (A (w i))` plus weighted orthonormality (228–236). Lines 237–239 answer the orthonormality question by the expected unitary condition `A* A = id`. No flagged dependency.

#### a00J01

There is no declaration named `apm_a00j01`; the graded declaration is `eLpNorm_tendsto_top`. It assumes strong measurability and finite `eLpNorm f ⊤` (lines 164–166) and concludes convergence of `eLpNorm f p` as `p → ⊤` to `eLpNorm f ⊤` (167–168). This is the standard Lean encoding of the stated `L∞` result on the unit interval. No flagged dependency.

#### a00J02

Lines 119–126 state exactly the right-hand limit `Tendsto (fun x ↦ f x / Real.sqrt x) (nhdsWithin 0 (Ioi 0)) (nhds 0)` under the three requested hypotheses. No flagged dependency.

#### a00J03

There is no `apm_a00j03`; the graded declarations are `composition_isometry` and `composition_isometric_isomorphism`. The former proves isometry from `MeasurePreserving φ` (lines 27–30). The latter proves surjectivity only after accepting both `he : MeasurePreserving e μ μ` and `he_symm : MeasurePreserving e.symm μ μ` (lines 47–51). The prose gives preservation only for `φ`; preservation of its measurable inverse is a consequence to prove, so supplying `he_symm` narrows the theorem.

#### a00J05

There is no `apm_a00j05`; the graded declarations are the three named parts. `cauchyTransform` is exactly `∫ t in K, ((t : ℂ) - z)⁻¹` (lines 54–59). Holomorphicity is `DifferentiableOn ℂ ... ((↑) '' K)ᶜ` (201–205), the asymptotic is `z * cauchyTransform K z → -(volume K).toReal` (226–228), and `cauchyTransform_not_extendable_to_entire` rejects any entire `g` agreeing off `K` (lines 347 onward). The historical repair is a correction: the source comments identify a harvested mismatch, and the repaired declarations state the actual problem.

#### a00J06

There is no `apm_a00j06`; the graded declaration is `singular_at_one`. The dependencies define a real formal power series and its sum (lines 56–62). Lines 93–96 prove `¬ ∃ ρ, 0 < ρ ∧ AnalyticAt ℝ (f a) 1`. Excluding even a real-analytic germ is stronger than excluding complex analytic continuation, not narrower or vacuous. No flagged dependency.

#### a01A01

Lines 587–600 assert explicit sequences on `[0,1]` and `EuclideanSpace ℝ (Fin d)`: integrability, nonnegativity, pointwise cofinal unboundedness (`∀ M N, ∃ k ≥ N, M ≤ f k x`), and integral convergence to zero. This faithfully strengthens `limsup = ∞` into its equivalent cofinal formulation. No flagged dependency.

#### a01A02

There is no `apm_a01a02`; the graded declaration is `weakL2_implies_L1_bound`. Lines 86–92 use the intended `ENNReal` inequality for every `t > 0` and conclude the requested estimate for every measurable finite positive-measure `E`; line 93 chooses `C₁ = 2√C`. Lines 77–85 document why the earlier `.toReal` form was vacuous when superlevel measure was `⊤`, so the repair is a correction. No flagged dependency.

#### a01A03

There is no `apm_a01a03`; the graded declaration is `convolution_identity_implies_indicator`. Lines 98–104 use `ContDiff ℝ ∞`, compact support, positive `h`, and conclude the required almost-everywhere indicator identity. Lines 82–97 document both statement defects. The compiled `analytic_compactSupport_eq_zero` and `convolution_identity_counterexample` (lines 210–245) refute the intermediate `ContDiff ℝ ⊤` version, making the later change a correction rather than a stylistic improvement. No axiom, opaque, or sorry-typed dependency was found.
