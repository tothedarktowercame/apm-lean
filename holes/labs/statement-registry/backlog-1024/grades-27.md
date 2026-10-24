| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| b99A04 | faithful | Encodes all four requested conclusions for a matrix ring: simplicity, decomposition of the regular module, classification of simple submodules, and classification of finite-dimensional modules. | — |
| bpm-1-1-1 | faithful | States exactly the requested cosine inequality for `0 < p < 1` and `0 ≤ θ ≤ π/2`. | — |
| bpm-1-1-2 | faithful | States the sharp endpoint-zero (L^\infty\)-(L^2) derivative inequality on `[a,b]`. | — |
| bpm-1-2-2 | faithful | Uses the problem's intermediate-value property and relative closedness of point fibers to conclude continuity on the interval. | — |
| bpm-1-3-1 | faithful | States the finite decreasing nonnegative power-mean limit with limit equal to the largest entry. | — |
| bpm-1-3-2 | faithful | States exactly `((n+1)/n)^n → e` over positive natural indices. | — |
| bpm-1-4-1 | faithful | States the endpoint equality conclusion from continuity and zero derivative on the open interval. | — |
| bpm-1-5-1 | faithful | States that a continuous nonnegative function with zero integral vanishes pointwise. | — |
| bpm-1-6-2 | faithful | States continuity of a pointwise limit of differentiable functions whose derivatives are uniformly bounded by one. | — |
| bpm-1-7-1 | faithful | Correctly gives the constant, cosine, and sine Fourier coefficients of the specified periodic sawtooth function. | — |

### b99A04

The graded declaration is `apm_b99a04`. The matrix algebra and its natural module are explicit (`R := Matrix (Fin n) (Fin n) F`, `V := Fin n → F`, lines 50–51). The conclusions quote all requested parts: `IsSimpleModule R V` (line 52); `iSupIndep L ∧ ⨆ i, L i = ⊤ ∧ ∀ i, Nonempty (L i ≃ₗ[R] V)` (lines 53–55); every nonzero action image `LinearMap.range ...` is linearly equivalent to `V` (lines 56–58); and every compatible finite-dimensional module is `Nonempty (W ≃ₗ[R] (Fin m → V))` for some `m` (lines 59–61). The scalar-tower assumptions merely express the finite-dimensionality over the base field required by the question. No `axiom`, `opaque`, or `sorry` occurs in the file.

### bpm-1-1-1

The graded declaration is `bpm_1_1_1`. It assumes `0 ≤ θ`, `θ ≤ Real.pi / 2`, `0 < p`, and `p < 1`, and concludes `Real.rpow (Real.cos θ) p ≤ Real.cos (p * θ)` (lines 16–20), matching the question verbatim. No declaration hazard occurs.

### bpm-1-1-2

The graded declaration is `bpm_1_1_2`. Its hypotheses are `ContDiffOn ℝ 1 f (Set.Icc a b)` and zero endpoint values, and its conclusion is `sSup (|f| '' Icc a b) ≤ sqrt (intervalIntegral (deriv f)^2)` (lines 83–88). This is the requested inequality; use of `deriv f` at the measure-zero endpoints does not restrict the claim. No declaration hazard occurs.

### bpm-1-2-2

The graded declaration is `bpm_1_2_2`. Lines 19–24 encode the intermediate-value property `u ∈ Icc x y → ∃ z ∈ Icc x y, f z = u` and relative closedness `IsClosed (Icc a b ∩ f ⁻¹' {y})`; line 26 concludes `ContinuousOn f (Icc a b)`. These are precisely the problem's hypotheses and conclusion. No declaration hazard occurs.

### bpm-1-3-1

The graded declaration is `bpm_1_3_1`. Lines 18–23 require the finite family to be antitone and nonnegative, and lines 24–26 conclude that `Real.rpow (∑ i, Real.rpow (A i) n) (1 / n)` tends to `A 0`. Indexing by `Fin (k+1)` is a faithful finite-list encoding. No declaration hazard occurs.

### bpm-1-3-2

The graded declaration is `bpm_1_3_2`. Lines 14–20 state `Tendsto (fun n : ℕ+ => ((n+1)/n)^n) atTop (𝓝 (exp 1))`, exactly the requested limit. Positive naturals avoid the undefined `n=0` term without narrowing the asymptotic claim. No declaration hazard occurs.

### bpm-1-4-1

The graded declaration is `bpm_1_4_1`. Lines 16–22 assume `a ≤ b`, continuity on `Icc a b`, and `HasDerivAt f 0 x` for every interior point, then conclude `f a = f b`. This is exactly the problem. No declaration hazard occurs.

### bpm-1-5-1

The graded declaration is `bpm_1_5_1`. Lines 18–23 assume continuity and pointwise nonnegativity on `[0,1]`, together with integral zero, and conclude `∀ x ∈ Icc 0 1, f x = 0`. This is exactly the requested result. No declaration hazard occurs.

### bpm-1-6-2

The graded declaration is `bpm_1_6_2`. Lines 15–18 encode differentiability everywhere with a derivative `d` satisfying `|d| ≤ 1`; lines 19–21 assume pointwise convergence to `g` and conclude `Continuous g`. The existential derivative is equivalent to the stated differentiability-plus-bound condition. No declaration hazard occurs.

### bpm-1-7-1

The graded declaration is `bpm_1_7_1`. Lines 89–94 characterize the base-period function and its `2π` periodicity. Lines 96–102 give zero constant coefficient, zero cosine coefficients, and sine coefficient `2 * (-1)^(k+1) / k`, which is precisely the displayed Fourier series. The question asks for the Fourier series coefficients, not a pointwise convergence theorem, so this is not narrower. No declaration hazard occurs.

None of the ten theorem statements changed after its file's first commit, so no repair classification applies.
