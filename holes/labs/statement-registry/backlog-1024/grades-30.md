| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| m96A03 | faithful | States Parseval for integrated ONB elements and the closed-range solvability/adjoint-kernel criterion. | — |
| m96A04 | faithful | Starts with algebraic `A` and arbitrary `B`, then concludes linearity and continuity of `B` and continuity of `A`. | — |
| m96J01 | faithful | Mathlib's orthogonal projection is used as the closest-point map and all four requested properties are stated, with nonzero `V` for norm one. | — |
| m97A05 | narrower | It constructs the distribution and proves the derivative/PDE relations, but omits the requested Fourier-transform formula and does not explicitly give the action formula for `∂x T`. | **correction** (`3e65ae743`): replaces the bank's arbitrary predicates and supplied conclusions with an actual tempered distribution and genuine derivative equations, though part (b) remains unencoded. |
| m98A01 | faithful | Uses Mathlib's normed/Banach/Hilbert structures, supplies a concrete non-Hilbert Banach example via parallelogram failure, and states open-mapping and closed-graph results. | — |
| m98J01 | faithful | Gives concrete open-mapping and closed-graph statements and a theorem with open mapping explicitly assumed whose conclusion is closed graph. | **correction** (`3e65ae743`): the bank quantified arbitrary propositions and assumed the desired implication itself; the replacement states the actual functional-analysis theorems. |
| m98J03 | faithful | Includes spectrum containment and degenerate cases, compactness iff finite-dimensional range, the orthogonal complement and closedness, invariant subspaces, and self-adjointness. | **correction** (`4c65103a4`): the bank encoded only closedness, commuting invariance, and the adjoint, omitting the spectrum and compactness parts. |
| m99A03 | faithful | Proves the normal nilpotent assertion for arbitrary complex Hilbert spaces and constructs the requested operator on an explicit infinite-dimensional Hilbert space. | — |
| m99A04 | faithful | States existence and uniqueness of a continuous extension agreeing with the uniformly continuous map on the dense subtype. | **neutral** (`8890d3968`): the theorem was renamed/repackaged from `extend_uniformContinuous_dense` to `apm_m99a04` without changing its mathematical statement. |
| m99A05 | faithful | Encodes weak convergence by all continuous linear functionals and states the counterexample and all four general convergence properties. | — |

### Evidence notes

#### m96A03

`apm_m96a03` states, for a Hilbert basis of the genuine `L²` space, `∑' n, ‖∫ s in a..t, u n s‖ ^ 2 = t - a` (lines 20–25). Its second conjunct says that for a continuous linear operator with closed range, `∃ x, A x = b` iff every `y` satisfying `A.adjoint y = 0` also satisfies `inner ℂ b y = 0` (lines 26–27). These are the two prelim claims. The statement has been unchanged since the bank commit.

#### m96A04

`apm_m96a04` takes `A : X →ₗ[ℂ] X`, so continuity is not built in, and an arbitrary function `B : X → X` (lines 19–22). From the adjoint identity it concludes existence of a linear map with underlying function `B`, `Continuous B`, and `Continuous A` (line 23). This exactly expresses parts (a)–(c), and the statement is unchanged from the bank.

#### m96J01

There is no `apm_m96j01`; the graded declaration is `projection_properties`. The local definition is `proj V := (V : Submodule ℝ H).starProjection` (lines 11–13), Mathlib's closest-point orthogonal projection. With `V ≠ ⊥`, the theorem states linearity, `‖F‖ = 1`, `IsSelfAdjoint F`, and `F.comp F = F` (lines 43–47). The nonzero hypothesis is exactly needed for the requested norm-one claim.

#### m97A05

`apm_m97a05` constructs `T : 𝓢'(ℝ × ℝ, ℂ)` and states its action `T φ = ∫ s, φ (s,-s)` (lines 100–103), so it genuinely defines a tempered—and hence ordinary—distribution. It further states `∂x T = ∂y T` and `∂x²T = ∂y²T` (lines 103–105), which supplies the wave-equation conclusion. No conjunct mentions the Fourier transform or identifies its value, and the first-derivative conjunct is only an equality with `∂y T`, not an explicit test-function action formula. The original bank theorem instead accepted arbitrary `isDistribution`/`hasFourier` predicates plus hypotheses already asserting them, so the concrete rewrite is a correction despite remaining incomplete.

#### m98A01

`apm_m98a01_C01` is the sup-norm space `ContinuousMap (Icc 0 1) ℝ` (line 17). The theorem asserts its completeness and exhibits functions violating the parallelogram identity (lines 19–22), the standard obstruction to a Hilbert norm. It then states the open mapping theorem for surjective continuous linear maps between real Banach spaces and the closed graph theorem for algebraic linear maps (lines 23–29). `NormedSpace`, `CompleteSpace`, and `InnerProductSpace` are the corresponding formal definitions/types rather than separately restated prose definitions.

#### m98J01

There is no single `apm_m98j01`; the graded declarations are `apm_m98j01_open_mapping`, `apm_m98j01_closed_graph`, and `apm_m98j01_closed_graph_of_open_mapping`. Lines 18–24 state that a surjective continuous linear map between Banach spaces is open. Lines 27–34 state that an everywhere-defined linear map with closed graph is continuous. Lines 38–47 explicitly take the open-mapping theorem as a hypothesis and conclude the closed-graph result. The bank's arbitrary propositions and hypothesis `OpenMapping → ClosedGraph` supplied the entire requested implication, so replacing it was a correction.

#### m98J03

The only theorem-local definition is `apm_m98J03_perp V := (V : Submodule ℝ H)ᗮ` (lines 20–22). `apm_m98j03` states spectrum containment in `{0,1}`, characterizes spectra `{0}` and `{1}` by `V=⊥` and `V=⊤`, gives compactness iff `V` is finite dimensional, asserts closedness of `Vperp`, gives both commuting invariance claims, and states `P.adjoint=P` (lines 139–153). The initial bank file contained only orthogonal-complement closedness, commuting invariance, and adjoint equality, so the repair that added the omitted parts is a correction.

#### m99A03

`m99A03ExampleSpace` is three copies of complex `ℓ²`, and `m99A03Shift` is the three-step block shift `(x₂,x₃,0)` (lines 15–23). `apm_m99a03` universally states that compact, star-normal `A` with `A^3=0` is zero and existentially supplies an operator on that explicit Hilbert space whose first two powers are noncompact and third power compact (lines 100–111). Selecting an explicit infinite-dimensional space is exactly what the prelim's construction request permits.

#### m99A04

`apm_m99a04` assumes complete metric spaces, a dense set represented by its subtype, and `UniformContinuous f`; it concludes unique `F : X → Y` that is continuous and agrees with `f` on every point of `A` (lines 19–25). The initial `extend_uniformContinuous_dense` statement has the same quantifiers and conclusion, so the later headline change is neutral.

#### m99A05

`M99A05WeaklyConverges` means convergence after every continuous linear functional (lines 14–17). `apm_m99a05` states: the standard `ℓ²` basis is weakly but not strongly null; strong convergence implies weak convergence; in finite dimension the two are equivalent; weakly convergent sequences are norm bounded; and weak limits are unique (lines 23–37). Thus every listed part is represented.

No current graded declaration depends on a local `axiom`, `opaque`, or `sorry`-typed definition; none of those declaration forms occurs in these ten current `Main.lean` files.
