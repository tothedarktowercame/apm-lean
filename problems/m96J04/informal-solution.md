<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m96J04: A noncompact operator whose powers are compact, and a compact operator with no nonzero eigenvalues

## Why It's Hard

Both parts are "exhibit an example," so the difficulty is not a long deduction but **choosing the right
object and then verifying every clause** — and each clause is a place where the naïve choice fails.

- **(a)** asks for `A` *noncompact* yet `A², A³, …` *all compact*. The instinct "make `A` small/smoothing"
  is wrong: a single compact factor already makes every product compact, so the tension is to keep `A`
  itself **off** the compact ideal while pushing `A²` onto it. The clean way to land *every* higher power
  in the ideal at once is to make `A` **nilpotent of index 2** (`A² = 0`): then `A²,A³,…` are the zero
  operator (trivially compact) while `A` need not be. The trap is that a nilpotent operator on a
  *finite*-dimensional space, or a finite-rank one, is already compact — so the noncompactness must come
  from an **infinite-dimensional** piece on which `A` acts like an isometry.
- **(b)** asks for a compact operator with **no eigenvalues except possibly `0`**. This runs against the
  spectral theorem reflex: a compact *self-adjoint* (or normal) operator always has an eigenvalue of
  modulus `‖A‖`. So the example **must be non-normal**; you need a compact operator whose entire spectrum
  is `{0}` — a *quasinilpotent* compact operator — yet which is not nilpotent. The Volterra integration
  operator is the canonical witness, and the work is to prove *both* that it is compact (Arzelà–Ascoli)
  *and* that `Vf = λf, λ≠0` forces `f ≡ 0` (a bootstrap/ODE argument).

## The Key Insight

- **(a) Nilpotence of index 2 trivializes the powers.** Split the Hilbert space as `H = H₁ ⊕ H₂` with
  both summands infinite-dimensional, and let `A` send the second copy *isometrically* onto the first and
  kill the first:
  $$A(x,y) = (y, 0), \qquad A = \begin{pmatrix} 0 & I \\ 0 & 0\end{pmatrix}.$$
  Then `A² = 0`, so `A²,A³,… ` are compact (they are `0`); but `A` is **not** compact because it acts as
  the identity on the infinite-dimensional `H₂`, which carries a bounded sequence with no convergent
  image.
- **(b) Quasinilpotence kills the eigenvalues.** Take the **Volterra operator** on `C[0,1]`,
  $$(Vf)(t) = \int_0^t f(s)\,ds.$$
  Compactness is Arzelà–Ascoli (the image of the unit ball is uniformly bounded and Lipschitz, hence
  equicontinuous). If `Vf = λf` with `λ ≠ 0`, then `f` is forced to be smooth with `f(0)=0` and
  `λf' = f`, whose only solution with `f(0)=0` is `f ≡ 0`. So `V` has **no** nonzero eigenvalue.

## Complete Proof

### Part (a): `A` noncompact, `Aⁿ` compact for all `n ≥ 2`

Let `H₁, H₂` be infinite-dimensional Hilbert spaces (e.g. two copies of `ℓ²`) and work on the Hilbert
space `H = H₁ ⊕ H₂` with `‖(x,y)‖² = ‖x‖² + ‖y‖²`. Define

$$A : H \to H, \qquad A(x,y) = (y, 0).$$

**`A` is bounded.** `‖A(x,y)‖² = ‖y‖² ≤ ‖x‖² + ‖y‖² = ‖(x,y)‖²`, so `‖A‖ ≤ 1` (indeed `‖A‖ = 1`, taking
`x=0`).

**`A² = 0`, so all higher powers are compact.** Compute
$$A^2(x,y) = A\big(A(x,y)\big) = A(y,0) = (0,0).$$
Hence `A² = 0`, and therefore `Aⁿ = 0` for every `n ≥ 2`. The zero operator is compact (it maps every
bounded set to `{0}`, which is relatively compact), so `A², A³, A⁴, …` are all compact. ✔

**`A` is not compact.** Let `{eₙ}` be an orthonormal sequence in `H₂` (exists since `H₂` is
infinite-dimensional). The vectors `(0, eₙ) ∈ H` are bounded: `‖(0,eₙ)‖ = 1`. Their images are
$$A(0,e_n) = (e_n, 0),$$
and for `n ≠ m`,
$$\|A(0,e_n) - A(0,e_m)\|^2 = \|e_n - e_m\|^2 = \|e_n\|^2 + \|e_m\|^2 = 2$$
(orthonormality). So `{A(0,eₙ)}` has no Cauchy — hence no convergent — subsequence. Thus `A` maps the
bounded set `{(0,eₙ)}` to a set that is not relatively compact, so **`A` is not compact**. ✔

This `A` is the required example: noncompact, with every power `A², A³, …` compact. ∎

*(Equivalent single-space form: on `ℓ²` with ONB `{eₖ}`, set `A e_{2k} = e_{2k-1}` and `A e_{2k-1} = 0`.
Then `A²=0` and `A` is noncompact because it sends the bounded `{e_{2k}}` to the non-precompact
`{e_{2k-1}}`.)*

### Part (b): a compact operator on a Banach space with no eigenvalues except `0`

Let `X = C[0,1]` with the sup norm — a Banach space — and let `V` be the **Volterra operator**
$$(Vf)(t) = \int_0^t f(s)\,ds, \qquad 0 \le t \le 1.$$
For `f ∈ C[0,1]`, `Vf` is continuous (in fact `C¹`), so `V : X → X`.

**`V` is bounded.** `|(Vf)(t)| ≤ ∫₀¹ |f| ≤ ‖f‖_∞`, hence `‖Vf‖_∞ ≤ ‖f‖_∞` and `‖V‖ ≤ 1`.

**`V` is compact (Arzelà–Ascoli).** Let `B = { f : ‖f‖_∞ ≤ 1 }` be the closed unit ball of `X`. Its image
`V(B)` is:

- *uniformly bounded*: `‖Vf‖_∞ ≤ ‖f‖_∞ ≤ 1` for `f ∈ B`;
- *equicontinuous*: for `f ∈ B` and `0 ≤ s ≤ t ≤ 1`,
  $$|(Vf)(t) - (Vf)(s)| = \Big|\int_s^t f\Big| \le |t-s|\,\|f\|_\infty \le |t-s|,$$
  so every `Vf` is `1`-Lipschitz, giving a common modulus of continuity.

By the Arzelà–Ascoli theorem, `V(B)` is relatively compact in `C[0,1]`. Therefore `V` is a **compact
operator**. ✔

**`V` has no nonzero eigenvalue.** Suppose `Vf = λf` for some scalar `λ ≠ 0` and some `f ∈ C[0,1]`; we
show `f ≡ 0`. Since `Vf` is continuous, `f = λ⁻¹ Vf` is continuous (it already is), and then `Vf` is
continuously differentiable, so `f = λ⁻¹ Vf` is `C¹`. Evaluate the eigen-equation
$$\lambda f(t) = \int_0^t f(s)\,ds$$
at `t = 0`: the right side is `0`, so `λ f(0) = 0`, and since `λ ≠ 0`, `f(0) = 0`. Differentiating both
sides (legitimate, `f ∈ C¹`),
$$\lambda f'(t) = f(t), \qquad t \in [0,1].$$
This linear ODE with `λ ≠ 0` has general solution `f(t) = f(0)\,e^{t/λ}`. With `f(0) = 0` we get
`f(t) ≡ 0`. Hence no nonzero `λ` is an eigenvalue. ✔

So `V` is a compact operator on the Banach space `C[0,1]` with **no eigenvalues other than (at most)
`0`**. (In fact `0` is not an eigenvalue either: `Vf = 0` means `∫₀ᵗ f = 0` for all `t`, so by
differentiation `f ≡ 0`. Thus `V` has *no* eigenvalues at all, while its spectrum is `{0}` — `V` is
quasinilpotent.) ∎

**Remark.** Part (a) works precisely because index-2 nilpotence sends *all* powers to the compact (indeed
zero) ideal, while an infinite-dimensional isometric block keeps `A` itself off it. Part (b) is the
standard illustration that, for non-normal compact operators, the spectral theorem's guarantee of an
eigenvalue fails: `V` is compact with spectrum `{0}` yet has no eigenvectors, in sharp contrast to the
compact self-adjoint case where eigenvalues of modulus `‖A‖` always exist.
