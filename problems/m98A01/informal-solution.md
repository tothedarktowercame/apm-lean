<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m98A01: Normed/Banach/Hilbert spaces, a Banach-but-not-Hilbert example, and the Closed Graph theorem from the Open Mapping theorem

## Why It's Hard

This is a four-part "foundations" question, and the difficulty is not a single hard deduction but
**knowing the exact definitions and the precise logical scaffolding** — getting a clause wrong (forgetting
completeness in "Banach," or that the *norm* must come from an inner product in "Hilbert") sinks the whole
answer. The two parts with genuine mathematical content are:

- **(c)** Producing a Banach space that is *not* Hilbert and *proving* it. The trap is trying to argue
  directly that "no inner product exists" — an existential over all possible inner products. The clean way
  is the **parallelogram law**: it is a *necessary* identity for any norm coming from an inner product, so
  exhibiting two vectors that violate it rules out *every* inner product at once.
- **(d)** Deriving the Closed Graph theorem from the Open Mapping theorem. The whole proof is an exercise
  in *changing the space you apply OMT to*: you do not apply OMT to `T` itself (which is exactly what you
  are trying to show is bounded). You apply it to the **coordinate projection from the graph**, exploiting
  that the graph — closed by hypothesis, inside a complete product — is itself a Banach space. Seeing that
  the right object is `π_X : G(T) → X`, not `T`, is the crux.

## The Key Insight

- **Banach = complete normed space; Hilbert = Banach whose norm is `⟨·,·⟩^{1/2}`.** The bridge from "norm"
  to "inner product" is the **parallelogram law** `‖x+y‖² + ‖x−y‖² = 2‖x‖² + 2‖y‖²`, forced by expanding
  the inner product. Any norm violating it cannot be a Hilbert norm — this powers (c).
- **Closed Graph from Open Mapping:** make the **graph** `G(T) = {(x,Tx)}` the stage. It is a closed
  subspace of the Banach space `X × Y`, hence itself Banach. The projection `π_X : G(T) → X`,
  `(x,Tx) ↦ x`, is a bounded linear **bijection** between Banach spaces, so by the Open Mapping theorem
  (bounded-inverse form) its inverse `x ↦ (x,Tx)` is bounded. Then `T = π_Y ∘ π_X^{-1}` is a composition
  of bounded maps, hence bounded.

## Complete Proof

### (a) Normed linear space

A **normed linear space** is a vector space `X` over the field `𝕂` (`= ℝ` or `ℂ`) together with a map
`‖·‖ : X → [0,∞)`, the *norm*, satisfying for all `x, y ∈ X` and all scalars `α ∈ 𝕂`:

1. **(positive definiteness)** `‖x‖ ≥ 0`, and `‖x‖ = 0` if and only if `x = 0`;
2. **(absolute homogeneity)** `‖αx‖ = |α|\,‖x‖`;
3. **(triangle inequality)** `‖x + y‖ ≤ ‖x‖ + ‖y‖`.

The norm induces a metric `d(x,y) = ‖x − y‖`, with respect to which addition and scalar multiplication are
continuous; thus `X` is in particular a metric (topological vector) space.

### (b) Banach spaces and Hilbert spaces

- A normed linear space `X` is a **Banach space** when it is **complete** in the metric `d(x,y)=‖x−y‖` —
  i.e. every Cauchy sequence in `X` converges to a limit in `X`.
- A Banach space `X` is a **Hilbert space** when its norm is induced by an **inner product**: there exists
  an inner product `⟨·,·⟩ : X × X → 𝕂` (linear in one argument, conjugate-symmetric, positive definite)
  such that `‖x‖ = ⟨x,x⟩^{1/2}` for all `x`. Equivalently (Jordan–von Neumann theorem), a Banach space is
  Hilbert iff its norm satisfies the **parallelogram law**
  $$\|x+y\|^2 + \|x-y\|^2 = 2\|x\|^2 + 2\|y\|^2 \qquad (x,y \in X).$$

### (c) A Banach space that is not a Hilbert space

**Example.** `X = C[0,1]`, the space of continuous real-valued functions on `[0,1]`, with the supremum
norm `‖f‖ = \max_{t\in[0,1]} |f(t)|`.

*It is a Banach space.* The sup norm satisfies the three norm axioms. Completeness is the standard fact
that a uniformly Cauchy sequence of continuous functions converges uniformly to a limit, and a uniform
limit of continuous functions is continuous; thus the limit lies in `C[0,1]`.

*It is not a Hilbert space.* We show the parallelogram law fails, which is impossible for an
inner-product norm. First, the necessity of the law: if `‖·‖` came from an inner product, then expanding
$$\|x+y\|^2 + \|x-y\|^2 = \langle x+y,x+y\rangle + \langle x-y,x-y\rangle = 2\langle x,x\rangle + 2\langle y,y\rangle = 2\|x\|^2 + 2\|y\|^2,$$
the cross terms `±2\,\mathrm{Re}\langle x,y\rangle` cancelling — so the parallelogram law holds for every
pair `x,y`. Now take the two functions
$$f(t) = 1 \ (\text{constant}), \qquad g(t) = t.$$
Then `‖f‖ = 1` and `‖g‖ = 1`, while
$$\|f+g\| = \max_{t\in[0,1]}(1+t) = 2, \qquad \|f-g\| = \max_{t\in[0,1]}(1-t) = 1.$$
Hence
$$\|f+g\|^2 + \|f-g\|^2 = 4 + 1 = 5, \qquad 2\|f\|^2 + 2\|g\|^2 = 2 + 2 = 4,$$
so `5 ≠ 4`: the parallelogram law fails for this pair. Therefore no inner product can induce the sup norm,
and `C[0,1]` is a Banach space that is **not** a Hilbert space. ∎

*(Any `p ≠ 2` example works the same way; e.g. in `ℓ^1`, `e_1, e_2` give
`‖e_1+e_2‖² + ‖e_1−e_2‖² = 4 + 4 = 8 ≠ 4 = 2‖e_1‖² + 2‖e_2‖²`.)*

### (d) Open Mapping theorem; Closed Graph theorem from it

**Open Mapping Theorem (statement).** Let `X` and `Y` be Banach spaces and `T : X → Y` a bounded
(continuous) linear map that is **surjective**. Then `T` is an **open map**: the image `T(U)` of every
open set `U ⊆ X` is open in `Y`.

**Bounded Inverse corollary.** If, in addition, `T` is a *bijection*, then `T^{-1} : Y → X` is bounded.
Indeed openness of `T` means: for every open `U ⊆ X`, `T(U)` is open; but `T(U) = (T^{-1})^{-1}(U)`, so
the preimage under `T^{-1}` of every open set is open, i.e. `T^{-1}` is continuous (hence bounded, being
linear). We use this corollary below.

**Closed Graph Theorem (statement).** Let `X, Y` be Banach spaces and `T : X → Y` a *linear* map whose
**graph**
$$G(T) = \{(x, Tx) : x \in X\} \subseteq X \times Y$$
is **closed** in `X × Y`. Then `T` is bounded.

**Proof (assuming the Open Mapping theorem).**

*The product is Banach and the graph is a Banach subspace.* Equip `X × Y` with the norm
`‖(x,y)‖ = ‖x‖_X + ‖y‖_Y`. With this norm `X × Y` is complete (a sequence is Cauchy/convergent iff each
coordinate is, and `X, Y` are complete), so `X × Y` is a Banach space. Since `T` is linear, `G(T)` is a
linear subspace of `X × Y`; by hypothesis it is closed, and a closed subspace of a Banach space is itself
complete. Hence `G(T)` is a **Banach space** under the restricted norm.

*The coordinate projections off the graph are bounded.* Define
$$\pi_X : G(T) \to X,\quad (x,Tx) \mapsto x, \qquad \pi_Y : G(T) \to Y,\quad (x,Tx) \mapsto Tx.$$
Both are linear, and bounded with norm `≤ 1`:
$$\|\pi_X(x,Tx)\| = \|x\| \le \|x\| + \|Tx\| = \|(x,Tx)\|, \qquad \|\pi_Y(x,Tx)\| = \|Tx\| \le \|(x,Tx)\|.$$

*`π_X` is a bijection, so its inverse is bounded.* `π_X` is **injective** (if `π_X(x,Tx) = 0` then `x = 0`,
so `(x,Tx) = (0, T0) = (0,0)` by linearity) and **surjective** (every `x ∈ X` is hit by `(x,Tx) ∈ G(T)`).
Thus `π_X : G(T) → X` is a bounded linear bijection between the Banach spaces `G(T)` and `X`. By the
**Bounded Inverse corollary** of the Open Mapping theorem, its inverse
$$\pi_X^{-1} : X \to G(T), \qquad x \mapsto (x, Tx)$$
is bounded: there is a constant `C` with `‖(x,Tx)‖ ≤ C\,‖x‖` for all `x`.

*Conclude `T` is bounded.* Observe `T = \pi_Y \circ \pi_X^{-1}`: for `x ∈ X`,
`\pi_X^{-1}(x) = (x,Tx)` and `\pi_Y(x,Tx) = Tx`. A composition of bounded linear maps is bounded, and
quantitatively, for every `x ∈ X`,
$$\|Tx\| = \big\|\pi_Y\big(\pi_X^{-1}(x)\big)\big\| \le \|\pi_Y\|\;\big\|\pi_X^{-1}(x)\big\| \le 1\cdot C\,\|x\| = C\,\|x\|.$$
Therefore `T` is bounded, i.e. continuous. ∎

**Remark.** The Closed Graph theorem is a labor-saving device: to prove a linear `T` is continuous it
suffices to check the *a priori weaker* condition that `xₙ → x` and `Txₙ → y` together force `y = Tx`
(closedness of the graph), instead of verifying `Txₙ → Tx` for every convergent `xₙ`. The proof shows this
is *exactly* as strong as continuity once both spaces are complete — and completeness is essential, since
it is what makes both `X × Y` and the closed subspace `G(T)` Banach so that the Open Mapping theorem
applies. (The converse direction — continuous ⇒ closed graph — holds in any topological setting and needs
no completeness.)
