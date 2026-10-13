# Blueprint for m03J01

## Triage

Verdict: **true and faithful**.

The reopened Lean statement now uses `ContDiff ℝ ∞`, so its test space is the
usual smooth compactly supported space rather than the analytic space produced
by `ContDiff ℝ ω`.  This matches the definition of `H₀¹(Ω)` in the source.
The theorem also retains the documented repair of the source typo
`U ∈ H²(U)` to `u ∈ H²(Ω)`.

I checked the principal degeneracies.  In dimension zero, the already proved
lemmas show that every gradient is zero and that testing the weak equation with
the solution gives the required `L²` bound.  For zero forcing, uniqueness forces
the value of every solution to vanish a.e.; closability of the weak gradient
then forces its gradient to vanish, and uniqueness of distributional
derivatives forces any weak Hessian to vanish a.e.  Thus the homogeneous case
is compatible with an estimate whose right side is zero.  Nonempty bounded open
sets do not exist in dimension zero, so that exceptional case is in fact
vacuous in the two PDE clauses.  No counterexample was present in the available
solve-loop records.

`Blueprint.lean` copies all currently compiled definitions and proofs from
`Main.lean`.  In particular, construction of the custom `H₀¹` closure,
existence and value-uniqueness of weak solutions, the abstract Riesz theorem,
and elementary weak-Hessian facts are proved rather than admitted.  Only the
three reopened obligations below contain `sorry`.

## Remaining lemmas

### `apm_m03J01_gradient_unique_of_val_ae`

**Statement in words.** Two elements of the custom `H₀¹` closure with equal
value functions almost everywhere have equal weak gradients almost everywhere.

**Why true.** Subtract the two approximating test-function sequences (using the
proved additive and scalar closure lemmas).  Their values tend to zero in
`L²`, while their gradients tend to the gradient difference.  The classical
closability argument for the gradient tests the limit against derivatives of
smooth compactly supported scalar functions: integration by parts makes the
pairing tend to zero from value convergence, while gradient convergence
identifies the limit.  Density of test functions then says every coordinate of
the gradient difference is zero.  The useful Mathlib infrastructure is
`Lp.tendsto_Lp_iff_tendsto_eLpNorm''`, `integral_congr_ae`, and the density of
compactly supported smooth functions / fundamental lemma of distributions.

**Expected size.** 180–300 lines.

**Dependencies.** Definitions and proved test-function/closure lemmas only.

**Truth check.** For equal representatives this is immediate.  For the key
zero-value case, the hand calculation is
`∫ (∂ᵢφₖ) ψ = -∫ φₖ (∂ᵢψ) → 0`; the left side also tends to
`∫ gᵢ ψ`, so `gᵢ = 0` distributionally and hence a.e.  Compact support makes
all pairings integrable.

### `apm_m03J01_weakHessian_unique_ae`

**Statement in words.** Two `L²` weak Hessians of the same weak gradient agree
almost everywhere.

**Why true.** Subtract their distributional identities.  For every pair of
coordinates and every compactly supported smooth test function, the integral
of `(H-K)ᵢⱼ φ` is zero.  The fundamental lemma of distributions gives
`(H-K)ᵢⱼ = 0` a.e.; finiteness of `Fin n × Fin n` combines the coordinatewise
statements into function-valued a.e. equality.  Relevant library operations
include `MemLp.sub`, `integral_sub`, and `Filter.Eventually` finite intersections.

**Expected size.** 80–160 lines, assuming the distributional fundamental lemma
is available in a directly applicable form; otherwise 200–300 lines to bridge
its test-function encoding.

**Dependencies.** Definitions only; independent of gradient uniqueness.

**Truth check.** In dimension zero the conclusion is pointwise true because
the codomain `Fin 0 → Fin 0 → ℝ` is subsingleton.  In positive dimension the
hand subtraction above is the standard uniqueness proof for distributions.

### `apm_m03J01_uniform_H2_bound`

**Statement in words.** On a fixed bounded domain, the qualitative hypothesis
that every weak solution has an `L²` weak Hessian implies one finite constant
bounding the displayed `H²` size by the forcing `L²` norm.

**Why true.** Form quotient Banach spaces for `L²` forcing and for triples
`(u, ∇u, H)` satisfying the approximation and weak-Hessian relations.  The
preceding two uniqueness lemmas make the solution operator single-valued on
a.e. classes.  The already proved energy argument gives uniqueness and the
continuous `L² → H₀¹` estimate.  If `Fₖ → F` in `L²` and the corresponding
triples converge in the graph norm, pass to the weak equation and the
distributional Hessian identities to identify the limit with the solution for
`F`.  Hence the graph is sequentially closed.  Apply
`LinearMap.continuous_of_seq_closed_graph`, extract its operator-norm bound,
and translate the real norm inequality to `ENNReal`; the proved
`apm_m03J01_H2size_lt_top` handles finiteness.  Finally choose representatives
to obtain the existential Hessian in the exact theorem statement.

**Expected size.** 250–450 lines.  Most of the length is quotient/graph-space
plumbing; the analytic argument itself is short.

**Dependencies.** Both preceding uniqueness lemmas, plus the already proved
weak-solution existence/uniqueness and `H2size_lt_top` lemmas.

**Truth check.** At `F = 0`, uniqueness plus the two preceding lemmas makes all
three graph components zero a.e., exactly as the asserted zero right-hand side
requires.  For scalar multiples, linearity of the weak equation and weak
Hessian identity scales both sides equally.  The sequential closed-graph
calculation agrees with the informal solution's standard proof.

## Assembly

The main theorem contains no `sorry`.  Its abstract clause is
`apm_m03J01_abstract_variational`; its weak-existence clause directly combines
`apm_m03J01_weakSolution_exists` and
`apm_m03J01_weakSolution_unique_ae`; and its regularity clause is the final
blueprint lemma.

## Dependency layers

* **Layer 1 (parallel):**
  `apm_m03J01_gradient_unique_of_val_ae`,
  `apm_m03J01_weakHessian_unique_ae`.
* **Layer 2:** `apm_m03J01_uniform_H2_bound`.
* **Layer 3 (already compiled):** assembly of `apm_m03j01`.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m03J01/Blueprint.lean
```

The final output of `#print axioms apm_m03j01` was:

```text
'apm_m03j01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The three warnings identifying `sorry` are exactly the three lemmas listed
above.  The main theorem has no direct `sorry`.
