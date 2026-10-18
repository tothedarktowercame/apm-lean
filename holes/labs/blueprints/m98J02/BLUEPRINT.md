# Blueprint for m98J02 (printed reading)

## Triage

**Verdict: true and faithful.** The theorem types of `apm_m98J02_partD` and
`apm_m98j02` are copied unchanged from `problems/m98J02/lean/Main.lean`.
The earlier narrow-reading repair has been moved to `narrow/`.

The construction uses `a = 3x - 2y`, `b = y`. Direct chain-rule
calculation gives

`T = 9 ∂a∂b + 2 ∂a - ∂b`.

For `w = exp(a/9 - 2b/9) v`, this becomes

`Tw = exp(a/9 - 2b/9) (9 ∂a∂b v + (2/9)v)`.

Thus the transformed equation is `∂a∂b v + (2/81)v = h`. The definitions
at the top of `Blueprint.lean` fix the coordinate map, source, power-series
kernel, oriented Goursat integral, pullback, and classical operator. Parts
(a)–(c), all their infrastructure, and the homogeneous constant distribution
retain their compiled proofs from `Main.lean`.

## Open lemmas

### `apm_m98J02_riemannKernel_spec`

The series `K(z) = Σ (-2/81)^k z^k/(k!)²` is entire, has `K(0)=1`, and
satisfies `zK'' + K' + (2/81)K = 0`. Prove infinite radius of convergence by
the ratio test, differentiate the power series twice, and shift the index in
the resulting summable series. Mathlib routes to investigate are
`HasSum.deriv`, `HasFPowerSeriesAt`, and the power-series API; every cited
name in the Lean statement itself has been checked by compilation.

Estimate: 100–180 lines. Dependencies: none.

Truth check: coefficient comparison gives, for the coefficient of `z^j`,
`(j+1)² a_(j+1) + (2/81)a_j = 0`; the definition satisfies this exactly.
At `z=0` only the `k=0` term remains.

### `apm_m98J02_goursat_spec`

For the fixed kernel and transformed source, the oriented double integral

`v(a,b)=∫₀ᵃ ∫₀ᵇ K((a-s)(b-t))h(s,t) dt ds`

is `C²` and satisfies `v_ab + (2/81)v=h`. For regularity first substitute
`s=aσ`, `t=bτ`, producing an integral on the fixed square `[0,1]²`, then
apply the parametric interval-integral differentiation API. For the equation,
apply FTC successively. The boundary term is `K(0)h(a,b)=h(a,b)`; the remaining
integral is the kernel ODE after `z=(a-s)(b-t)`.

Estimate: 220–300 lines. Dependencies: `riemannKernel_spec` (passed as its
three explicit hypotheses, so the file is independently extractable).

Truth check: for `h=0`, the integral and both sides vanish. For constant `h`
at `(a,b)=(0,b)` or `(a,0)`, `v=0` and the mixed derivative boundary term is
`h`, as required. Oriented integrals make the same FTC computation valid for
negative endpoints.

### `apm_m98J02_pullback_spec`

The explicit pullback is `C²`, and chain rule plus the exponential product
rule yields `classicalT g=f`. This is finite-dimensional derivative algebra;
use `ContDiff.comp`, `ContDiff.exp`, product rules, and `fderiv` chain rules,
then normalize coordinate components with `fin_cases`/`ring`.

Estimate: 140–220 lines. Dependencies: only the two hypotheses produced by
`goursat_spec`.

Truth check: the hand calculation above cancels the first-order terms and
leaves `9(v_ab + 2v/81)`. The inverse coordinate map sends `(a,b)` to
`((a+2b)/3,b)`, so it is genuinely inverse to `(3x-2y,y)`.

### `apm_m98J02_regularDistribution_of_continuous`

A continuous, possibly noncompactly supported function defines a distribution
by `φ ↦ ∫gφ`. On each test-function support stage, bound `g` on that
compact set and use the stage seminorm controlling the sup norm. Package the
linear functional with `TestFunction.mkCLM`. No global integrability of `g` is
needed because every test function is compactly supported.

Estimate: 100–180 lines. Dependencies: none.

Truth check: `g=1` is the already compiled constant distribution construction;
`g=0` gives the zero distribution. This also checks why a global-support
restriction would be spurious.

### `apm_m98J02_regular_solution_solves`

If `g` is `C²`, `Tg=f` pointwise, and `w` represents `g`, then `w` satisfies
the frozen adjoint-pairing predicate. Bundle the formal adjoint with the
already compiled `apm_m98J02_formalAdjointTest`. Integrate by parts once for
the `y` term and twice for the `xx` and `xy` terms; test-function compact
support supplies integrability and eliminates boundary terms. The existing
proof of `apm_m98J02_constantDistribution_homogeneous_aux_integral_partial`
demonstrates the relevant Mathlib integration-by-parts theorem
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`.

Estimate: 180–260 lines. Dependencies: none beyond the compiled definitions
and test-function lemmas.

Truth check: with `g=0=f`, all integrals vanish. For `g=1`, `Tg=0`, reducing
to the already compiled homogeneous-constant result. Signs match the formal
adjoint: the first derivative changes sign once, while each second derivative
changes sign twice.

## Assembly and dependency layers

`apm_m98J02_partD` contains no `sorry`. It obtains the kernel, Goursat
solution, and pullback; constructs the regular distribution; applies the
integration-by-parts lemma; and takes
`w' = w + apm_m98J02_constantDistribution`. Cancellation plus the compiled
nonzero lemma proves `w' ≠ w`, and the compiled homogeneous-addition lemma proves
that `w'` solves the same equation.

- Layer 1, fully parallel: `riemannKernel_spec`,
  `regularDistribution_of_continuous`, `regular_solution_solves`.
- Layer 2: `goursat_spec` after the kernel lemma.
- Layer 3: `pullback_spec` after the Goursat lemma.
- Layer 4: already-complete `partD` and `apm_m98j02` assembly.

There are **five** open lemmas. The riskiest is `goursat_spec`, specifically
locating or building the fixed-domain parametric integral regularity argument.
I am confident in the statement of every leaf; no mathematical doubt remains.

## Compilation and axioms

`Blueprint.lean` compiles with the prescribed command. Its final output is:

```text
'apm_m98j02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The only new uses of `sorryAx` are the five named leaves above; the main
theorems contain no `sorry`.
