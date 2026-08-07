# Proof Outline: m96J06

The Lean artifact formalizes the restricted continuous-function Banach space,
the bounded linear involution, and the core pointwise quadratic estimate. The
fixed-point assembly remains.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m96J06.md`

## Formalized

- Both half-shifted arguments remain in `[-2,2]`.
- The quadratic term preserves restricted continuity and satisfies the
  pointwise two-radius Lipschitz estimate.
- The linear part is bundled on `C(Icc (-2) 2, ℝ)` as a continuous linear map,
  has norm bound three, and is its own inverse.
- Both half-shifts are bundled as continuous interval self-maps. Their product
  defines `apm_m96J06_quadraticC`, with the compiled bound
  `‖apm_m96J06_quadraticC x‖ ≤ r²` on the radius-`r` ball.
- The quadratic difference satisfies
  `‖Q x - Q z‖ ≤ 2 * r * ‖x-z‖` on the radius-`r` ball, compiled as
  `apm_m96J06_quadraticC_sub_norm_le`.

## Closer hop 2 progress

- The nonlinear term now lives in the actual continuous-function Banach
  algebra, rather than only as an unbundled restricted function.
- The quadratic size estimate needed for self-mapping is complete. The
  remaining quantitative lemma is its sup-norm Lipschitz estimate on a ball,
  followed by composition with the norm-three involution.

## Closer hop 3 progress

- The full continuous-map sup-norm Lipschitz estimate is proved. At radius
  `1/12`, composing with the norm-three linear involution gives contraction
  constant `1/2`; no further nonlinear estimate is required.

## Remaining Boundary

Define the fixed-point map on the closed-ball subtype of radius `1/12`, prove
its self-map estimate from `‖y‖ < 1/48` and `‖Q x‖ ≤ 1/144`, apply
`ContractingWith.exists_fixedPoint'`, and extract its continuous map as the
raw-function witness.
