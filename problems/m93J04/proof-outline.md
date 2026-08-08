# Proof Outline: m93J04

The frozen Lean theorem is present in `lean/Main.lean`. The two kernel branch
normal forms and algebraic derivative jump `1 / y²` are proved. Test-function
values and first derivatives now vanish at both outer endpoints; the set
integral splitting and second-derivative normalization also compile.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m93J04.md`

## Completed proof

The final calculation is routed through explicit primitives rather than four
separate integrations by parts. On `[0,y]` the primitive is
`(log y / y²) * (x³ φ' + 2x² φ)`; on `[y,1]` it is
`(x³ log x φ' + x²(2 log x - 1)φ) / y²`. Their derivatives are exactly the
two weighted formal-adjoint integrands. The interval FTC evaluates both
branches, the support hypothesis kills the outer endpoint terms, and the two
values at `y` simplify to `φ y`.
