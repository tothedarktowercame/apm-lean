# Proof Outline: m99J01

The unique real fixed point of cosine is constructed by the intermediate value
theorem and proved unique using strict antitonicity of cosine on `[0,π]`.
Closer hop 1 additionally proves that `x ↦ cos x - x` is globally Lipschitz
with constant two and that every fixed point defines the constant equilibrium
in the exact frozen solution predicate.

Closer hop 2 proves `apm_m99j01_solution_unique`: any two global `C¹`
representatives satisfying the frozen equation agree at every nonnegative
time. It applies Mathlib's `ODE_solution_unique` on each compact interval
`[0,t]`, so no negative-time ODE hypothesis is introduced.

The remaining bridge is global Picard–Lindelöf existence as a single global
`C¹` representative and the subsequent attraction proof. Uniqueness is now
closed; comparison with the compiled constant equilibrium can then support
the monotone trapping and convergence argument.

Closer hop 3 proves the global phase-line signs: `cos x - x > 0` below the
fixed point and `cos x - x < 0` above it. The proof handles values outside
`[-1,1]` by the global cosine bounds and uses strict antitonicity only on
`[0,π]`. Thus the pointwise direction needed for trapping is compiled; the
global representative and the calculus-to-monotonicity/convergence bridge
remain.
