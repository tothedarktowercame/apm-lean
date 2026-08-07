# Proof Outline: m99J01

The unique real fixed point of cosine is constructed by the intermediate value
theorem and proved unique using strict antitonicity of cosine on `[0,π]`.
Closer hop 1 additionally proves that `x ↦ cos x - x` is globally Lipschitz
with constant two and that every fixed point defines the constant equilibrium
in the exact frozen solution predicate.

The remaining bridge is global Picard–Lindelöf existence as a single global
`C¹` representative.  Once available, `ODE_solution_unique_univ` gives
uniqueness; no crossing of the compiled constant equilibrium then yields the
monotone trapping and convergence argument.
