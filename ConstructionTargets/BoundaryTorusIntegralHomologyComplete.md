# Boundary-torus integral homology completion

This target packages the banked Mayer--Vietoris calculations in the canonical
integral `ModuleCat ℤ` representation.  It normalizes H1 to `Fin 2 → ℤ`,
transports H2 to ℤ, and proves vanishing in every degree at least three by
using the production union exactness segment: the piece term and the next
overlap term both vanish, forcing the ambient term to vanish.

The exact remaining homology seam is degree zero.  The current production
Mayer--Vietoris sequence is indexed by natural degrees and does not contain
the terminal augmentation needed to prove that the H0 reassembly arrow is
epic.  A reusable connected-H0 theorem (or an augmented degree-zero
Mayer--Vietoris endpoint) is required to derive `H₀(BoundaryTorus) ≅ ℤ`.
Accordingly `boundaryTorus_positiveDegree_module_homology` states all proved
positive-degree and higher-vanishing clauses but does not assume the missing
H0 coordinate.

The fundamental-group conjunct of frozen `t01J03_bridge_1` is also outside
this target.
