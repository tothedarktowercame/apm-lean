# Degree-two Mayer–Vietoris calculation for the equator-gluing model

This target performs the reusable-model calculation for
`SphereEquatorGluingOpenCover.EquatorGluing 2 h`.

It derives the short exact sequence

`0 → H₂(S²) ⊕ H₂(S²) → H₂(EquatorGluing 2 h) → H₁(S¹) → 0`

from the actual production Mayer–Vietoris arrows. Monicity of the left map
comes from `H₂(S¹) = 0`; epicity of the connecting map comes from the
vanishing of both piecewise `H₁` groups. The quotient is identified with
`ℤ`, projectivity derives a section, and `ProjectiveQuotientExactSplitting`
splits the sequence. `T96A03DegreeTwoNormalization` then identifies the three
free coordinates with `Fin 3 → ℤ`.

The final declaration is `degreeTwoModuleIsoFinThree`.

This proves a result only for the reusable equator-gluing model. It does not
identify the frozen dependent quotient with that model and does not close the
frozen `t96A03` theorem.
