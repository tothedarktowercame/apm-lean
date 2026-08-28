# Solid-torus homotopy and integral homology

This target contracts the closed-disk coordinate of
`SolidTorusGluingOpenCover.SolidTorus` by the explicit formula
`x ↦ (1-t) • x`.  It proves that the formula remains in the closed unit disk,
is continuous, starts at the identity, ends on the literal circle core, and
fixes the core through the retraction/section equations.  The result is
packaged as `solidTorusHomotopyEquivCircle`.

Using homotopy invariance and the banked circle/sphere computations, without a
product or Kunneth theorem, it provides:

- `solidTorusH0IsoInt : H₀(SolidTorus; ℤ) ≅ ℤ`;
- `solidTorusH1IsoInt : H₁(SolidTorus; ℤ) ≅ ℤ`;
- `solidTorusHomology_isZero_of_one_lt` for every degree above one.

The homology results use the `ModuleCat ℤ` presentation required by frozen
`t01J03`.  This target does not compute the gluing map on homology, invoke
Mayer--Vietoris, or assert any frozen conclusion.
