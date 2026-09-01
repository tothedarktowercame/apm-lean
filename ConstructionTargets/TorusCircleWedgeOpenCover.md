# Torus–circle point-wedge open cover

This target constructs the reusable geometric cover of the point wedge of a
torus and a circle. The punctured-circle set `M` and punctured-torus set `N`
are literal inequalities against `-1`; `U` and `V` are their quotient images.
The target proves that both are open, cover the wedge, and have intersection
exactly `restrictedOpen N M`.

`UModel`, `VModel`, and `UVModel` normalize the restricted quotient spaces to
wedges of the corresponding punctured factors. Their representative formulas
record the left, right, and selected-basepoint coordinates needed by later
consumer adapters.

The generic `pointedWedgeHomeomorph` transports wedges through pointed
homeomorphisms. The generic `wedgeSwap` exchanges summands and sends the glued
basepoint to the glued basepoint in the required orientation.
`wedgeHomotopyEquivRight` derives right-summand contraction by composing this
symmetry with `wedgeHomotopyEquivLeft`; it does not duplicate quotient descent.
Together with the fully typed contraction equivalence to `Unit`, this yields
the exact equivalences `U ≃ₕ Circle × Circle`, `V ≃ₕ Circle`, and
`U ∩ V ≃ₕ Unit`.

The authoritative fixture also reproduced the frozen `t02A03` quotient
relation and compiled an identity-on-representatives homeomorphism from this
generic wedge to that local presentation. Those declarations are deliberately
omitted here to avoid a ConstructionTarget dependency on a frozen `Main`.
A later problem-facing adapter can transfer `U`, `V`, and the three homotopy
equivalences to the frozen `apm_t02a03_*` names. `t97J04` is the other exact
consumer of this reusable geometry.
