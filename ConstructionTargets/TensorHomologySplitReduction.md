# Tensor homology split reduction

`TensorHomologySplitReduction.lean` supplies the strongest bounded algebraic
step reached directly from the pinned Mathlib tensor-complex API without a
spectral sequence or an assumed Künneth theorem.

The declarations `tensorHomotopyLeft` and `tensorHomotopyRight` specialize
Mathlib's bifunctor homotopy construction to `HomologicalComplex.tensorObj`.
The two one-factor homology theorems and
`tensorHomologyMap_eq_of_homotopies` prove that supplied chain homotopies make
the corresponding tensor-complex homology maps equal. The reflexive fixture
checks the interface without adding a vanishing premise.

This is a genuine prerequisite for the field argument: the contraction maps
from an explicit split complex can now be transported through the tensor
product at the homotopy and homology-map levels. It does **not** construct
those splittings or package the resulting maps as a homotopy equivalence. In
particular, it does not assert a direct-sum formula for arbitrary complexes,
an Eilenberg--Zilber comparison, or any topological product statement.

The exact remaining algebraic producer is a compiled construction, over a
field, of the cycle/boundary complement data and a homotopy equivalence from a
chain complex to the graded complex of its homology objects (with zero
differential), followed by the diagonal direct-sum calculation for the tensor
of two zero-differential graded complexes. The generic natural isomorphism was
therefore not claimed in this bounded round: those complement choices are not
packaged as a homological-complex splitting theorem in the pinned Mathlib.
