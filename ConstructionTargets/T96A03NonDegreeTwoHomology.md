# T96A03 homology outside degree two

This target computes the integral singular homology of the generic equator
gluing `EquatorGluing 2 h` in every degree except two.  It uses the three
homotopy equivalences from `SphereEquatorGluingOpenCover`, the production
two-open-set Mayer--Vietoris sequence, and the existing integral sphere
homology calculation.

The degree-zero proof uses the actual signed overlap arrow and the generic
signed-diagonal cokernel calculation.  The degree-one proof uses vanishing of
the two sphere-piece groups, exactness at the union and pieces, and monicity
of the connected overlap's degree-zero arrow.  Above degree two, exactness at
the union has zero objects on both sides.

The result is stated in `ModuleCat ℤ`, so it can be transported through a
homeomorphism into a frozen presentation.  This module deliberately does not
calculate degree two, split its short exact sequence, or claim the frozen
problem is closed.
