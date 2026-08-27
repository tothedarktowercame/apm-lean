# T00A01 Mayer–Vietoris endpoint adapter

`T00A01MayerVietorisAdapters.lean` proves that the actual production
reassembly map

`H₀(U) ⊞ H₀(V) ⟶ H₀(X)`

is epic for an open two-cover.  The proof uses the already-compiled short
exact sequence of cover-small chain complexes and the fact that degree zero
has no outgoing differential; it then transports the result through the
production comparison isomorphisms.

The file also transports the existing homotopy-equivalence invariance theorem
from additive commutative groups to the `ModuleCat ℤ` presentation used by the
frozen problem.

Finally, `isIso_middle_of_two_exact_of_isZero_ends` packages the generic
four-object exact-sequence step used in degree three: two consecutive exact
triples with zero outer terms make the shared arrow an isomorphism.

`h0SubspaceInclusionIso` packages the augmentation proof that a subspace
inclusion induces an H₀ isomorphism when both spaces are nonempty and carry
chosen integral H₀ coordinates.

For `t00A01`, these supply the bottom endpoint, homotopy transport, and the
top-degree algebraic step. `openCoverH0IsoOfCoordinates` now combines the
production inclusion normalization, augmentation isomorphisms, epic H₀
reassembly, and the conjugated signed-diagonal cokernel to compute ambient H₀.
`productionConnecting_isIso_of_pieces_isZero` packages the top-degree
connecting-map calculation, while
`groupHomologyIsZeroOfModuleHomologyIsZero` moves frozen vanishing hypotheses
back to the additive-group presentation.
`productionIntersectionArrow_mono_zero_of_coordinates` exposes the actual
degree-zero overlap arrow's monicity needed for the H₁ exactness argument.
This file still does not claim that
the frozen homology bridge closes; the cover-specific all-degree assembly has
not yet been wired into Main.
