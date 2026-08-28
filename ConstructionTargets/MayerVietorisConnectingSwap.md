# Mayer–Vietoris connecting-map swap

This target constructs the literal morphism from the production subcomplex
Mayer–Vietoris short complex for `(P,Q)` to the one for `(Q,P)`.  Its first
component is the negative intersection transport, its middle component is
biproduct symmetry, and its third component is the union transport.

`connecting_swap` applies `ConnectingMapNegationNaturality` to show that the
reversed connecting map is the negative original connecting map after the
intersection and union transports.

This does not compare the Mayer–Vietoris connecting map with the pair/excision
shift used for sphere homology, and therefore assumes neither the antipodal
recurrence nor the frozen `t94J08` conclusion.
