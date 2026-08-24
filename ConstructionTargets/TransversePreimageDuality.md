# TransversePreimageDuality

This module names the exact interface between the already reusable
null-winding preimage construction and a geometric Poincare-duality theorem.

`DetectsTopMap Hcircle Htop f c` says that null winding of the parametrized
components of `f ⁻¹' range c`, measured by `Hcircle`, forces the morphism
induced by `f` under `Htop` to vanish.  A differential-topology development can
prove this predicate using its preferred orientation and intersection theory;
consumers then use the axiom-free eliminator `map_eq_zero`.

The interface is functor-generic and does not bake the genus-two surface or
integral singular homology into the categorical boundary.

## Verification

The module ends with `#print axioms` for `map_eq_zero`.  Its elaborated output
is `[propext, Classical.choice, Quot.sound]`; in particular, the library
increment itself has no `sorryAx`.  The keying problem remains open only in the
separate geometric proof that produces `DetectsTopMap`.
