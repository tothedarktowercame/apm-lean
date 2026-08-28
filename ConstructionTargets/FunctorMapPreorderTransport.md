# Functor-map transport from preorders

This target proves a typed transport formula for a functor whose source is a
preorder.  Given propositional equalities of the source and target objects, the
formula explicitly conjugates the new functor map by `eqToHom` maps.  The proof
eliminates the object equalities first and only then uses uniqueness of arrows
in the thin source category.

`comp_map_eq_eqToHom_comp_map_comp_eqToHom` is the restriction/precomposition
form used by finite-chain comparisons.  It does not assert equality of
functors or eliminate dependent functor expressions.
