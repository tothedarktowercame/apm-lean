# A vertical family for one homotopy-grid strip

This target chooses the left vertical edge of the following cell at every
nonterminal row vertex and the right edge of the final cell at the terminal
vertex. `stripVertical_succ_eq_right` reconciles every interior choice with
the preceding cell's right edge by the overlap equation.

`strip_composeFin_square` specializes the generic categorical ladder theorem:
the bottom composite followed by the terminal vertical equals the initial
vertical followed by the top composite.

The next step is to prove that the initial and terminal vertical morphisms are
identities from the relative-endpoint condition on the homotopy, and then
insert the outer endpoint transports from `TwoOpenDescentDatum.evaluate`.
