# EmbeddedCircleLift

Keyed to `t00J02`, this module isolates the continuous and categorical part of
the transverse inverse-image argument.

For an embedding `c : C(Circle, S)`, every continuous map with image in
`range c` lifts continuously through `c`.  After applying an arbitrary functor
`F : TopCat ⥤ D`, if `F.map c` is mono and the original map is sent to zero,
then the lift is sent to zero as well.  The component-level theorem accepts a
circle whose range lies in `f ⁻¹' range c`, which is the exact interface used
by `apm_t00J02_bridge_1`.

The remaining problem-specific step is geometric: use transversality and
Poincaré duality to turn the zero winding of all lifted components into
vanishing of the map on top singular homology.
