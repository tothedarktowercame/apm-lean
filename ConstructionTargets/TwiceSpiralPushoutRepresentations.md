# Twice-spiral pushout representations

`TwiceSpiralPushoutRepresentations.lean` defines the category of actions of
the existing `TwiceSpiralPushout d` on objects of a groupoid.

For coordinate vertex data, the right integer action is transported onto the
left target by `baseGlue.symm.conj`.  The original boundary compatibility then
proves equality with the left action along the literal maps
`leftBoundaryHom` and `rightBoundaryHom d`.  The resulting pushout action is
constructed by Mathlib's `Monoid.PushoutI.lift`; its values on both canonical
legs are recorded by simp theorems using `PushoutI.lift_of`.

Conversely, a pushout action restricts along the two `PushoutI.of` maps and
uses identity glue.  Its compatibility is derived from
`PushoutI.of_comp_eq_base`.

The remaining packet is morphism transport.  In the coordinate-to-pushout
direction the left intertwiner must also be shown to intertwine the
baseGlue-conjugated right action, using `baseGlue_square`; after that,
`PushoutI.hom_ext_nonempty` supplies the action intertwining for every pushout
element.  The two functors and their equivalence can then be packaged without
adding any group-pushout assumption.
