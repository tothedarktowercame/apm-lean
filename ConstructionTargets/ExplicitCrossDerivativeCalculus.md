# Explicit cross-derivative calculus

This target proves the local analytic bridge for frozen `t97J08`.  The angle
form is evaluated on `1` and `Complex.I`, reducing it to the two coefficient
functions `-y/(2πr²)` and `x/(2πr²)`.  The file constructs their actual
Fréchet derivatives from the continuous real and imaginary projections,
product calculus, and inversion calculus.

`beta_cross_derivatives` proves the required cross evaluation equality away
from zero.  `beta_closed_on_puncturedPlane` combines that calculation with
the honest differentiability witnesses and exactly matches the frozen
closedness predicate.  No winding number, loop integral, circle invariant, or
final theorem is assumed.
