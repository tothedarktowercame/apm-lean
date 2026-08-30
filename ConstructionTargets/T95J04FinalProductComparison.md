# Final product comparison for t95J04

`T95J04FinalProductComparison.lean` proves that `S² × S⁴` is not homeomorphic
to `S³ × S³` by comparing integral singular homology in degree two.

The left product has nonzero `H₂`: the first factor `S²` is a retract after
choosing the canonical pole of `S⁴`, and the banked sphere computation says
the top homology of `S²` is nonzero.  The right product has zero `H₂` by the
reviewed pole-cover Mayer--Vietoris calculation.  The canonical comparison
from additive-group homology to integral-module homology puts both statements
in `ModuleCat ℤ`.  Functorial transport across a hypothetical homeomorphism
would then make the nonzero left object zero.

The proof uses neither Eilenberg--Zilber nor a Künneth theorem and does not
address the remaining Sard branch of the frozen problem.
