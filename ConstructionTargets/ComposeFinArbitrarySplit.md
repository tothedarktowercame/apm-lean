# ComposeFinArbitrarySplit

`composeFin_dropLast_two` proves the structural decomposition that removes the
last two arrows of a dependent finite categorical composite. Its prefix uses
two literal `Fin.castSucc` restrictions, so the theorem does not rewrite a
dependent arrow family through arithmetic casts.

The remaining arbitrary two-block theorem must iterate this decomposition and
use `composeFin_front_tail_absorbed` to absorb the reindexing transports at
each successor.  Its concatenated-subdivision specialization must then apply
the banked left/right mapped-piece conjugation formulas.  No evaluation or
quotient composition law is claimed here.
