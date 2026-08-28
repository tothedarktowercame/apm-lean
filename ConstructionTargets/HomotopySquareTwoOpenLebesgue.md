# HomotopySquareTwoOpenLebesgue

This target applies Mathlib's metric Lebesgue-number theorem to the compact
square `unitInterval × unitInterval`.  For a continuous square and two open
sets covering its target, it produces one positive radius such that every
metric ball of that radius is mapped into one cover member.

Two reusable consequences are included.  An arbitrary subset contained in
one such ball is mapped into one cover member, and a set whose two coordinate
distances from a chosen point are both below the radius is small by the
product max metric.  The final theorem specializes the construction to
`Path.Homotopy`.

The next geometric packet chooses a natural-number mesh with reciprocal below
this radius, proves every closed grid cell is coordinatewise small, and
packages its Boolean label and full cell-image membership.  Only after that
certificate exists should the cell-boundary homotopies be compared through
the descent functors.
