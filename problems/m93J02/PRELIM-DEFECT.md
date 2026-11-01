# Defects and conventions in the preliminary statement

The displayed denominator in the global seminorm is printed as
`|x-y^α|`.  This is a typographical error: throughout the formalization it is
read as `|x-y|^α`, the standard Hölder quotient and the denominator matching
the local definition.

The statement also leaves the range of `α` unspecified.  We use the standard
strict Hölder convention `0 < α < 1`.  This restriction is mathematically
substantive, not merely a convenience.  At `α = 1` the answers can depend on
the geometry of `Ω`: for an interval, for example, the local and global
Lipschitz seminorms agree, the reverse comparison holds, and the local normed
space is complete.  Thus the blanket negative comparison and incompleteness
claims valid in the strict Hölder range cannot be asserted for every compact
connected set at `α = 1`.

The source permits a one-point compact connected set.  The registered theorem
therefore treats it separately: both seminorms vanish, both comparisons hold,
and both norms are complete.  In Mathlib `IsConnected U` includes nonemptiness,
so there is no additional empty-set case under the theorem's hypotheses.
