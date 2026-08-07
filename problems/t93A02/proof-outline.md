# Proof Outline: t93A02

The custom hyperspace embeds into Mathlib's complete extended-metric space of
closed sets via `t93A02H.toCloseds`.  Pairwise finite Hausdorff edistance and
the definitional edistance identity are compiled as
`t93A02H.hausdorffEDist_ne_top` and `t93A02H.edist_toCloseds`.
Closer hop 2 proves the sharper conversion
`t93A02H.edist_toCloseds_eq_ofReal_hausdorffDist`, expressing the extended
distance exactly as `ENNReal.ofReal` of the frozen real distance.
It then uses this identity in `t93A02H.cauchySeq_toCloseds`, completing the
translation to Mathlib's extended-metric `CauchySeq` predicate.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t93A02.md`

## Remaining boundary

Translate `IsT93A02HausdorffCauchy` into the uniform/extended Cauchy predicate
on `Closeds X`, invoke its complete-space instance, and prove that the limit
is nonempty and bounded.  Nonemptiness follows by tracking points through a
rapidly Cauchy subsequence; boundedness follows from finite distance to one
fixed bounded member.  Finally convert extended Hausdorff convergence back to
the stated real-valued `hausdorffDist` convergence.

`NonemptyCompacts` is not a valid shortcut: in a general complete metric
space, closed bounded sets need not be compact.  Repository and Mathlib
searches found no packaged theorem completing the preservation argument.  The
frozen statement is unchanged and appears sound.
