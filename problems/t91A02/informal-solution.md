<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t91A02: A covering would force a non-integer number of sheets

## Why It's Hard

The statement is a *non-existence* claim — no covering map `N_{16} \to N_8` exists — and non-existence is
hard to attack head-on, since one cannot inspect "all possible maps." The trick is to find a single
numerical invariant that any covering would have to respect, and show the numbers are incompatible. The
right invariant is the **Euler characteristic**, which is multiplicative under finite covers:
`\chi(\text{total space}) = (\#\text{sheets}) \cdot \chi(\text{base})`. The only subtlety is justifying that
the number of sheets is a finite positive integer (so that divisibility is the real constraint) — which
follows because both surfaces are compact. Once that is in place, the obstruction is pure arithmetic: `6`
does not divide `14`.

## The Key Insight

For the non-orientable surface `N_k = \#^k \mathbb{RP}^2`, `\chi(N_k) = 2 - k`. A covering of a compact
space by a compact space is finite-sheeted, and Euler characteristic multiplies by the number of sheets `n`:

$$\chi(N_{16}) = n \cdot \chi(N_8) \ \Longrightarrow\ -14 = n\cdot(-6) \ \Longrightarrow\ n = \frac{14}{6} = \frac{7}{3}.$$

Since `n` must be a positive integer, this is impossible. Hence no covering `N_{16} \to N_8` exists.

## Complete Proof

Let `N_k = \#^k \mathbb{RP}^2` be the connected sum of `k` projective planes, a closed (compact, without
boundary) connected surface. Its Euler characteristic is

$$\chi(N_k) = 2 - k,$$

since `\chi(\mathbb{RP}^2) = 1` and each connected sum drops `\chi` by `2` (`\chi(A \# B) = \chi(A) + \chi(B) - 2`).
Thus

$$\chi(N_{16}) = 2 - 16 = -14, \qquad \chi(N_8) = 2 - 8 = -6.$$

**Suppose, for contradiction,** that there is a covering map `p : N_{16} \to N_8`.

**The number of sheets is a finite positive integer.** Since `N_8` is connected, the cardinality of the
fiber `p^{-1}(y)` is the same for all `y \in N_8`; call it `n` (the number of sheets). Each fiber is a
discrete closed subset of the compact space `N_{16}`, hence finite, so `n \in \{1, 2, 3, \dots\}`.

**Euler characteristic multiplies.** For an `n`-sheeted covering of a finite CW complex, lifting a CW
structure of the base `N_8` produces a CW structure on `N_{16}` with exactly `n` times as many cells in each
dimension; therefore

$$\chi(N_{16}) = n \cdot \chi(N_8).$$

**Arithmetic contradiction.** Substituting the values,

$$-14 = n \cdot (-6) \ \Longrightarrow\ n = \frac{-14}{-6} = \frac{7}{3},$$

which is not an integer. This contradicts `n \in \mathbb Z_{>0}`. Therefore no covering map
`N_{16} \to N_8` exists:

$$\boxed{\ \#^{16}\mathbb{RP}^2 \text{ is not a covering space of } \#^{8}\mathbb{RP}^2.\ }\qquad\blacksquare$$

**Remark.** The obstruction is pure divisibility: `N_{16}` can cover `N_8` only if `\chi(N_8) = -6` divides
`\chi(N_{16}) = -14`, and `6 \nmid 14`. Equivalently, the genus relation for an `n`-fold cover `N_{nk - 2(n-1)}\to N_k`
(from `\chi` multiplicativity) would require `16 = 8n - 2(n-1) = 6n + 2`, i.e. `n = 7/3`. The same Euler-
characteristic test decides covering questions among surfaces in general: a closed surface `S` can cover a
closed surface `B` only if `\chi(B) \mid \chi(S)` with quotient a positive integer (plus orientation/`\pi_1`
compatibility, not even needed here). Here the divisibility already fails, so the finer invariants are
unnecessary.
