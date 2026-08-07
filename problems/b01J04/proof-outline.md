# Proof Outline: b01J04

## Result

Closer hop 3 proves the forward implication of simultaneous diagonalization
and completely proves the inverse-polynomial assertion. One boundary remains:
constructing a simultaneous eigenbasis from two commuting diagonalizable
complex matrices.

## Proved

1. Two diagonal conjugates commute by `Matrix.commute_diagonal`; cancellation
   by the nonsingular inverse of the conjugating matrix gives `A * B = B * A`.
2. For an invertible matrix over an arbitrary field,
   `Matrix.det_eq_sign_charpoly_coeff` shows the constant coefficient of the
   characteristic polynomial is nonzero.
3. `Polynomial.X_mul_divX_add` and `Matrix.aeval_self_charpoly` give
   `A * aeval A charpoly.divX + c₀ I = 0`.
4. Scaling `charpoly.divX` by `-c₀⁻¹` constructs the required polynomial
   whose evaluation is `A⁻¹`.

## Remaining Boundary

Mathlib's joint generalized-eigenspace theorem, found through sibling
`b93J03`, gives the relevant `iSup/iInf` decomposition. No theorem was found
that assembles this decomposition into the common eigenbasis required by the
frozen matrix-conjugation statement. This local direct-sum/basis construction
is the sole remaining sorry.
