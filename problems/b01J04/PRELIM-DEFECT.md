# Prelim defect

Part (a) as printed is false. Take n = 2 and A = B = [[0,1],[0,0]]. Then AB = BA, but no conjugate of A is diagonal, since A is nonzero and nilpotent.

The direction AB = BA ⇒ simultaneous diagonalisation needs A and B to be individually diagonalisable, and the reverse direction implies it. The correction adds exactly that (`apmMatrixDiagonalizable A`, `apmMatrixDiagonalizable B`) and nothing else. Part (b) is unchanged.
