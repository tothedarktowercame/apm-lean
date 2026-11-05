# Preliminary defect report: a97A07

## Exact failing claim

The problem asks to prove that the function
$P(z)=\frac{1}{2\pi i}\int_{\gamma}\frac{f(\zeta)}{p(\zeta)}\,\frac{p(\zeta)-p(z)}{\zeta-z}\,d\zeta$
"is a polynomial of degree $n-1$". The exact degree is false.

## Complete counterexample

Take $n=2$, $z_1=0$, $z_2=1/2$, $\gamma$ the unit circle traversed once
counterclockwise, and $f\equiv 1$. Both nodes are distinct and inside $\gamma$,
and $f$ is entire. Here $p(z)=z(z-\tfrac12)$ and
$\frac{p(\zeta)-p(z)}{\zeta-z}=\zeta+z-\tfrac12$, so
\[
P(z)=\frac{1}{2\pi i}\int_\gamma\frac{\zeta+z-\frac12}{\zeta(\zeta-\frac12)}\,d\zeta .
\]
By residues at $0$ and $\tfrac12$ this is
$\frac{z-\frac12}{-\frac12}+\frac{z}{\frac12}=1$. So $P\equiv 1$, which has degree $0$, not $1$.
In general $P$ is the interpolation polynomial of $f$ at the nodes, and its degree is
$n-1$ only when the top divided difference $f[z_1,\dots,z_n]$ is nonzero.

## Evident intent and smallest correction

The intended claim is that $P$ is a polynomial of degree at most $n-1$ that
interpolates $f$ at $z_1,\dots,z_n$: the Lagrange–Hermite interpolation formula.
The registered statement asks for `P.natDegree ≤ n - 1`. Every other clause of the
problem (an arbitrary Jordan curve, $f$ analytic inside and on it, the integral
as printed) is kept.
