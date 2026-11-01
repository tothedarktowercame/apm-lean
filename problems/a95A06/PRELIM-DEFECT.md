# Preliminary defect report: a95A06

## Exact failing claim

Part (b) asks one to demonstrate that “there is no open set $U$ that properly
contains $\Delta$ and has an analytic function $F$ defined on it with
$F(z)=f(z)$ for every $z\in\Delta$.”  This is false because an arbitrary open
set need not be connected.

## Complete counterexample

Let
\[
U=\Delta\cup B(2,1/10).
\]
The two disks are disjoint.  Thus $U$ is open and properly contains $\Delta$.
Define
\[
F(z)=\begin{cases}
f(z),&z\in\Delta,\\
0,&z\in B(2,1/10).
\end{cases}
\]
This is well-defined and analytic on $U$: analyticity is local, and on the two
open components $F$ is respectively the analytic function $f$ and the constant
zero function.  It agrees with $f$ at every point of $\Delta$, contradicting
the printed part (b).

## Evident intent and smallest correction

The title/content and the hint about radial derivative growth at rational
angles show that the intended assertion is that the unit circle is a natural
boundary.  Analytic continuation is normally considered on a region, meaning
a connected open set.  The smallest correction is therefore to replace “open
set $U$” by “connected open set $U$” (equivalently here, “open region $U$”).
One could instead require every component of $U$ to meet $\Delta$, but that is
a less direct, more elaborate repair than the standard connected-region
formulation.

## Clauses which stand as printed

Part (a) stands unchanged: for the literal series beginning at $n=1$, $f$ is
continuous on the closed unit disk and analytic on the open unit disk.  In part
(b), the proper containment, analyticity, and agreement clauses also stand as
printed.  Only connectedness of $U$ is added.  The Lean theorem likewise uses
the literal $n=1$ tail; it does not add the duplicate $n=0$ term.
