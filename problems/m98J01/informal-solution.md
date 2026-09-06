# Informal solution

**Open mapping theorem.** If (X,Y) are Banach spaces and
\(S:X\to Y\) is a bounded linear surjection, then (S) maps open subsets of
\(X\) to open subsets of (Y). Equivalently, there is (c>0) such that the
image of the open unit ball contains the ball (B_Y(0,c)).

**Closed graph theorem.** If (X,Y) are Banach spaces and a linear map
\(T:X\to Y\) has closed graph
\(G(T)=\{(x,Tx):x\in X\}\subseteq X\times Y\), then (T) is bounded
(and hence continuous). No continuity assumption on (T) is made.

Assume the open mapping theorem. Since (G(T)) is a closed subspace of the
Banach space (X\times Y), it is Banach. The first projection
\[
  P:G(T)\longrightarrow X,\qquad P(x,Tx)=x,
\]
is bounded, linear, and bijective. The open mapping theorem says that its
inverse (P^{-1}:X\to G(T)) is bounded. The second coordinate projection
\(Q:G(T)\to Y\) is bounded, and
\[
  T=Q\circ P^{-1}.
\]
Thus (T) is a composition of bounded linear maps and is bounded, proving the
closed graph theorem.
