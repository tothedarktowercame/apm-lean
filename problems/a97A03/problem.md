# a97A03

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:17.049226Z`
- source-frame-id: `apm-v2-a97A03-1775003886693`
- source-module-root: `ApmCanaries.Frames.A97A03.Apm_v2_a97A03_1775003886693`

## Problem Statement

Raw TeX source:

```tex
If $f:[a,b]\rightarrow \R$ is absolutely continuous, prove that the
following are equivalent:

\begin{quotation}
There exists a positive constant $B$ such that $\forall x,y\in
[a,b]:|f(x)-f(y)|\leq B|x-y|$.
\end{quotation}

\begin{quotation}
There exists a positive constant $C$ such that for almost all $x\in
[a,b]:|f'(x)|\leq C$.
\end{quotation}

\soln{The first condition is that $f$ is Lipschitz with Lipschitz
constant $B$. The second condition is that the derivative of $f$ is
bounded.
(absolutely continuous function)\defn{
\item $F:A \subset \R\rightarrow\R$ 
\item $\forall \epsilon>0
: \exists \delta >0 
: \forall \{(a_1,b_1), \ldots, (a_N,b_N) \pipe i\neq j \Rightarrow (a_i,b_i) \cap (a_j,b_j) = \phi \} \subset \mathrm{domain}(F) 
: \sum_1^N (b_j-a_j) < \delta \Rightarrow \sum_1^N |F(b_j)-F(a_j)|<\epsilon$}
Need to show that ABC and L $\Rightarrow $ DB.
Need to show that ABC and DB $\Rightarrow $ L.
}
```
