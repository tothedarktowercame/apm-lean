# m98J02

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m98J02.md`
- imported-at: `2026-07-13T17:26:55.970159Z`

## Problem Statement

Raw TeX source:

```tex
Let $u$ and $v$ be distributions (\ie\ $u$ and $v$ in $\mathcal{D}'$).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Define what it means for $u$ to have compact support.
%------------------------------------------------------------------*
\item Define the convolution $u\ast v$ of $u$ and $v$ assuming $u$ has
compact support.
%------------------------------------------------------------------*
\item Show that $u \ast v$ is a distribution.
%------------------------------------------------------------------*
\item Suppose that $T=2
\pbypk{x}{2}-\pbypk{y}{}+3\frac{\partial^2}{x\partial y}$ with $f\in
C^2(\Rtw)$ and $T w_0=\delta_0$ where $\delta_0$ is the dirac point
mass distribution at the origin. Find any distributional solution $w$
to $Tw=f$ and show that $w\in C^2(\Rtw)$. Is the solution unique?
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```

## Interpretation note (2026-10-18)

Part (d) can be read in two ways, and they differ in difficulty.

1. **Narrow reading.** The hint `T w_0 = \delta_0` suggests the answer
   `w = f * w_0`. Part (b) defines convolution only when one factor has
   compact support, so on this reading `f` is implicitly compactly supported.
   One must also take `w_0` to be a regular distribution given by a locally
   integrable function: `T` is not hypoelliptic, so for some fundamental
   solutions `f * w_0` involves third derivatives of `f` and is not `C^2`.
   On this reading `w = f * w_0` is `C^2` because derivatives fall on `f`.
2. **Printed reading.** `f` is an arbitrary `C^2(\mathbb R^2)` function, as
   written. Then neither `f` nor `w_0` need have compact support, `f * w_0`
   need not be defined, and the solution has to be built from the forward and
   backward fundamental solutions `E_\pm`, which are supported in opposite cones:
   `w = E_+ * (\chi f) + E_- * ((1-\chi) f)` (see `informal-solution.md`).

Under both readings the solution is not unique: adding a constant gives a second
solution.

The competition statement (`lean/Main.lean`, `apm_m98j02`) uses the printed
reading and is open. The narrow reading is proved, with no sorries, in
`out-of-competition/Main.lean` (`apm_m98j02_compactF`). That proof is recorded
as an out-of-competition finding and does not count as a closure of m98J02.
