# m97A04

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m97A04.md`
- imported-at: `2026-07-13T17:26:55.676861Z`

## Problem Statement

Raw TeX source:

```tex
Explain how the two-point boundary value problem $u''+au'+bu=c$
($0<t<1$), $u(0)=u(1)=0$ can be solved numerically using the formulas
$u''(t)\approx h^{-2}[u(t+h)-2u(t)+u(t-h)]$, $u(t)\approx
(2h)^{-1}(u(t+h)-u(t-h))$. Exhibit the system of equations that must
be solved. Prove that if $b(t)<0$ for all $t$ then for small values of
$h>0$ the linear equations have a unique solution.
```
