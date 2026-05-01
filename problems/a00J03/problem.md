# a00J03

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:15.822323Z`
- source-frame-id: `apm-v2-a00J03-1774991806132`
- source-module-root: `ApmCanaries.Frames.A00J03.Apm_v2_a00J03_1774991806132`

## Problem Statement

Raw TeX source:

```tex
Let $(X,\mathcal{A},\mu)$ be a measure space and let
$\varphi:X\rightarrow X$ be a measurable bijection with measurable
inverse with $\mu(\varphi^{-1}A)=\mu(A)$ for all $A\in
\mathcal{A}$. Show that $T_{\varphi}:f\in
L^p(X,\mathcal{A},\mu)\rightarrow f\circ \varphi$ is an isometric
isomorphism on $L^p(X,\mathcal{A},\mu)$ for $1\leq p<\infty$.
```
