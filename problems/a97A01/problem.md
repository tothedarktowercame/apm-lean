# a97A01

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:16.982872Z`
- source-frame-id: `apm-v2-a97A01-1775003392734`
- source-module-root: `ApmCanaries.Frames.A97A01.Apm_v2_a97A01_1775003392734`

## Problem Statement

Raw TeX source:

```tex
Define a sequence of functions $f_n:[0,1]\rightarrow \R$ as follows:
$f_1(t)=1$ for all $t$ and there after $f_n(t)=1$ if $t\in
\{[(k-1)/2^n,k/2^n) \pipe k \text{odd}\}$, and $f_n(t)=1$ if $t\in
\{[(k-1)/2^n,k/2^n) \pipe k \text{even}\}$, and $f_{n}(1)=-1$ for all
$n>1$. Prove that if $f\in L^{\infty}([0,1])$ then $\lim_{n\rightarrow
\infty}\int_0^1 f f_n=0$.
```
