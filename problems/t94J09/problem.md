# t94J09

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t94J09.md`
- imported-at: `2026-07-13T17:26:58.149750Z`

## Problem Statement

Raw TeX source:

```tex
Classify the polygon with edges labeled
$acd^{-1}g^{-1}fe^{-1}bc^{-1}d^{-1}g^{-1}e^{-1}fab.$ (Note: all the
vertices are the same, except the ones between $d^{-1}$ and $g^{-1}$,
which form a second distinct vertex.)

\soln{Apparently you can do this with Euler number?

Anyway, { \tt ac-d-gf-eb-c-d-g-efab } is the connected sum of three
real projective planes according to kind.c (not necessarily to be
trusted!).

The output stream was

Getting rid of a vertex... ac-d-gf-eb-c-d-g-efab --> ac-gf-eb-c-dd-g-efab

Folding... ac-gf-eb-c-dd-g-efab --> ac-gf-eb-c-g-efab 

Consolidating a twisted pair... ac-gf-eb-c-g-efab --> aab-cg-fe-bcge-f

Consolidating a twisted pair... aab-cg-fe-bcge-f --> aab-cgge-ff-eb-c

Consolidating a twisted pair... aab-cgge-ff-eb-c --> aabb-cc-g-g-ef-fe

Folding... aabb-cc-g-g-ef-fe --> aabb-g-g-ef-fe 

Folding... aabb-g-g-ef-fe --> aabb-g-g-ee 

Folding... aabb-g-g-ee --> aabb-g-g 

Connected sum of 3 real projective planes.
}
```
