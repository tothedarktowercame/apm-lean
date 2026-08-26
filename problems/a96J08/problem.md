# a96J08

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a96J08.md`
- imported-at: `2026-07-13T17:26:52.732845Z`

## Statement correction (2026-08-26)

The Lean target was registered as **I = -π cot(πω)**, transcribed faithfully from
the boxed answer in `informal-solution.md`. **That boxed answer is wrong.**

The informal derivation is sound right up to its last line, ending at

    I(1 - e^{2πiω}) = -πi(1 + e^{2πiω})

and since (1 + e^{2iθ})/(1 - e^{2iθ}) = i·cot θ, this gives

    I = -πi · (i cot πω) = +π cot(πω)

The sign flipped in the boxing, and the "equivalently I = π cot(π(1-ω))" line
carried the same slip forward. The formalisation was not at fault.

Frame f45's Solver established this independently and with axiom-clean
refutations — `not_tendsto_truncation_quarter_neg_pi` (ω = 1/4: truncations have
positive real part against a -π target) and
`not_tendsto_truncation_three_quarters_pos_pi` (ω = 3/4: negative against +π),
both depending only on [propext, Classical.choice, Quot.sound]. ω = 1/2 cannot
discriminate, since cot(π/2) = 0 under either sign, which is why two instances
were needed.

f45 was voided on this finding and the problem recast for f46 with the corrected
target.

## Problem Statement

Raw TeX source:

```tex
Evaluate the integral $\int_{-\infty}^{\infty}e^{\omega x}/(1-e^x)dx$,
where $\omega$ is a complex number with $0<\Re(\omega)<1$.
```
