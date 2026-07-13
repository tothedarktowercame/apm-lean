# Proof Outline: a01A03

## Problem

For g ∈ L¹(ℝ) and any f ∈ C¹(ℝ), suppose g ∗ f'(x) = f(x+h) - f(x-h).
Show that g ≡ χ_{[-h,h]}.

## Harvest Mismatch Note

The informal-solution file `apm-a01A03.md` contains the proof for **a01A02**
(weak-L² implies local L¹), not a01A03 (convolution identity). The proposed
Lean statements are for the weak-L² problem. This bundle implements the
correct problem from `a01A03.tex`.

## Proof Strategy

Take Fourier transforms of both sides. The convolution theorem gives
F(g ∗ f') = ĝ · F(f') = ĝ · iξf̂(ξ). The right side gives
(e^{ihξ} - e^{-ihξ})f̂(ξ) = 2i sin(hξ)f̂(ξ). Since this holds for all f,
ĝ(ξ) = 2sin(hξ)/ξ. The inverse Fourier transform of this is χ_{[-h,h]}.

## Lean State

- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 1 (main theorem)
- **Classification**: partial
- **Blocker**: Fourier transform of L¹ convolutions + specific Fourier pair + injectivity of L¹ Fourier transform
