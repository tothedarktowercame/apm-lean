# Proof Outline: a01A05

## Problem

Let {fₙ} be a sequence in L² with ‖fₙ‖=1 and |∫fₙfₘ| ≤ 2⁻ᵐ for n<m.
Let {eₙ} be a Gram-Schmidt orthonormalization with ‖eₙ‖=1.
(a) Show ‖fₘ - eₘ‖ ≤ 2⁻ᵐ.
(b) For any g ∈ L², show ∫gfₘ → 0.

Stated in general Hilbert space H (covers L² as special case).

## Harvest Mismatch Note

The informal-solution file `apm-a01A05.md` contains the proof for **a01A04**
(unit ball volumes), not a01A05 (Gram-Schmidt / nearly-orthogonal sequences).
The proposed Lean statements are for the ball volume problem. This bundle
implements the correct problem from `a01A05.tex`.

## Proof Strategy

(a) Gram-Schmidt: eₘ = uₘ/‖uₘ‖ where uₘ = fₘ - Σ⟨fₘ,eₙ⟩eₙ.
    Near-orthogonality bounds |⟨fₘ,eₙ⟩|, giving ‖fₘ-eₘ‖ ≤ 2⁻ᵐ.
(b) Bessel's inequality: Σ|⟨g,eₙ⟩|² ≤ ‖g‖², so ⟨g,eₙ⟩ → 0.
    Since ‖fₘ-eₘ‖ ≤ 2⁻ᵐ → 0, |⟨g,fₘ⟩-⟨g,eₘ⟩| → 0, hence ⟨g,fₘ⟩ → 0.

## Lean State

- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 2 (parts a and b)
- **Classification**: partial
