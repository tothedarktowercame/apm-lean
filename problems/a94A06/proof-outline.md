# Proof Outline: a94A06

## Problem

Evaluate $\int_0^\infty x^7/(1+x^{12}) dx$ using the residue theorem on a
pie-slice contour of angle $\pi/6$.

## Informal proof

The pie-slice contour relates the integral along the real axis to the integral
along the ray at angle $\pi/6$, where $(re^{i\pi/6})^{12} = r^{12}$. The sole
pole in the sector $0 < \arg z < \pi/6$ is $z_0 = e^{i\pi/12}$, with residue
$e^{-i\pi/3}/12$. Combining the pieces: $I(1 - e^{4i\pi/3}) = 2\pi i \cdot
e^{-i\pi/3}/12$. Equating real parts: $I = \pi\sqrt{3}/18$.

## Formalization (Lean 4)

Rather than formalizing the residue theorem (which requires extensive
complex-analysis machinery), the Lean proof uses a **real-variable approach**:

1. **Antiderivative via partial fractions.** The substitution $u = x^4$
   transforms the integral to $(1/4)\int_0^\infty u/(1+u^3) du$. The
   antiderivative of $u/(1+u^3)$ is found by partial fractions:
   $$H(u) = -\tfrac{1}{3}\ln(u+1) + \tfrac{1}{6}\ln(u^2-u+1) + \tfrac{\sqrt{3}}{3}\arctan\tfrac{2u-1}{\sqrt{3}}$$

2. **Verification of $H'(u) = u/(1+u^3)$.** ✓ Verified in Lean.
   Each piece's derivative is computed using `HasDerivAt.log`,
   `HasDerivAt.arctan`, and chain rule, then combined algebraically.
   Key challenge: `field_simp` + `ring` fails on polynomial denominators
   (e.g., $u^2 - u + 1$) unless the denominator is first normalized to match
   the nonzeroness hypothesis form (e.g., `1 - u + u^2`).

3. **Antiderivative $G(x) = (1/4) H(x^4)$.** Expanded directly:
   $$G(x) = -\tfrac{1}{12}\ln(x^4+1) + \tfrac{1}{24}\ln(x^8-x^4+1) + \tfrac{\sqrt{3}}{12}\arctan\tfrac{2x^4-1}{\sqrt{3}}$$

4. **Verification of $G'(x) = x^7/(1+x^{12})$.** ✓ Verified in Lean.
   Written directly without `HasDerivAt.comp` (which has defeq issues with
   natural-number powers).

5. **$G(0) = -\pi\sqrt{3}/72$.** ✓ Verified using `arctan_inv_sqrt_three`.

6. **$\lim_{x\to\infty} G(x) = \pi\sqrt{3}/24$.** ⏳ Remaining.
   The log terms cancel ($\to 0$), and $\arctan \to \pi/2$.

7. **$\int_0^\infty = G(\infty) - G(0) = \pi\sqrt{3}/24 + \pi\sqrt{3}/72 = \pi\sqrt{3}/18$.** ⏳ Remaining.

## Key technical challenges encountered

- **`field_simp` + `ring` on polynomial denominators**: When the denominator
  is a polynomial like $u^2 - u + 1$, `field_simp` normalizes it to
  $1 - u + u^2$ but doesn't clear it without an explicit nonzeroness
  hypothesis in the SAME normalized form. Fix: `rw [show u^2 - u + 1 = 1 - u + u^2 from by ring]`
  before `field_simp [hq]`.

- **`HasDerivAt.comp` defeq issue with `npowRec`**: When composing
  `HasDerivAt H ... (x^4)` with `HasDerivAt (fun y => y^4) ... x`, the
  defeq check fails because `x^4` reduces via `npowRec` differently in
  the two positions. Fix: write $G$ directly (expanded) instead of using
  composition.

- **`polyrith` unavailable**: The external service for `polyrith` has been
  shut down, making field identity proofs harder.

## Files

- `informal-solution.md`: harvested informal proof
- `lean/Main.lean`: Lean 4 partial proof (2 sorries)
