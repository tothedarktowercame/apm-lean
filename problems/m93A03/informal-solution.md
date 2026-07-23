<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m93A03: Weak convergence plus norm convergence implies strong convergence (Radon–Riesz)

## Why It's Hard

The statement is true, but the temptation is to think weak convergence is "almost"
strong convergence and wave your hands. It is not: weak convergence alone is
genuinely weaker, and the standard cautionary example shows it. If `\{e_n\}` is an
orthonormal sequence, then `⟨e_n, g⟩ → 0` for every `g` (Bessel's inequality
forces the coefficients to be summable-square, hence to vanish), so `e_n \rightharpoonup 0`
weakly — yet `\|e_n\| = 1` for all `n`, so `e_n` does **not** converge to `0` in
norm. Weak convergence lets the "mass" of the vectors rotate off to infinity in
new directions without ever settling down.

So the hypothesis `⟨f_n, g⟩ → ⟨f, g⟩` cannot by itself give norm convergence. The
problem hands you a second hypothesis — `\|f_n\| → \|f\|` — and the entire content
is recognizing that *this is exactly the missing piece*, and that the inner-product
structure of a Hilbert space is what lets the two hypotheses combine. In the
orthonormal example the second hypothesis fails (`\|e_n\| = 1 \ne 0 = \|0\|`),
which is precisely why that example is not a counterexample here.

## The Key Insight

Do not try to estimate `\|f_n - f\|` by manipulating the vectors. Instead
**expand its square using the inner product** and watch every term converge:

$$\|f_n - f\|^2 = \|f_n\|^2 - 2\,\mathrm{Re}\,⟨f_n, f⟩ + \|f\|^2.$$

The norm hypothesis controls the first term (`\|f_n\|^2 → \|f\|^2`); the weak
hypothesis, applied with the *specific* test vector `g = f`, controls the middle
term (`⟨f_n, f⟩ → ⟨f, f⟩ = \|f\|^2`). The three pieces collapse to
`\|f\|^2 - 2\|f\|^2 + \|f\|^2 = 0`. The whole proof is this one algebraic identity;
the cleverness is entirely in choosing `g = f` as the test vector and in knowing to
square the norm so the inner product appears. This is the Radon–Riesz property
(also called the Kadec–Klee property): in a Hilbert space, weak convergence plus
convergence of norms upgrades to strong convergence.

## Complete Proof

**Claim.** Let `F` be a Hilbert space, `\{f_n\} \subseteq F`, and `f ∈ F`. Suppose

1. `⟨f_n, g⟩ → ⟨f, g⟩` for every `g ∈ F` (i.e. `f_n \rightharpoonup f` weakly), and
2. `\|f_n\| → \|f\|`.

Then `\|f_n - f\| → 0` (i.e. `f_n → f` in norm).

**Proof.** Expand the squared norm of the difference using the inner product. For
each `n`,

$$\|f_n - f\|^2 = ⟨f_n - f,\ f_n - f⟩
= ⟨f_n, f_n⟩ - ⟨f_n, f⟩ - ⟨f, f_n⟩ + ⟨f, f⟩.$$

Writing `⟨f, f_n⟩ = \overline{⟨f_n, f⟩}`, the two cross terms combine as
`⟨f_n,f⟩ + ⟨f,f_n⟩ = 2\,\mathrm{Re}\,⟨f_n, f⟩`, so

$$\|f_n - f\|^2 = \|f_n\|^2 - 2\,\mathrm{Re}\,⟨f_n, f⟩ + \|f\|^2. \tag{$\ast$}$$

Now take the limit as `n → ∞` of each term on the right of `(\ast)`:

- By hypothesis (2), `\|f_n\|^2 → \|f\|^2` (squaring is continuous).
- By hypothesis (1) applied to the particular test vector `g = f`,
  `⟨f_n, f⟩ → ⟨f, f⟩ = \|f\|^2`; taking real parts (which is continuous),
  `\mathrm{Re}\,⟨f_n, f⟩ → \|f\|^2`.

Therefore the right-hand side of `(\ast)` converges:

$$\lim_{n\to\infty} \|f_n - f\|^2 = \|f\|^2 - 2\|f\|^2 + \|f\|^2 = 0.$$

Hence `\|f_n - f\|^2 → 0`, and so `\|f_n - f\| → 0`. That is, `f_n → f` in norm. ∎

**Remark (why both hypotheses are needed).** The identity `(\ast)` makes the roles
transparent. Hypothesis (2) is essential: with an orthonormal sequence `\{e_n\}`,
`e_n \rightharpoonup 0` weakly but `\|e_n\| = 1 \not\to 0 = \|0\|`, and indeed
`(\ast)` gives `\|e_n - 0\|^2 = \|e_n\|^2 = 1 \not\to 0`. Hypothesis (1) is also
essential — it is what makes the cross term equal `\|f\|^2` in the limit; without
it the middle term is uncontrolled. Both together, and only together, force the
right-hand side to zero. This is special to inner-product spaces: the proof uses
the polarization of `\|f_n - f\|^2` into norm and inner-product pieces, which has
no analogue in a general Banach space (where the Radon–Riesz property can fail). ∎
