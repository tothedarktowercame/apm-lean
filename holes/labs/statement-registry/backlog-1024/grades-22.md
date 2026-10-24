| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| a99J09 | faithful | The restricted-measure `MemLp` hypothesis represents $f\in L^p([0,\infty))$, and the conclusion is holomorphicity of its Laplace transform on the open right half-plane. | — |
| aunk01 | narrower | The integral-invariance clause quantifies only real-valued `f : ℝ → ℝ`; the usual unqualified $L^1(\mathbb R)$ in this context includes complex-valued functions. | — |
| aunk02 | faithful | It explicitly represents a region as open and connected, a contained disk on which the imaginary part vanishes, and reality throughout the region. | — |
| aunk03 | faithful | It states the requested evaluation \(\sum_{k\ge1}k^{-4}=\pi^4/90\); the prescribed kernel and square contour are proof-method data rather than additional mathematical conclusions. | — |
| aunk04 | faithful | It gives zero roots in the open unit disk and proves that every entire function with the stated real-power growth is a polynomial whose coefficients above order $m$ vanish. | — |
| aunk05 | faithful | Local uniform convergence on the region yields holomorphicity of the limit and local uniform convergence of the derivatives. | — |
| b00J01 | faithful | It identifies the three Galois groups and exhaustively classifies the rational intermediate fields by degrees and Galois status. | — |
| b00J03 | faithful | For every finite nonabelian group of order $p^3$, it proves that the center has order $p$ and equals the commutator subgroup. | — |
| b00J04 | faithful | For every intermediate algebra in a fraction field, it states the special fraction form, the PID conclusion, and equality with the base ring under module-finiteness. | — |
| b01A01 | faithful | It states the split-or-irreducible dichotomy for $X^p-a$ and separability of every irreducible polynomial under surjective Frobenius. | — |

### Evidence notes

**a99J09.** The registered declaration is lowercase `apm_a99j09`, not `apm_a99J09`. The transform and domain are `apm_a99j09_laplace` and `apm_a99j09_rightHalfPlane` (lines 20–24). The theorem assumes `hp : 1 < p` and `MemLp f (ENNReal.ofReal p) (volume.restrict (Ici 0))`, and concludes `DifferentiableOn ℂ ...` on that half-plane (lines 112–114). A real exponent is automatically finite, so this captures the requested $1<p<\infty$. No axiom, opaque, or sorry occurs.

**aunk01.** Translation is exactly `(fun x : ℝ ↦ x + y) '' A` (lines 20–21). Lines 23–28 prove Borel measurability and measure invariance, then integral invariance, but the last quantifier is specifically `(f : ℝ → ℝ)`. The problem leaves the scalar field of its $L^1$ function unqualified; in the surrounding analysis convention this includes complex-valued integrable functions, which this theorem does not quantify over. There are no placeholders.

**aunk02.** Lines 17–21 assume `IsOpen Ω`, `IsConnected Ω`, holomorphicity via `DifferentiableOn ℂ`, and a positive-radius ball contained in `Ω` on which `(f z).im = 0`; lines 21–22 conclude the same equality for every `z ∈ Ω`. This is the stated identity-theorem consequence, with “region” made explicit. No placeholders occur.

**aunk03.** Lines 9–14 define exactly the prescribed cotangent kernel and square boundary. The theorem itself (lines 16–17) states `(∑' k : ℕ, 1 / (k+1)^4) = π^4/90`, which is precisely the series beginning at one. The definitions are unused by the theorem proof, but the problem’s “use” clause prescribes a method rather than strengthening the proposition being proved. No placeholders occur.

**aunk04.** The polynomial is `X^4 - C 3 * X^3 + X^2 + C 6` (lines 24–26). The final theorem counts its roots of norm `< 1` with multiplicity and obtains zero (lines 188–189). Lines 190–196 quantify positive `A,B,m`, an entire `f`, the exact growth bound using `Real.rpow`, and produce a polynomial equal to `f` whose coefficient `k` is zero whenever `m < k`; this supplies the requested degree conclusion. No placeholders occur.

**aunk05.** Lines 19–27 quantify an open connected `Ω`, holomorphic `fseq n`, and `TendstoLocallyUniformlyOn fseq f atTop Ω`, then conclude both `DifferentiableOn ℂ f Ω` and locally uniform convergence from `deriv (fseq n)` to `deriv f`. This faithfully expresses both requested clauses. No placeholders occur.

**b00J01.** The registered declaration is lowercase `apm_b00j01`. Its polynomial is `X ^ 3 - C 7` (line 21). Over `ℚ`, lines 763–774 give automorphism group `S₃`, one degree-two field, three distinct degree-three fields, an exhaustive intermediate-field list, and exactly the requested Galois/non-Galois statuses. Lines 775–780 identify the real group with `ZMod 2` and the finite-field group with `ZMod 3`. No placeholders occur.

**b00J03.** The registered declaration is lowercase `apm_b00j03`. Lines 52–58 quantify prime `p`, a finite group of cardinality `p^3`, and an explicit noncommutativity witness, concluding `Nat.card (Subgroup.center G) = p` and `Subgroup.center G = commutator G`. This is a direct encoding of the problem. No placeholders occur.

**b00J04.** The registered declaration is lowercase `apm_b00j04`. Lines 178–187 quantify a PID domain `R`, its fraction field realization `F`, and an intermediate `Subalgebra R F`; they state the required `a/b` representation with inverse denominator in `S`, `IsPrincipalIdealRing S`, and `Module.Finite R S → S = ⊥`. Here `⊥` is the image of the base algebra, so it is exactly `S=R`. The only occurrence of the token `sorry` is historical prose in a comment (line 195), not a declaration or proof placeholder.

**b01A01.** The registered declaration is lowercase `apm_b01a01`, and its helper `apmFrobeniusPolynomial` is `X ^ p - C a` (lines 21–22). Lines 24–31 assume a field of prime characteristic `p`, assert that each such polynomial splits or is irreducible, and assert that surjectivity of `α ↦ α^p` makes every irreducible `q` separable. No placeholders occur.
