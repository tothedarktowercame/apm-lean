| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| b94A02 | faithful | Encodes the balanced coefficient map with its formula and surjectivity, the tensor equivalence, and failure of injectivity after tensoring when `b ∈ I`. | — |
| b94J01 | faithful | States the invariant-factor classification, the coprimality criterion for a product of two cyclic groups, and cyclicity of finite subgroups of a field's units. | — |
| b94J02 | faithful | States all three trace claims over an arbitrary field, with rank correctly cast into the field. | — |
| b94J03 | faithful | Identifies the splitting-field degrees/models and Galois groups over `ℚ`, `ℝ`, and `ZMod 7`. | — |
| b94J04 | faithful | Defines `S⁻¹M` as `LocalizedModule S M`, proves preservation of short exactness, and supplies an explicit converse counterexample. | — |
| b95J01 | faithful | Gives the least positive exponent, divisibility for every integral exponent, the normal-index result, and an explicit nonnormal counterexample. | — |
| b95J02 | faithful | Correctly formalizes both the finite-abelian exponent criterion and the cyclic-vector/minimal-polynomial criterion. | — |
| b95J03 | faithful | Gives the unique tensor map, the requested image/kernel dimensions, and the correct two-element basis over `ℂ/ℝ`. | — |
| b95J04 | faithful | Formalizes every forward and converse Kummer-theory conclusion, including the specified automorphism action. | — |
| b96A03 | faithful | Correctly formalizes purity, automorphism preservation of primes, orbit products, divisibility, and primality in the fixed ring. | — |

### b94A02

Lines 152–170 of `apm_b94a02` assume `I ≠ ⊤` and `∀ c, b*c=0 → c∈I`, then assert a surjective curried linear map with the defining formula
`φ x (Ideal.Quotient.mk I s) = Ideal.Quotient.mk I (r * s)`, a linear equivalence
`TensorProduct R (Ideal.span {b}) (R ⧸ I) ≃ₗ[R] (R ⧸ I)`, and, under `b ∈ I`, noninjectivity of the tensor-induced inclusion. The custom definition at lines 36–47 constructs exactly the quotient-valued coefficient map. This covers all three source parts. The theorem statement is unchanged from bank commit `8b6af9d59`.

### b94J01

The definition at lines 21–25 says that `d` consists of factors at least two, ordered by divisibility, with
`G ≃* ∀ i, Multiplicative (ZMod (d.get i))`. Lines 689–697 of `apm_b94j01` assert unique such invariant factors for every finite commutative group, cyclicity of the two-factor product iff `Nat.Coprime m n`, and `IsCyclic G` for every finite subgroup `G ≤ Kˣ`. These are precisely the three requested results. The statement is unchanged from bank commit `76fcbf619`.

### b94J02

Lines 17–25 of `apm_b94j02` state: positive nilpotence exponent implies `Matrix.trace A = 0`; vanishing of `trace (B*C)` for every `B` implies `C = 0`; and `D^2=D` implies `trace D = (D.rank : K)`. The cast is the correct arbitrary-characteristic interpretation of the printed equality. Quantifying the nilpotence implication over `m` is equivalent to the source's “if some positive `m` exists.” The statement is unchanged from bank commit `564154b7f`.

### b94J03

The polynomial is literally `X ^ 3 - C 3` (lines 21–22). Lines 211–226 of `apm_b94j03` describe every abstract splitting field: over `ℚ`, degree six and automorphism group `S₃`; over `ℝ`, an `ℝ`-algebra equivalence with `ℂ` and group `Z/2`; over `ZMod 7`, degree three, cardinality `343`, and group `Z/3`. This is a faithful description of each requested splitting field and Galois group. The statement is unchanged from bank commit `aef93cfb9`.

### b94J04

Lines 13–17 define short exactness as injectivity, exactness, and surjectivity. Lines 21–23 define the requested `S⁻¹M` to be Mathlib's quotient construction `LocalizedModule S M`. Lines 27–41 of `apm_b94j04` prove localized maps preserve `IsShortExact` and exhibit the nonexact zero-map sequence `ZMod 1 → ZMod 2 → ZMod 1`, which becomes exact after localization at powers of two. The first theorem conjunct merely records inhabitation, but the source's definitional part is carried by the preceding exact type definition, so it is not a vacuous substitute. The statement is unchanged from bank commit `7fd529cd7`.

### b95J01

Lines 22–33 of `apm_b95j01` produce, for each `g`, a positive `k` with `g^k∈H`, minimality among positive natural exponents, divisibility of every integer exponent landing in `H`, and `k ∣ H.index` when `H` is normal. The second conjunct uses the index-three transposition subgroup of `S₃`, an element outside it whose square lies in it, and `¬ 2 ∣ 3`; hence its least exponent is two and the nonnormal analogue fails. The theorem statement remained unchanged from bank commit `967101913` through the later review-flag commit.

### b95J02

Lines 14–20 define `groupExponent` as the least positive universal exponent and `ActsCyclically` by spanning with the orbit of one vector. Lines 197–208 of `apm_b95j02` explicitly establish positivity/universality/minimality of the exponent and
`IsCyclic G ↔ Nat.card G = groupExponent G`; the second conjunct is
`ActsCyclically T ↔ finrank V = natDegree (minpoly F T)`. This exactly expresses both source theorems. The statement is unchanged from bank commit `9cb48702a`.

### b95J03

Lines 15–23 define multiplication on the tensor square and its composition with the faithful multiplication representation. Lines 57–75 of `apm_b95j03` characterize this map uniquely by
`φ (a ⊗ₜ b) c = a*b*c`, give image dimension `[E:F]` and kernel dimension `[E:F]^2-[E:F]`, and exhibit the basis
`1⊗1 + i⊗i`, `1⊗i - i⊗1` for `ℂ/ℝ`. These are exactly the four requested parts. The statement is unchanged from bank commit `44e5f08fc`.

### b95J04

Lines 185–219 of `apm_b95j04` assume prime `p`, a nontrivial `p`-th root of unity `z`, and state `ringChar F ≠ p`, the complete factorization indexed by exponents `1,…,p`, the Galois/cyclic description of every radical extension `F⟮α⟯`, and the pointwise automorphism formula. Its last conjunct assumes a finite-dimensional Galois extension with cyclic automorphism group of cardinality `p` and produces the requested nonzero `z`-eigenvector with `α∉F`, `α^p∈F`, and `F⟮α⟯=E`. This matches every source part. The statement is unchanged from bank commit `9ddc3b705`.

### b96A03

Lines 19–20 define `F`-purity by triviality of every character from every subgroup to `Fˣ`. Lines 22–35 define the product of distinct orbit elements (using `Finset.image`) and the actual fixed subring. Lines 189–205 of `apm_b96a03` prove odd finite groups are `ℚ`-pure, automorphisms preserve primality, purity gives equality-or-nonassociation, the orbit product is invariant and divides invariant multiples, and that product is prime as an element of the fixed subring. These exactly cover the five source parts. The statement is unchanged from bank commit `4db06c490`.

No current file contains an `axiom`, `opaque`, or proof-valued `sorry`; the sole `sorry` match is historical prose in a comment in `b94J03`.
