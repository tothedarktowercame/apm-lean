| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| b01A03 | faithful | States the equivalence of complementedness, freeness of `M/S`, and saturation for a finite free module over a PID. | — |
| b01A04 | faithful | Existentially realizes both requested groups as Galois groups over `ℚ`. | — |
| b01J01 | faithful | States all four requested divisibility, index, Sylow-trace, and Sylow-count claims. | — |
| b01J03 | faithful | States all four requested consequences, including equality of root stabilizers/fields, `F[α]=K`, and `P=G`. | — |
| b01J04 | narrower | Part (a) adds the necessary assumptions that `A` and `B` are individually diagonalizable; the printed unrestricted biconditional is false. | — |
| b03J01 | faithful | States normality of the index-`p` subgroup and cyclicity in the twin-prime order case under the source's global setup. | — |
| b03J02 | faithful | States nonprincipality of `(a,x)` and that the two-variable polynomial ring over a field is not a PID. | — |
| b03J03 | faithful | Proves UFDs integrally closed in their fraction fields and disproves part (b) with the squarefree example `D=ℤ`, `a=5`. | — |
| b03J04 | faithful | Produces the roots-of-unity splitting subfield, proves it and `α` generate `K`, and states the irreducible-or-root dichotomy. | — |
| b90A01 | faithful | States faithful embeddings into `S_k` and `A_k`, the alternating-group index bound, and nonsimplicity at order `120`. | — |

### Evidence

**b01A03.** `apm_b01a03` assumes a commutative domain with `IsPrincipalIdealRing` and a finite free module (lines 31–35), and concludes `(apmComplemented S ↔ Module.Free R (M ⧸ S)) ∧ (Module.Free R (M ⧸ S) ↔ apmSaturated S)` (lines 36–37). The used definitions say `apmComplemented S := ∃ T, IsCompl S T` (lines 18–21) and spell out exactly the source's divisibility closure in `apmSaturated` (lines 23–29). No axiom, opaque declaration, or sorry occurs.

**b01A04.** `apm_b01a04` concludes realizability for `Multiplicative (ZMod 3)` and `Multiplicative (ZMod 3 × ZMod 3)` (lines 325–328). The used definition `apm_b01A04_isGaloisGroup G` existentially supplies a field `K`, an `Algebra ℚ K`, `IsGalois ℚ K`, and a group equivalence `(K ≃ₐ[ℚ] K) ≃* G` (lines 22–28), exactly expressing the requested examples. No axiom, opaque declaration, or sorry occurs.

**b01J01.** `apm_b01j01` assumes finite `G`, `H K : Subgroup G`, normal `K`, and prime `p` (lines 296–299). Lines 300–306 respectively state the quotient divisibility, existence of an index-`p` subgroup, equality of Sylow subgroups of `K` (embedded in `G`) with intersections `P ⊓ K`, and divisibility of the two Sylow counts. The used set definitions are explicit at lines 25–32. No axiom, opaque declaration, or sorry occurs.

**b01J03.** `apm_b01j03` contains the splitting-field, prime degree, irreducibility, separability, monicity, Sylow, self-normalizer, and root hypotheses at lines 194–205. Its conclusion gives `|G|=p*s`, `p∤s`, exactly `s*(p-1)` order-`p` elements, equal root stabilizers, equal root fields, root field `⊤`, and `P=⊤` (lines 206–215). `apm_b01J03_rootField` is `IntermediateField.adjoin F {α}` and `rootStabilizer` its fixing subgroup (lines 22–29). No axiom, opaque declaration, or sorry occurs.

**b01J04.** `apm_b01j04` assumes `apmMatrixDiagonalizable A → apmMatrixDiagonalizable B →` before the simultaneous-diagonalization/commutation equivalence (lines 223–228); this is a genuine restriction absent from the source. It is necessary because, as the file notes, a non-diagonalizable matrix commutes with itself, refuting the printed converse. `apmMatrixDiagonalizable` transparently means conjugate by a unit to a diagonal matrix (lines 20–22). Part (b), lines 229–232, faithfully states that every invertible matrix has polynomial inverse. The restricted statement was already present in the first statement-bank commit, so there is no later repair classification. No axiom, opaque declaration, or sorry occurs.

**b03J01.** `apm_b03j01` assumes the explicit smallest-prime-divisor predicate and `H.index = p` (lines 128–132), then concludes `H.Normal` and, if `p+2` is prime and `|G|=p(p+2)`, `IsCyclic G` (lines 133–134). `apmB03SmallestPrimeDivisor` exactly expands to primality, divisibility, and minimality among prime divisors (lines 16–17). No axiom, opaque declaration, or sorry occurs.

**b03J02.** `apm_b03j02` states for every domain and nonzero nonunit `a` that `apmTwoGeneratorIdeal a` is not principal, and for every field `K` that `MvPolynomial (Fin 2) K` is not a principal ideal ring (lines 58–62). The ideal is transparently `Ideal.span {C a, X}` (lines 16–17). No axiom, opaque declaration, or sorry occurs.

**b03J03.** `apm_b03j03` universally states `IsIntegrallyClosedIn D K` for a UFD and its fraction field (lines 128–132). Part (b) gives `Squarefree (5 : ℤ) ∧ ¬IsIntegrallyClosed (ℤ[X] ⧸ apmQuadraticIdeal)` (lines 133–134), a valid disproof of the universal assertion requested by “prove or disprove”; `apmQuadraticIdeal` is exactly `(X²-5)` (lines 18–19). No axiom, opaque declaration, or sorry occurs.

**b03J04.** `apm_b03j04` assumes prime `p`, nonzero `β`, a splitting field for `X^p-C β`, and a root `α` (lines 29–35). It produces an intermediate field that is a splitting field of `X^p-1` and whose union with `{α}` generates `⊤` (lines 36–39), followed by irreducibility or a base-field root (lines 40–41). The two polynomials are transparent definitions at lines 21–27. No axiom, opaque declaration, or sorry occurs.

**b90A01.** `apm_b90a01` assumes finite simple `G`, prime `p`, exactly `k>1` Sylow subgroups (lines 652–655), then gives injective homomorphisms into `Equiv.Perm (Fin k)` and `alternatingGroup (Fin k)` (lines 656–657). It also universally states the index bound for a proper simple subgroup of `A_n`, `n≥5` (lines 658–660), and nonsimplicity for every finite group of cardinality `120` (lines 661–662). No axiom, opaque declaration, or sorry occurs.
