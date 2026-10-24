| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| b96A04 | narrower | Part (a) adds the hypothesis `y ≠ 0`, absent from the prelim (but necessary, since the printed claim is false for `y = 0`); the remaining clauses are faithful. | — |
| b96J01 | faithful | Exactly states that a subgroup of `S₅` containing a 5-cycle and a transposition is all of `S₅`. | neutral: the review-flag commit merely renamed/repackaged the same theorem with fully qualified predicates. |
| b96J03 | faithful | Uses the standard group-theoretic definitions, proves nilpotent implies solvable, supplies a solvable nonnilpotent counterexample, and classifies the presented group as neither. | — |
| b97A04 | faithful | States finite dimensionality of `V` and its endomorphism division algebra, identifies the latter with `ℂ`, identifies `R` with the full matrix/end ring, and decomposes every module into copies of `V`. | — |
| b97J02 | faithful | Encodes all five claims: prime quotients are fields, the idempotent-generator criterion, products of fields, the natural injective map, and finite-spectrum bijectivity. | — |
| b98A03 | faithful | States the conductor’s maximality, uniqueness above primes away from it, the constant-term criterion, equality after adjoining a common element, and the final conductor/intersection result. | neutral: the repair replaces `¬ I ≤ map(P)` by the equivalent explicit witness `∃ r, map(r) ∈ I ∧ r ∉ P`, using the theorem’s conductor characterization. |
| b98J02 | faithful | States finite prime avoidance, the Galois norm’s membership in `P ∩ A`, and transitivity on primes lying over a fixed prime. | — |
| b98J03 | faithful | States cyclicity over a finite base, both primitive-element implications, generation by minimal-polynomial coefficients, and finiteness of intermediate fields. | — |
| b99A01 | faithful | States the half-plane maximum principle and every requested valuation-domain property, including localization of an overring at its maximal ideal. | — |
| b99A03 | faithful | States the coset/conjugate equivalence, stability of a transversal under left multiplication, and equality of the conjugate product with the mapped minimal polynomial. | — |

### Evidence

#### b96A04

Lines 101–124 encode all five parts. The first clause is
```lean
(∀ y d : R, y ≠ 0 → d * y ∣ y → IsUnit d)
```
whereas the prelim does not say `y ≠ 0`. This is a real added hypothesis: at `y = 0`, `d*0 ∣ 0` for every nonunit `d`, so the printed claim is false. The remaining clauses give torsion-freeness of a free module, the unsolvable `(dx)y=m` equation, free/projective embedding consequences for the fraction field, rigidity of projective quotients, common denominators for finitely generated intermediate modules, and the finite-generation consequence `R=K`. No axiom, opaque, or sorry-typed dependency was found.

#### b96J01

Lines 19–24 state
```lean
{G : Subgroup (Equiv.Perm (Fin 5))}
(hσ : ∃ σ ∈ G, Equiv.Perm.IsCycle σ ∧ orderOf σ = 5)
(hτ : ∃ τ ∈ G, Equiv.Perm.IsSwap τ) :
G = ⊤
```
which is exactly the prelim. The review-flag commit changes the declaration name from `subgroup_eq_top_of_fiveCycle_and_swap` to `apm_b96j01` and qualifies `IsCycle`/`IsSwap`; the proposition is unchanged, so the repair is neutral. No axiom/opaque/sorry dependency was found.

#### b96J03

Lines 22–26 define
```lean
apm_b96j03_IsNilpotent G := Group.IsNilpotent G
apm_b96j03_IsSolvable G := IsSolvable G
```
and lines 231–239 state nilpotent implies solvable, existence of a solvable nonnilpotent group, and that the group presented by the exact five source relations is neither solvable nor nilpotent. Definitions are supplied by the named declarations even though the main theorem naturally states their consequences. The file correctly rejects the imported solution fragment’s ring-theoretic `rⁿ=0` as irrelevant to groups. No axiom/opaque/sorry dependency was found.

#### b97A04

Lines 125–142 state
```lean
Module.Finite ℂ V
(∀ φ : Module.End R V, φ ≠ 0 → IsUnit φ)
Module.Finite ℂ (Module.End R V)
(∀ φ, ∃ c : ℂ, φ = c • LinearMap.id)
Nonempty (R ≃ₐ[ℂ] Module.End ℂ V)
∀ W, ∃ ι, Nonempty (W ≃ₗ[R] (ι →₀ V))
```
under exactly the finite-dimensional algebra, simple-module, and faithfulness assumptions. The last two clauses give the requested structure of `R` and arbitrary `R`-modules. No axiom/opaque/sorry dependency was found.

#### b97J02

Lines 18–27 faithfully define the spectrum, zero-dimensionality, and reducedness. Lines 147–169 then state all source conclusions, including the natural map formula
```lean
φ a P = Ideal.Quotient.mk P.1 a
```
its injectivity, and `Finite (APMSpectrum R) → Function.Bijective φ`. The direct product clause permits an arbitrary index type. No axiom/opaque/sorry dependency was found.

#### b98A03

Lines 222–251 state each requested conductor and prime-contraction clause. In particular, part (b) is
```lean
(∃ r : R, algebraMap R T r ∈ I ∧ r ∉ P) → Q₁ = Q₂
```
and the final clause quantifies every intermediate `Subalgebra R T` whose two contractions agree, forcing it to be bottom (the copy of `R`), then concludes the mapped `P`, `Q₁ ⊓ Q₂`, and `I` agree. The bank condition `¬I ≤ Ideal.map ... P` is equivalent to the explicit witness once the preceding elementwise conductor characterization and injective algebra map are used; the change is neutral. No axiom/opaque/sorry dependency was found.

#### b98J02

Lines 19–50 state finite prime avoidance; for `x ∈ P`, existence of `y ∈ P` in the image of `A` whose image in `M` is the full Galois product; and, for any two primes over `q`, existence of a Galois automorphism transporting one prime to the other. The assumptions `IsIntegralClosure B A M` and `hinter` encode the source’s integral-closure and `B ∩ L = A` assumptions, rather than supplying any requested conclusion. No axiom/opaque/sorry dependency was found.

#### b98J03

Lines 15–32 state:
```lean
Finite k → IsCyclic (K ≃ₐ[k] K) ∧ ∃ x, adjoin k {x} = ⊤
Infinite k → Set.Finite univ → ∃ x, adjoin k {x} = ⊤
...
adjoin k (range fun n => algebraMap E K ((minpoly E x).coeff n)) = E
...
primitive → Set.Finite univ
```
These are precisely parts (a)–(d), with `IsCyclic` answering the no-proof classification question. No axiom/opaque/sorry dependency was found.

#### b99A01

Lines 23–55 include both the opening half-plane problem and all valuation-domain parts. The first conjunct assumes boundedness and continuity on the closed upper half-plane, analyticity on the open half-plane, and the boundary norm bound, and concludes the same norm bound in the interior. The second conjunct gives total ordering and a unique maximal ideal, principality of finitely generated ideals, the displayed integrality criterion, inheritance by intermediate subrings, and the localization formula. No axiom/opaque/sorry dependency was found.

#### b99A03

Lines 21–31 define genuine left cosets, complete left transversals, and the conjugate product. Lines 34–54 state the coset equality iff `σ α = τ α`, that `s.image (τ * ·)` remains a transversal, and
```lean
apmConjugateProduct F E α s =
  (minpoly F α).map (algebraMap F E)
```
The last equality simultaneously says the product descends to `F[X]` and is the minimal polynomial, so it covers parts (c) and (d). No axiom/opaque/sorry dependency was found.
