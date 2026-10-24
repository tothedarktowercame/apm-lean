| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| b90A02 | narrower | Restricts the arbitrary unital ring and right-module formulation to a commutative ring and ordinary `Module R M`. | — |
| b90A03 | faithful | Encodes the Sylow fixed-field existence and the intended uniqueness iff `L/K` is Galois; the printed “Galois over L” is an evident typo. | correction (`86b0edf56`) |
| b90A04 | faithful | Formalizes the conductor as ideals in both rings and all extension, contraction, primality, and uniqueness claims. | — |
| b93A01 | faithful | States every subgroup and sharp symmetric-group embedding/nonembedding conclusion with the requested orders. | — |
| b93A02 | faithful | States the CRT isomorphism and every requested Artinian-ring consequence. | — |
| b93A03 | faithful | Includes right exactness, integer endomorphisms, the tensor calculation/counterexample, and the complete cyclic-flat classification. | — |
| b93A04 | faithful | Encodes composita/intersections by lattice sup/inf and gives all four Galois-correspondence claims. | — |
| b93J01 | faithful | Supplies a counterexample and a valid corrected theorem for each of the five false assertions. | correction (`6df52d422`) |
| b93J02 | faithful | States both implications and supplies concrete domains witnessing every requested nonimplication. | correction (`c8dba2622`) |
| b93J03 | narrower | Adds `[Nontrivial V]`, excluding the zero vector space so that the demanded common eigenvector can satisfy `v ≠ 0`. | — |

### Evidence

#### b90A02

`apm_b90a02` quantifies `(R M : Type) [CommRing R] [AddCommGroup M] [Module R M]` and concludes free implies flat, projective implies flat, `Module.Flat ℤ ℚ`, and nonprojectivity of `ℚ` (lines 40–45). The latter four claims match the prelim, but `CommRing R` is a genuine restriction of “a ring with unity,” and the source explicitly defines flatness for right modules. The file itself acknowledges that Mathlib's available `Module.Flat` API prompted this restriction (lines 8–17). No local axiom, opaque declaration, or sorry-typed definition is used.

#### b90A03

`apm_b90a03` assumes a finite-dimensional Galois extension of degree `p^n*q^m` with distinct primes and `1<n,1<m` (lines 97–102). It concludes existence of a proper intermediate field with `Module.finrank (↥L) F = p^n` and, for every such `L`, singleton uniqueness iff `IsGalois K (↥L)` (lines 103–110). This matches the mathematically intended `L/K` reading; the prelim's “L is a Galois extension of L” is tautological and is explicitly identified as a typo in lines 8–10.

Commit `86b0edf56` parenthesized the uniqueness equivalence inside the `∀ L` implication. The first bank version grouped `↔ IsGalois K (↥L)` outside the intended implication structure, so this was a **correction** of a mis-parsed statement, not a narrowing.

#### b90A04

The conductor definitions are `{x : S | ∀ t : T, x.1*t ∈ S}` and its overring realization `{x : T | x ∈ S ∧ ∀ t, x*t ∈ S}` (lines 20–26). `apm_b90a04` realizes both as ideals, proves every overring ideal contained in `S` lies in the conductor, proves `xt∈P ↔ x²t∈P`, constructs the prime lifted ideal, identifies its contraction with `P`, and proves uniqueness (lines 36–53). These are exactly parts (a)–(f).

#### b93A01

`apm_b93a01_embeds G H := ∃ f : G →* H, Function.Injective f` (lines 19–20), so the encoding means an actual subgroup embedding. The main theorem gives a normal subgroup of order `q`, commutativity from a normal subgroup of order `p`, the sharp embeddings/nonembeddings into permutations of `q` and `q-1` points in the nonabelian case, and of `p+q` and `p+q-1` points in the abelian case (lines 171–183). This matches every prelim part.

#### b93A02

`apm_b93a02` gives `R/(I⊓J) ≃+* (R/I)×(R/J)` under `I⊔J=⊤` (lines 20–22), says every Artinian domain is a field and every prime ideal in an Artinian ring is maximal (lines 23–26), proves a finite infimum of distinct primes is coprime to another prime (lines 27–30), and proves the set of prime ideals finite (lines 31–32). Finset membership implements the prelim's finite list of distinct primes without loss.

#### b93A03

`apm_b93a03_flat` says tensoring with `M` preserves injectivity of every injective integer-linear map (lines 18–22), directly encoding the given definition. The main conjunction states tensor right-exactness, uniquely classifies every additive map `ℤ→ℤ`, gives `ℤ⊗ZMod 2 ≃ ZMod 2`, exhibits multiplication by two as injective before but not after tensoring, and classifies cyclic flat groups as infinite cyclic or subsingleton (lines 73–88). Thus it addresses all five parts, including the requested disproof.

#### b93A04

`apm_b93a04` characterizes membership in `L₁ ⊔ L₂` by finite sums of products (lines 21–27), proves the compositum Galois when both fields are (line 28), identifies fixing subgroups of sup and inf with subgroup inf and sup under `K/F` Galois (lines 29–31), and concludes the compositum is Galois with abelian automorphism group when it is all of `K` and both input Galois groups are abelian (lines 32–36). Sup/inf are the exact intermediate-field compositum/intersection encodings.

#### b93J01

`apm_b93j01` gives: the `A₄` counterexample and simplicity for `n≥5` (lines 1995–1998); the quaternion counterexample and all five order-eight isomorphism types (lines 1999–2009); the `A₄` order-six counterexample and Lagrange correction (lines 2010–2014); the `ℚ` counterexample and finite-abelian correction (lines 2015–2018); and the `S₃` counterexample plus the standard `p∤q-1` correction (lines 2019–2024). The custom direct-sum predicate requires cyclic summands, independence, and supremum `⊤` (lines 25–27).

The initial bank contained only isolated examples and no theorem expressing the five requested corrections. Commit `6df52d422` introduced the complete registered conjunction and also corrected the printed item (c), whose “subgroup of order n” is trivially witnessed by the whole group and was evidently intended to say order `m`. This is a **correction**.

#### b93J02

`apm_b93j02` states PID⇒UFD and UFD⇒integrally closed for all commutative domains (lines 202–207). It uses `ℤ[X]` for UFD⇏PID, a countably generated polynomial ring for UFD⇏Noetherian, and `ℤ[√-5]` for Noetherian⇏PID and for a non-UFD domain (lines 208–219). These are concrete examples with exactly the requested properties.

The initial bank had only a helper proving the composite PID⇒integrally-closed implication and omitted the separately requested implications and all counterexamples. Commit `c8dba2622` installed the complete target, so it is a **correction** of an incomplete/mismatched bank statement.

#### b93J03

`apm_b93j03` assumes an algebraically closed field, finite-dimensional module, and additionally `[Nontrivial V]` (lines 365–368). Under pairwise commutation it concludes a common eigenvector `v ≠ 0` and a basis in which every member has block-triangular matrix (lines 369–372). The conclusions faithfully encode the two requested parts, but `[Nontrivial V]` is an extra hypothesis not stated in the prelim and excludes the zero-dimensional case; without it the nonzero eigenvector conclusion is false. Hence the current theorem is narrower.

No graded current declaration depends on a local `axiom`, `opaque`, or `sorry`-typed definition. The lone `sorry` text found in b93J03 is only a comment describing its removal.
