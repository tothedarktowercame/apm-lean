| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| b96J04 | faithful | Gives both splitting-field Galois groups and the exact total/Galois degree-four subfield counts. | — |
| b97A01 | faithful | Exhausts and counts the five conjugacy classes, classifies normal subgroups, proves solvability and the order-24 action theorem, and supplies the requested example. | — |
| b97A02 | faithful | Encodes affine automorphisms over the finite constant field, their order, the exact fixed field, and finiteness over every proper constant-field extension. | — |
| b97A03 | faithful | States irreducibility, splitting over every chosen root field, the `S₃` automorphism group, and an exhaustive six-field list. | — |
| b97J01 | faithful | Gives standard derived/lower-central definitions, explicit `S₅` and `S₃` examples, and both finite p-group conclusions. | — |
| b97J03 | faithful | Counts exactly the roots in `ℚ(α)`, proves divisibility and the abelian case, and gives `r = 2` for `X⁶-2`. | — (the theorem statement is unchanged from its first commit) |
| b97J04 | faithful | Encodes the full additive Jordan–Chevalley decomposition, characteristic polynomial, eigenspace characterization and uniqueness, plus the multiplicative decomposition. | — |
| b98A01 | narrower | The last requested equivalence about a subgroup of order `3` is absent and is replaced by an equivalence about a subgroup of order `35`. | — |
| b98A02 | faithful | States existence/maximality, the characterization of subfields, Galois intersection, and compatibility of maximal abelian subextensions with intersection. | — |
| b98A04 | faithful | States the common-annihilator ideal, finite faithful tuple, regular-module embedding, and occurrence of every simple module as a composition factor. | — |

### Evidence

#### b96J04

The polynomial definitions are literal: `apm_b96J04_fQ : ℚ[X] := X ^ 8 + 1` and its `ZMod 41` counterpart (lines 26–28). The theorem identifies `(K ≃ₐ[ℚ] K)` with `Multiplicative (ZMod 2 × ZMod 4)`, counts all degree-four intermediate fields and the Galois ones as three, and identifies the finite-field automorphism group with `Multiplicative (ZMod 2)` (lines 489–502). These are `C₂ × C₄`, three/all three, and `C₂`, respectively.

#### b97A01

The theorem explicitly lists the five cycle types and class sizes `1,6,3,8,6` (lines 718–738), then states exactly
`N = ⊥ ∨ N = apm_b97A01_V4 ∨ N = alternatingGroup (Fin 4) ∨ N = ⊤`
and `IsSolvable apm_b97A01_S4` (lines 739–743). Lines 744–750 give the requested map with kernel cardinality two and a normal Sylow-2 subgroup. Lines 751–754 use literal `SL₂(F₃)` as an order-24, non-`S₄` example with nonnormal Sylow 3-subgroup.

#### b97A02

`apm_b97a02_affineAutomorphisms` is precisely the set of `F`-algebra automorphisms sending `X` to `aX+b`, with `a ≠ 0` (lines 20–25); being an `F`-algebra equivalence supplies fixation of constants. The invariant is `(X^q-X)^(q-1)` with `q = Fintype.card F` (lines 27–29). The theorem states uniqueness (lines 305–309), cardinality `q(q-1)` (310–311), the iff fixed-field characterization (312–315), and `Module.Finite K (RatFunc F)` for every `K ≠ ⊥` (316–317).

#### b97A03

The definitions are exactly `X^6+3`, `ℚ(α)`, and the derived sixth root of unity (lines 20–27). The theorem states irreducibility (line 1364), that every complex root belongs to `ℚ(α)` (1365–1369), an automorphism-group equivalence with `Perm (Fin 3)` (1370–1372), and exhausts every intermediate subfield by six displayed alternatives (1373–1382).

#### b97J01

Solvable and nilpotent mean termination of the derived and lower central series (lines 22–26). The theorem supplies the nonsolvable `S₅`, solvable nonnilpotent `S₃` (28–31), nontrivial center for `|G|=p^n>1` (32–34), and nilpotence for every finite p-group (35–37).

#### b97J03

The root count is `Set.ncard` of roots lying in `IntermediateField.adjoin ℚ {α}` (lines 20–24), and the special polynomial is `X^6-C 2` (26–28). Lines 696–704 state `r ∣ natDegree`, `r = natDegree` for every abelian splitting-field Galois group, and exactly `r=2` in the special case. Comparing the first statement commit `cff537b77` with the current theorem shows the same type; later commit `4f8650bdc` only replaced proof placeholders.

#### b97J04

`APMAdditiveJC` contains semisimplicity, nilpotence, commutation, and `T=S+N` (lines 21–23); the eigenspace/generalized eigenspace and unipotence definitions are literal (26–40). Lines 288–303 state existence, characteristic-polynomial equality, both eigenspace inclusions, uniqueness, and unique commuting semisimple/unipotent factorization for each invertible `T'`. The source's obvious `N`/`U` typo in part (d) is reasonably encoded as `U`.

#### b98A01

Part (a) is accurately encoded at lines 423–428, and the first three requested assertions of part (b) appear at lines 429–440. But problem.md asks
“`G` contains a subgroup of order `3` iff `G` contains a normal subgroup of order `7`,”
whereas lines 441–442 say
`((∃ M : Subgroup G, Nat.card M = 35) ↔ ∃ N : Subgroup G, N.Normal ∧ Nat.card N = 7)`.
Thus the registered theorem omits the stated order-3 equivalence and proves a different order-35 equivalence.

#### b98A02

`apm_b98A02_IsMaximalAbelian` requires `A ≤ E`, Galoisness, commutative automorphism group, and containment of every other abelian Galois subextension (lines 22–30). The theorem gives its existence (200–205), the iff characterization for `K ≤ E` (206–211), Galoisness of `E ⊓ L` (212–215), and `A(E∩L)=A(E)∩A(L)` (216–224).

#### b98A04

The ambient hypotheses are exactly a faithful module over a left-Artinian ring (lines 815–817). Lines 818–823 give the common-annihilator ideal, a finite tuple with zero common annihilator, and an injective linear map `R → Fin s → M`. Lines 824–835 encode a finite strict composition series with simple factors and assert that every simple `V` is linearly equivalent to one factor.

No audited file contains an `axiom`, `opaque`, or `sorry` declaration on which its registered theorem depends.
