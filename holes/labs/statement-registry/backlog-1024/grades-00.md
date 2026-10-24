| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| a98J03 | narrower | The intended Poisson-kernel result is encoded, including a stronger contraction bound, but only for real-valued `L²`; the prelim does not specify this scalar restriction. | — |
| a99J08 | faithful | The upper half-disk interpretation and the global square-root estimate faithfully express boundedness of the quotient while making the value at `0` meaningful. | — |
| a99J10 | faithful | It states holomorphy, the `|Im z|⁻¹ᐟ²` bound away from the singular real diameter, radial convergence from below, and identically-zero conclusion. | — |
| b00J02 | faithful | It directly states the requested order of `GL₃(ℤ/4ℤ)` as `86016`. | — |
| b01A02 | faithful | Both the smallest-prime-index normality theorem and every requested order-255 conclusion are stated. | — |
| b01J02 | faithful | It classifies all maximal ideals, gives the requested explicit nonprime witness, and supplies a nonzero prime nonmaximal ideal. | — |
| b93J04 | faithful | It gives the radical basis, Klein-four Galois group with explicit generator actions, and the complete five-element subfield list. | — |
| b94A01 | faithful | It enumerates `Aut(P)`, the two actions of `Q`, the semidirect decomposition, and both requested nonabelian products. | — |
| b96A02 | faithful | All four requested group/Galois assertions are stated with the actual group orders, normal core, splitting-field conditions, and degrees. | — |
| b96J02 | faithful | It lists exactly the three Jordan types, proves their cardinality and pairwise nonisomorphism, and classifies every 16-element module. | neutral (the only post-bank theorem-text change is indentation) |

### Evidence notes

#### a98J03

The prelim defines an operator on unspecified-scalar `L²(ℝ)` and asks for membership, bounded linearity, and convergence. The source denominator appears to contain a typographical error, `1 / ((x-t)+y²)`. The formal definition uses the standard Poisson kernel:

```lean
573 noncomputable def apmPoissonKernel (y x : ℝ) : ℝ :=
574   (y / Real.pi) / (x ^ 2 + y ^ 2)
576 noncomputable def apmPoissonIntegral (y : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
577   ∫ t, apmPoissonKernel y (x - t) * f t ∂volume
```

The registered theorem supplies a contraction family and convergence:

```lean
839 theorem apm_a98j03 :
840     ∃ T : ℝ → (Lp ℝ 2 volume →L[ℝ] Lp ℝ 2 volume),
841       (∀ y : ℝ, 0 < y → ‖T y‖ ≤ 1) ∧
842       (∀ (f : ℝ → ℝ) (hf : MemLp f 2 volume) (y : ℝ), 0 < y →
843         ∃ hgy : MemLp (apmPoissonIntegral y f) 2 volume,
844           T y (hf.toLp f) = hgy.toLp (apmPoissonIntegral y f)) ∧
845       (∀ F : Lp ℝ 2 volume,
846         Tendsto (fun y ↦ T y F) (nhdsWithin 0 (Ioi 0)) (nhds F))
```

The substantive restriction is `Lp ℝ` and `f : ℝ → ℝ`, rather than a scalar-polymorphic or complex-valued `L²(ℝ)` statement. The norm bound is a legitimate strengthening, not a fidelity defect. No theorem-dependent axiom, opaque constant, or sorry-typed definition was found.

#### a99J08

The domain is explicitly the open upper half-disk:

```lean
26 def apm_a99J08_upperHalfDisk : Set ℂ :=
27   Metric.ball 0 1 ∩ {z | 0 < z.im}
```

The theorem assumes continuity on its closure, holomorphy inside, and the two diameter boundary conditions, then states the equivalent meaningful-at-zero estimate:

```lean
711 theorem apm_a99j08
712     (g : ℂ → ℂ)
713     (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
714     (hgholo : DifferentiableOn ℂ g apm_a99J08_upperHalfDisk)
715     (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
716     (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0) :
717     ∃ C : ℝ, 0 ≤ C ∧
718       ∀ z ∈ closure apm_a99J08_upperHalfDisk,
719         ‖g z‖ ≤ C * Real.sqrt ‖z‖
```

This is equivalent to boundedness of `‖g z‖ / sqrt ‖z‖` off `0`, and correctly includes the forced corner value at `0`. No theorem-dependent axiom, opaque constant, or sorry-typed definition was found.

#### a99J10

The theorem states:

```lean
164 theorem apm_a99j10 (f : ℂ → ℂ)
165     (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
166     (hbound : ∀ z ∈ ball (0 : ℂ) 1, z.im ≠ 0 →
167       ‖f z‖ ≤ Real.rpow |z.im| (-(1 : ℝ) / 2))
168     (hradial : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
169       Tendsto
170         (fun r : ℝ => f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
171         (𝓝[<] (1 : ℝ)) (𝓝 0)) :
172     ∀ z ∈ ball (0 : ℂ) 1, f z = 0
```

The `z.im ≠ 0` guard is the correct Lean encoding of a bound whose right-hand side is infinite/undefined on the real diameter; omitting it would make Lean's `Real.rpow 0` convention impose an unintended zero bound. No smoothness-order issue or theorem-dependent axiom/opaque/sorry definition occurs.

#### b00J02

The statement is exactly the numerical question:

```lean
113 theorem apm_b00j02 :
114     Fintype.card (GL (Fin 3) (ZMod 4)) = 86016
```

`GL (Fin 3) (ZMod 4)` is the literal general linear group requested. Although history contains commits named “statement repair,” comparison with the first statement-bank commit shows no change to the registered theorem statement, so no repair classification applies. No theorem-dependent axiom, opaque constant, or sorry-typed definition was found.

#### b01A02

The auxiliary predicate says precisely “smallest prime divisor”:

```lean
31 def apmSmallestPrimeDivisor (p n : ℕ) : Prop :=
32   p.Prime ∧ p ∣ n ∧ ∀ q : ℕ, q.Prime → q ∣ n → p ≤ q
```

The theorem then states both requested parts:

```lean
258 theorem apm_b01a02 :
259     (∀ (G : Type*) [Group G] [Fintype G]
260       (p : ℕ) (H : Subgroup G),
261       apmSmallestPrimeDivisor p (Fintype.card G) →
262       H.index = p → H.Normal) ∧
263     (∀ (G : Type*) [Group G] [Fintype G],
264       Fintype.card G = 255 →
265         (∃ P : Subgroup G, P.Normal ∧ Nat.card P = 17) ∧
266         (∃ H : Subgroup G,
267           H.Normal ∧ Nat.card H = 85 ∧ IsCyclic H) ∧
268         IsCyclic G)
```

No hypothesis supplies any requested conclusion. No theorem-dependent axiom, opaque constant, or sorry-typed definition was found.

#### b01J02

The three named ideals are literal encodings of the prelim objects:

```lean
41 def apm_b01J02_twoGeneratedIdeal (p : ℕ) (f : ℤ[X]) : Ideal ℤ[X] :=
42   Ideal.span {C (p : ℤ), f}
45 def apm_b01J02_nonprimeIdeal : Ideal ℤ[X] :=
46   Ideal.span {C 3, X ^ 2 + X + 1}
49 def apm_b01J02_xIdeal : Ideal ℤ[X] :=
50   Ideal.span {X}
```

The theorem classifies every maximal ideal as `(p,f)` with `p` prime and `f mod p` irreducible (lines 242–246), uses `f=g=X-1` as the requested product witness (lines 247–251), and proves `(X)` nonzero, prime, and nonmaximal (lines 252–254). These cover all three parts directly. No theorem-dependent axiom, opaque constant, or sorry-typed definition was found.

#### b93J04

The polynomial is literal:

```lean
20 noncomputable def apm_b93j04_poly : Polynomial ℚ :=
21   X ^ 4 - C 10 * X ^ 2 + C 1
```

The theorem quantifies over its actual splitting field and gives `r₂²=2`, `r₃²=3`, generation and basis `1,r₂,r₃,r₂r₃` (lines 1104–1111), the abstract Klein-four equivalence and explicit sign-changing automorphisms (lines 1112–1115), and exactly the bottom, three quadratic, and top intermediate fields (lines 1116–1121). This is the requested complete description. No theorem-dependent axiom, opaque constant, or sorry-typed definition was found.

#### b94A01

The generator assumptions are the prelim assumptions:

```lean
108     ∀ (G : Type*) [Group G] [Fintype G]
109         (P : Sylow 5 G) (Q : Sylow 2 G) (x : P) (y : Q),
110       Fintype.card G = 10 →
111       Subgroup.zpowers x = ⊤ →
112       Subgroup.zpowers y = ⊤ →
```

The conclusion enumerates all four automorphisms with the requested power action (lines 113–116), exactly two homomorphisms and their values on `y` (lines 117–121), the normal/complement/generation facts and semidirect-product equivalence (lines 122–125), and under noncommutativity states `yx=x⁴y` and `(x²y)(x³y)=x⁴` (lines 126–129). No theorem-dependent axiom, opaque constant, or sorry-typed definition was found.

#### b96A02

The registered conjunction states: the order-30 normal-subgroup claims (lines 570–573); the splitting-field/normal-core equivalence (lines 574–577); degree `15` or `30` when the Galois group has order `30` (lines 578–582); and existence of a degree-9 splitting polynomial from a degree-6 one when the Galois group has order `18` (lines 583–587). These are direct encodings of all four prelim parts, with no added core-carrying hypothesis. No theorem-dependent axiom, opaque constant, or sorry-typed definition was found.

#### b96J02

The ring and three candidate module types are defined literally:

```lean
20 def apm_b96J02_squareIdeal : Ideal (ZMod 2)[X] :=
21   Ideal.span {X ^ 2}
23 abbrev apm_b96J02_R := (ZMod 2)[X] ⧸ apm_b96J02_squareIdeal
93 abbrev apm_b96J02_k := apm_b96J02_R ⧸ apm_b96J02_xIdeal
95 abbrev apm_b96J02_freeType := apm_b96J02_R × apm_b96J02_R
97 abbrev apm_b96J02_mixedType :=
98   apm_b96J02_R × (apm_b96J02_k × apm_b96J02_k)
100 abbrev apm_b96J02_trivialType :=
101   apm_b96J02_k × (apm_b96J02_k × (apm_b96J02_k × apm_b96J02_k))
```

The theorem proves all three have cardinality 16 (lines 885–887), are pairwise nonisomorphic (lines 888–893), and every finite 16-element module is equivalent to one of them (lines 894–898). This is exactly the three square-zero Jordan types. Comparing the first statement-bank commit `5afb5ecad6632b8446d75dc190be539e81b2b501` with current HEAD shows only indentation changes on the final disjunction, hence a neutral repair classification. No theorem-dependent axiom, opaque constant, or sorry-typed definition was found.
