<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t03J01: Retracting the double torus onto a curve — primitivity in homology decides

## Why It's Hard

The natural first tool — "the inclusion of a retract induces an *injection* on `\pi_1`" — turns out to be too
weak to settle the problem, and recognizing this is the crux. *Both* curves `J_1` and `J_2` are essential
(not null-homotopic), so for both the inclusion `\pi_1(S^1) = \mathbb Z \to \pi_1(X)` is injective. The
injectivity criterion therefore fails to distinguish them, which is exactly the confusion in a naive
approach.

The correct, finer invariant is that a retraction induces not merely an injection but a **split surjection**
`r_* : \pi_1(X) \to \pi_1(J) = \mathbb Z` with `r_*([J]) = 1`. Because `\mathbb Z` is abelian, `r_*` factors
through the abelianization `H_1(X)`, so a retraction forces a homomorphism `H_1(X) \to \mathbb Z` sending
`[J]` to a *generator* — i.e. `[J]` must be a **primitive** (indivisible, nonzero) homology class. The whole
problem reduces to: is `[J_i]` primitive in `H_1(X) = \mathbb Z^4`? The separating/non-separating distinction
between `J_2` and `J_1` answers exactly this, and the surprise is that `J_2`, though `\pi_1`-essential, is
*null-homologous* (a commutator), so it admits no retraction.

## The Key Insight

For a circle `J \subset X` (closed orientable surface), **`X` retracts onto `J` iff `[J]` is primitive in
`H_1(X;\mathbb Z)`.**

- *Necessary:* a retraction `r` gives `r_* \circ j_* = \mathrm{id}_{\mathbb Z}`; abelianizing, a homomorphism
  `\varphi : H_1(X) \to \mathbb Z` with `\varphi([J]) = 1`, so `[J]` is primitive.
- *Sufficient:* if `[J]` is primitive, there is `\alpha \in H^1(X;\mathbb Z) = [X, S^1]` with
  `\langle\alpha, [J]\rangle = 1`, i.e. a map `f : X \to S^1` restricting to a degree-`1` map on `J`;
  straightening that degree-`1` self-map to the identity and extending by the homotopy extension property
  yields an honest retraction.

Now:
- `J_1` (cutting `X` into one **connected** piece) is **non-separating**, so `[J_1] \ne 0` is **primitive** —
  `X` retracts onto `J_1`.
- `J_2` (cutting `X` into **two** once-punctured tori) is **separating**, so `[J_2] = 0` — `X` does *not*
  retract onto `J_2`.

## Complete Proof

`X` is the genus-`2` surface, with `\pi_1(X) = \langle a_1,b_1,a_2,b_2 \mid [a_1,b_1][a_2,b_2]\rangle` and
`H_1(X;\mathbb Z) = \mathbb Z^4 = \langle a_1,b_1,a_2,b_2\rangle`. For a subspace circle `J \subset X` write
`j : J \hookrightarrow X` for the inclusion and `[J] \in H_1(X)` for its homology class.

**The retraction criterion.** Suppose `r : X \to J` is a retraction, `r \circ j = \mathrm{id}_J`. Then on
fundamental groups `r_* \circ j_* = \mathrm{id}_{\pi_1(J)} = \mathrm{id}_{\mathbb Z}`, so `r_*` is a
homomorphism `\pi_1(X) \to \mathbb Z` with `r_*(j_*(1)) = 1`. As `\mathbb Z` is abelian, `r_*` factors as
`\pi_1(X) \twoheadrightarrow H_1(X) \xrightarrow{\varphi} \mathbb Z`, and `\varphi([J]) = 1`. Thus a retraction
**forces** a homomorphism `\varphi : H_1(X) = \mathbb Z^4 \to \mathbb Z` with `\varphi([J]) = 1`, which exists
iff `[J]` is **primitive** (its coordinates have gcd `1`; in particular `[J] \ne 0`). This is the necessary
condition we use below; its sufficiency (degree-`1` map to `S^1` + homotopy extension) is recorded in the Key
Insight.

### (a) `X` retracts onto `J_1` — YES

Cutting `X` along `J_1` yields a *single connected* surface (the twice-punctured piece), so `J_1` is
**non-separating**: `X \setminus J_1` is connected. A non-separating simple closed curve on a closed orientable
surface represents a **primitive** class in `H_1(X)` — concretely, `J_1` is part of a symplectic basis
`a_1,b_1,a_2,b_2`, say `[J_1] = a_1`, which is indivisible and nonzero.

Hence the homomorphism `\varphi : H_1(X) \to \mathbb Z` dual to that basis (`\varphi(a_1) = 1`, `\varphi` zero
on the others) satisfies `\varphi([J_1]) = 1`. Equivalently, there is a class `\alpha \in H^1(X;\mathbb Z)`
with `\langle\alpha,[J_1]\rangle = 1`, hence a map `f : X \to S^1` whose restriction to `J_1` has degree `1`.
Identify the target `S^1` with `J_1`; then `f|_{J_1} : J_1 \to J_1` is degree `1`, homotopic to
`\mathrm{id}_{J_1}`. Since `(X, J_1)` is a CW pair (cofibration), the homotopy extension property extends this
homotopy to a homotopy of `f` to a map `r : X \to J_1` with `r|_{J_1} = \mathrm{id}_{J_1}`. So `r` is a
retraction:

$$\boxed{\ X \text{ retracts onto } J_1.\ }$$

### (b) `X` retracts onto `J_2` — NO

Cutting `X` along `J_2` yields **two** pieces (two once-punctured tori), so `J_2` is **separating**. A
separating simple closed curve is **null-homologous**: it is the common boundary of the two complementary
subsurfaces `\Sigma_1, \Sigma_2`, so `[J_2] = \partial[\Sigma_1] = 0` in `H_1(X)`. (In `\pi_1`, `J_2` is the
nontrivial commutator `[a_1,b_1] = [a_2,b_2]^{-1}`, which is `\ne 1` but lies in the commutator subgroup,
hence dies in `H_1`.)

If a retraction `r : X \to J_2` existed, the criterion above would give `\varphi : H_1(X) \to \mathbb Z` with
`\varphi([J_2]) = 1`. But `[J_2] = 0`, so every homomorphism gives `\varphi([J_2]) = 0 \ne 1` — contradiction.

$$\boxed{\ X \text{ does not retract onto } J_2.\ }$$

**Remark.** The lesson is that `\pi_1`-injectivity of the inclusion — which holds for **both** curves, since
each is essential — is *necessary but not sufficient* for a retraction. The right invariant is the
**splitting**, which abelianizes to primitivity in `H_1`. The separating curve `J_2` is the sharp
counterexample: it is `\pi_1`-essential (a nontrivial commutator) yet *null-homologous*, so it is detected as
"non-retractible" only by passing to homology. Geometrically, a retraction onto a circle requires a
"coordinate" `X \to S^1` that wraps once around `J`; non-separating curves carry such a coordinate (they have a
dual curve), separating curves do not (they bound on both sides).
