<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t02A01: An abelian cover of the once-punctured torus splits its boundary into n circles

## Why It's Hard

The space `S` (a torus minus an open disk) has a single boundary circle, and the claim is that *every*
regular cover with cyclic deck group `\mathbb Z/n` splits that one circle into exactly `n` upstairs. A priori
the boundary could lift to *any* number of components (`1`, `n`, or something in between), with each
component wrapping the boundary some number of times — the question is why the count is forced to be the
maximum, `n`.

The crux is an algebraic fact that is easy to overlook: the boundary `\partial S` of a once-punctured torus
is not just any loop, it is the **commutator** `[a,b]` of the two generators of `\pi_1(S) = F_2`. Whether the
boundary lifts to a loop or to a longer multiply-wrapped circle is controlled by where its class lands in the
deck group under the classifying homomorphism — and because the deck group `\mathbb Z/n` is **abelian**, every
commutator dies. Connecting "boundary = commutator," "abelian deck group kills commutators," and "trivial
monodromy `\Rightarrow` `n` components" is the chain that must be assembled.

## The Key Insight

`S` deformation retracts to `S^1 \vee S^1`, so `\pi_1(S) = F_2 = \langle a, b\rangle`, and the boundary circle
represents the commutator `c = [a, b] = aba^{-1}b^{-1}`. A regular cover with deck group `\mathbb Z/n` is
classified by a surjection `\varphi : F_2 \to \mathbb Z/n`. Since `\mathbb Z/n` is abelian,

$$\varphi(c) = \varphi([a,b]) = \varphi(a) + \varphi(b) - \varphi(a) - \varphi(b) = 0.$$

So the boundary loop has **trivial image** in the deck group: its monodromy permutation of the `n`-point fiber
is the identity. A circle's preimage in an `n`-fold cover is a disjoint union of circles whose count equals
the number of cycles of the boundary monodromy; with the identity permutation there are `n` fixed points,
hence `n` cycles. Therefore `\widetilde S` has exactly `n` boundary components, each mapping homeomorphically
onto `\partial S`.

## Complete Proof

**Setup.** `S` is a torus with an open disk removed — a compact surface of genus `1` with one boundary circle
`\partial S`. It deformation retracts onto a wedge of two circles, so `\pi_1(S) = F_2 = \langle a, b\rangle`
(free of rank `2`), and the boundary circle represents the commutator

$$[\partial S] = c = [a, b] = aba^{-1}b^{-1} \in \pi_1(S)$$

(the standard fact that the boundary of the once-punctured torus is the commutator of its two handle loops).

Let `p : \widetilde S \to S` be a regular (normal) covering with deck group `G \cong \mathbb Z/n`. It is
classified by a surjective homomorphism `\varphi : \pi_1(S) \to G` whose kernel is `p_*\pi_1(\widetilde S)`;
the cover has `|G| = n` sheets, and `G` acts on each fiber `p^{-1}(x)` simply transitively.

**Step 1 — The boundary loop lies in the kernel.** Because `G \cong \mathbb Z/n` is abelian, every commutator
maps to the identity:

$$\varphi(c) = \varphi([a,b]) = [\varphi(a), \varphi(b)] = 0 \in G.$$

So `c = [\partial S] \in \ker\varphi = p_*\pi_1(\widetilde S)`.

**Step 2 — The boundary monodromy is trivial.** Restrict `p` over the boundary circle: `p^{-1}(\partial S) \to \partial S`
is an `n`-fold covering of the circle `\partial S \cong S^1`. Identify the fiber over a basepoint
`x_0 \in \partial S` with `G` (`n` points). The monodromy of a loop `\gamma` based at `x_0` acts on the fiber
by the deck transformation `\varphi(\gamma)`; for the boundary loop `c` this action is translation by
`\varphi(c) = 0`, i.e. the **identity** permutation of the fiber.

**Step 3 — Count the boundary components.** The components of the cover `p^{-1}(\partial S) \to S^1` correspond
bijectively to the **cycles** of the boundary monodromy permutation, and each component covers `\partial S`
with degree equal to the length of its cycle. Since the monodromy is the identity on the `n`-element fiber, it
has `n` cycles, each of length `1`. Hence `p^{-1}(\partial S)` consists of exactly `n` circles, each mapping
**homeomorphically** (degree `1`) onto `\partial S`. These `n` circles are precisely the boundary components of
`\widetilde S`. Therefore

$$\boxed{\ \widetilde S \text{ has exactly } n \text{ boundary components.}\ }\qquad\blacksquare$$

**Remark.** Everything hinges on the deck group being **abelian**: it forces the (commutator) boundary class
to vanish in `G`, making the boundary monodromy trivial and splitting the single boundary circle into the
*maximum* number of lifts, `n`, each of degree `1`. If instead the cover had a nonabelian deck group with
`\varphi([a,b]) \ne 0`, the boundary monodromy could be a nontrivial permutation, and `\partial S` would lift
to fewer (but longer, multiply-wrapped) circles — the number of boundary components would be `[G : \langle \varphi(c)\rangle]`,
which here is `[G : \{0\}] = n`. The geometric content is that an abelian cover "unwinds" the commutator
boundary completely.
