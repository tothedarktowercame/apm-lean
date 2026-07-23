<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t98A03: The wedge T²∨ℝP² — not a manifold, π₁ = ℤ²∗ℤ/2, and its regular vs. irregular 3-fold covers

## Why It's Hard

The space `X=T^2\vee\mathbb{RP}^2` packs four sub-questions, and the covering parts hinge on one structural
constraint that is easy to miss:

- **(a)** The wedge point is the obstruction to being a manifold — a neighborhood there is *two* `2`-disks
  joined at a point, whose punctured neighborhood is *disconnected*, unlike `\mathbb R^2\setminus\{0\}`.
- **(b)** Van Kampen on a wedge gives the **free product** `\pi_1(T^2)*\pi_1(\mathbb{RP}^2)=\mathbb
  Z^2*\mathbb Z/2`.
- **(c),(d)** Connected `3`-fold covers correspond to transitive homomorphisms `\rho:\pi_1(X)\to S_3`, and the
  **decisive constraint** is that the `\mathbb{RP}^2`-generator `c` satisfies `c^2=1`, so `\rho(c)` must be an
  **involution** in `S_3` (the identity or a transposition). This pins down how the projective plane can
  lift: `\rho(c)=\mathrm{id}` lifts `\mathbb{RP}^2` to *three* copies (symmetric → **regular**), while
  `\rho(c)=` a transposition lifts it to one `\mathbb{RP}^2` plus one `S^2` (asymmetric → **irregular**). The
  torus part must be a `3`-cycle to keep the cover connected. Reading off regularity from the *symmetry of
  the sheets* is the key.

## The Key Insight

`\pi_1(X)=\mathbb Z^2*\mathbb Z/2=\langle a,b,c\mid [a,b]=1,\ c^2=1\rangle`. A connected `3`-fold cover is a
transitive `\rho:\pi_1(X)\to S_3`; since `\rho(a),\rho(b)` commute and `\rho(c)^2=1`:

- **Regular** (`(c)`): `\rho(a)=(123)`, `\rho(b)=e`, `\rho(c)=e`. Image `=\langle(123)\rangle\cong\mathbb Z/3`
  (regular action). The torus triple-covers connectedly; `\mathbb{RP}^2` lifts to **three** disjoint
  `\mathbb{RP}^2`'s — all three sheets identical, so the `\mathbb Z/3` deck group acts transitively.
- **Irregular** (`(d)`): `\rho(a)=(123)`, `\rho(b)=e`, `\rho(c)=(12)`. Image `=S_3` (order `6>3`), point
  stabilizer `\{e,(12)\}` non-normal. The torus still triple-covers connectedly, but `\mathbb{RP}^2` lifts to
  one `\mathbb{RP}^2` (over the fixed sheet `3`) plus one `S^2` (the connected double cover over sheets
  `1,2`) — the sheets are *not* interchangeable, so the cover is irregular.

## Complete Proof

Let `x_0` be the wedge point of `X=T^2\vee\mathbb{RP}^2`.

### (a) `X` is not a manifold

A neighborhood of `x_0` in `X` is the union of a neighborhood of `x_0` in `T^2` (a `2`-disk `D`) and a
neighborhood in `\mathbb{RP}^2` (a `2`-disk `D'`), joined only at `x_0`. Deleting `x_0` from a small such
neighborhood `N` gives
$$
N\setminus\{x_0\} = (D\setminus\{x_0\})\ \sqcup\ (D'\setminus\{x_0\}),
$$
a disjoint union of two punctured disks — **two** connected components. If `X` were a `2`-manifold at `x_0`,
`x_0` would have a neighborhood homeomorphic to `\mathbb R^2`, and `\mathbb R^2\setminus\{pt\}` is
**connected** — contradiction. (The other points of `X` are genuine surface points, so `x_0` is the unique
failure.) Hence **`X` is not a manifold**.

### (b) `\pi_1(X)`

`T^2` and `\mathbb{RP}^2` are path-connected with the wedge point a nondegenerate (CW) base point, so by van
Kampen the fundamental group of the wedge is the free product
$$
\pi_1(X) = \pi_1(T^2) * \pi_1(\mathbb{RP}^2) = \mathbb Z^2 * \mathbb Z/2 = \big\langle\, a,b,c \ \big|\ [a,b]=1,\ c^2=1 \,\big\rangle,
$$
where `a,b` generate the torus part (commuting) and `c` generates `\pi_1(\mathbb{RP}^2)=\mathbb Z/2`.

### (c) A regular connected `3`-fold cover

Connected `3`-fold covers correspond to transitive homomorphisms `\rho:\pi_1(X)\to S_3` (up to conjugacy);
the cover is **regular** iff the image is a transitive subgroup of order `3`, i.e. `\langle(123)\rangle`.
Define
$$
\rho(a)=(123),\quad \rho(b)=e,\quad \rho(c)=e
$$
(this respects the relations: `\rho(a),\rho(b)` commute, and `\rho(c)^2=e`). The image is
`\langle(123)\rangle\cong\mathbb Z/3`, acting transitively, so the cover `\widetilde X` is connected and
regular with deck group `\mathbb Z/3`.

**Geometric model.** Over the torus, `a\mapsto(123)` makes the torus triple-cover connectedly — e.g.
`\widetilde T=T^2\xrightarrow{(z,w)\mapsto(z^3,w)}T^2`. The wedge point `x_0` has three preimages
`x_0^{(1)},x_0^{(2)},x_0^{(3)}`. Over `\mathbb{RP}^2`, `c\mapsto e` is trivial, so `\mathbb{RP}^2` lifts to
**three disjoint copies**, one wedged onto `\widetilde T` at each `x_0^{(i)}`:
$$
\widetilde X = \widetilde T \ \vee \ \big(\mathbb{RP}^2 \sqcup \mathbb{RP}^2 \sqcup \mathbb{RP}^2\big)
\quad(\text{one }\mathbb{RP}^2\text{ at each lift of }x_0).
$$
The `\mathbb Z/3` deck group cyclically permutes the three sheets *and* the three `\mathbb{RP}^2`'s, acting
transitively on each fiber — confirming regularity. ✓

### (d) An irregular connected `3`-fold cover exists

**Yes.** Take the transitive homomorphism `\rho:\pi_1(X)\to S_3` with
$$
\rho(a)=(123),\quad \rho(b)=e,\quad \rho(c)=(12).
$$
This respects the relations (`\rho(a),\rho(b)` commute; `\rho(c)^2=(12)^2=e`). The image is
`\langle(123),(12)\rangle=S_3` (a `3`-cycle and a transposition generate `S_3`), which is transitive, so the
corresponding cover `\widetilde X'` is **connected**. It is **irregular**: the image `S_3` has order `6>3`,
so the action is not simply transitive; equivalently the point stabilizer `\operatorname{Stab}(3)=\{e,(12)\}`
is *not normal* in `S_3`, so the index-`3` subgroup `\rho^{-1}(\operatorname{Stab}(3))\le\pi_1(X)` is not
normal — the cover is not regular.

**Geometric model.** As in (c), `a\mapsto(123)` triple-covers the torus connectedly (`\widetilde T`), with
three lifts `x_0^{(1)},x_0^{(2)},x_0^{(3)}`. But now `c\mapsto(12)` acts on the three sheets as the
transposition `(12)`, fixing sheet `3`:

- over sheets `\{1,2\}`: `c` swaps them, so `\mathbb{RP}^2` lifts to its **connected double cover**, namely
  `S^2`, attached to `\widetilde T` at the two points `x_0^{(1)},x_0^{(2)}`;
- over sheet `3`: `c` fixes it, so `\mathbb{RP}^2` lifts to **one `\mathbb{RP}^2`**, attached at `x_0^{(3)}`.

So
$$
\widetilde X' = \widetilde T \ \cup\ \big(S^2 \text{ at } x_0^{(1)},x_0^{(2)}\big) \ \cup\ \big(\mathbb{RP}^2 \text{ at } x_0^{(3)}\big).
$$
The three sheets are now structurally different — two of them carry a shared `S^2`, the third a lone
`\mathbb{RP}^2` — so no deck transformation can move sheet `3` to sheet `1`; the deck group does not act
transitively, confirming the cover is **irregular**. ∎

**Remark.** The whole covering theory of `X` is governed by the relation `c^2=1`: the projective plane's
generator can only map to an **involution** of the fiber, so a `\mathbb{RP}^2` either lifts to copies of
itself (when `\rho(c)` fixes a sheet) or to its double cover `S^2` (when `\rho(c)` swaps two sheets). A
*regular* cover demands all sheets be interchangeable, forcing `\rho(c)` to act *uniformly* — for `3` sheets
the only uniform involution is the identity, giving three `\mathbb{RP}^2`'s; any genuine transposition breaks
the symmetry (one sheet fixed, two swapped) and produces the irregular cover, mixing one `\mathbb{RP}^2` with
one `S^2`. This is the surface-level reason `T^2\vee\mathbb{RP}^2` has both regular and irregular `3`-fold
covers, and exactly mirrors the general dictionary {covers ↔ subgroups}, regular ↔ normal subgroup.
