<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t96A01: An index-n subgroup of a genus-4 surface group is a genus-(3n+1) surface group

## Why It's Hard

Presenting an arbitrary subgroup of a group is generally hard — there is no purely algebraic shortcut, and a
direct attack (Reidemeister–Schreier rewriting on `n` cosets) would produce an unwieldy presentation with no
obvious simplification. The problem is tractable only because **surface groups are special**: their
finite-index subgroups are again surface groups, and *which* one is pinned down by a single number.

The route is geometric. An index-`n` subgroup `H\le\pi_1(S)` is `\pi_1` of a connected `n`-sheeted cover
`\widetilde S\to S`, which is again a **closed orientable surface**; its genus is forced by the **Euler
characteristic**, which multiplies under covers:
$$
\chi(\widetilde S)=n\,\chi(S)=n(2-2\cdot4)=-6n \ \Rightarrow\ \text{genus } g'=\tfrac{2-\chi}{2}=3n+1 .
$$
The subtlety is realizing (i) that the answer depends only on the *index* `n`, not on which subgroup `H` is
chosen (all index-`n` subgroups are isomorphic), and (ii) that one should *not* compute generators by hand —
the genus determines the standard one-relator presentation outright.

## The Key Insight

Index-`n` subgroups of `\pi_1(S)` are fundamental groups of connected `n`-fold covers, which are closed
orientable surfaces. With `\chi(S)=-6`, the cover has `\chi=-6n`, hence genus
$$
g' = 1-\tfrac{\chi}{2} = 1+3n = 3n+1 .
$$
Therefore `H` is the genus-`(3n+1)` surface group:
$$
\boxed{\ H \cong \Big\langle\, x_1,y_1,\dots,x_{3n+1},y_{3n+1} \ \Big|\ \prod_{i=1}^{3n+1}[x_i,y_i]=1 \,\Big\rangle\ }
$$
(`6n+2` generators, one relator — the product of `3n+1` commutators).

## Complete Proof

Let `S` be the closed connected orientable surface of genus `4`, so
$$
\pi_1(S) = \Big\langle a_1,b_1,\dots,a_4,b_4 \ \Big|\ \textstyle\prod_{i=1}^4[a_i,b_i]=1\Big\rangle, \qquad \chi(S)=2-2\cdot4=-6 .
$$
Let `H\le\pi_1(S)` have index `n`.

### Step 1: `H` is the fundamental group of an `n`-fold cover

`S` is connected, locally path-connected, and semilocally simply connected, so covering-space theory applies:
there is a connected covering `p:\widetilde S\to S` with `p_*\big(\pi_1(\widetilde S)\big)=H`, and the number
of sheets equals the index `[\pi_1(S):H]=n`. Since `p_*` is injective,
$$
H \cong \pi_1(\widetilde S).
$$

### Step 2: the cover is a closed orientable surface

- `p` is a local homeomorphism, so `\widetilde S` is a `2`-manifold.
- `S` is compact and `p` is `n`-sheeted (finite), so `\widetilde S` is compact and boundaryless: a *closed*
  surface.
- A covering of an orientable manifold is orientable (lift a coherent orientation through local inverses of
  `p`), so `\widetilde S` is orientable.

Thus `\widetilde S` is a **closed orientable surface**, hence of some genus `g'`, with
`\pi_1(\widetilde S)` the standard genus-`g'` surface group.

### Step 3: Euler characteristic determines the genus

Euler characteristic multiplies under a finite cover (triangulate `S`, lift the triangulation — each cell has
exactly `n` preimages, so every count, and hence the alternating sum, multiplies by `n`):
$$
\chi(\widetilde S) = n\,\chi(S) = n\cdot(-6) = -6n .
$$
A closed orientable surface of genus `g'` has `\chi = 2-2g'`, so
$$
2 - 2g' = -6n \quad\Longrightarrow\quad g' = 1 + 3n = 3n+1 .
$$

### Step 4: write the presentation

Therefore `\widetilde S` is the closed orientable surface of genus `g'=3n+1`, and
$$
H \cong \pi_1(\widetilde S) = \Big\langle\, x_1,y_1,\dots,x_{3n+1},y_{3n+1} \ \Big|\ \prod_{i=1}^{3n+1}[x_i,y_i]=1 \,\Big\rangle,
$$
where `[x_i,y_i]=x_iy_ix_i^{-1}y_i^{-1}`. This is the required presentation: `H` is free on `6n+2` generators
modulo the single relation that the product of the `3n+1` commutators is trivial. ∎

**Check.** For `n=1`, `H=\pi_1(S)` itself, and the formula gives genus `3\cdot1+1=4`, the genus of `S` —
consistent. As `n` grows, the subgroup is a surface group of larger and larger genus.

**Remark.** The presentation depends only on the **index** `n`, not on the particular subgroup: all index-`n`
subgroups of `\pi_1(S)` are isomorphic, because each is `\pi_1` of an `n`-fold cover whose genus `3n+1` is
*forced* by `\chi=n\chi(S)`, and genus is a complete invariant of closed orientable surfaces. This is the
surface-group analogue of Nielsen–Schreier (where index-`n` subgroups of a rank-`r` free group are free of
rank `n(r-1)+1`); here `\chi`-multiplicativity — i.e. Riemann–Hurwitz with no branching — plays the same role,
turning "subgroup of index `n`" into "surface group of genus `1-n\chi(S)/2`." The reason one can *write down*
a clean presentation at all is exactly that the finite-index subgroups of a surface group stay within the
surface-group family.
