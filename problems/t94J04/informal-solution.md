<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t94J04: All index-k subgroups of a genus-2 surface group are isomorphic (each is a genus-(k+1) surface group)

## Why It's Hard

For a *general* group, finite-index subgroups of the same index need **not** be isomorphic — index by
itself is a weak invariant. So the theorem is a special rigidity of *surface groups*, and the difficulty is
finding the geometric reason: one must translate "subgroup of index `k`" into a *topological* object whose
isomorphism type is pinned down by `k` alone.

The translation is the **subgroup–cover dictionary**: an index-`k` subgroup `H\le G=\pi_1(F)` is `\pi_1` of a
connected `k`-sheeted cover `\widetilde F\to F`. The crux is then that this cover is again a **closed
orientable surface**, and the *only* freedom — its genus — is **forced** by the **Euler characteristic**:
$$
\chi(\widetilde F) = k\,\chi(F) = k(2-2\cdot2) = -2k,
$$
so the genus is `g'=k+1`, the *same* for every index-`k` subgroup. The classification of surfaces (genus is a
complete invariant) then makes all these covers homeomorphic, hence their `\pi_1`'s isomorphic. The subtle
point is realizing that multiplicativity of `\chi` leaves *no* room: once `k` is fixed, the homeomorphism type
of the cover is determined.

## The Key Insight

Index-`k` subgroups `H\le G` correspond to connected `k`-fold covers `\widetilde F\to F`, with `H\cong
\pi_1(\widetilde F)`. Each `\widetilde F` is a **closed orientable surface** with
$$
\chi(\widetilde F) = k\,\chi(F) = -2k \implies \text{genus } g' = \tfrac{2-\chi}{2} = k+1 .
$$
Since closed orientable surfaces are classified up to homeomorphism by genus, *every* index-`k` cover is
homeomorphic to `\Sigma_{k+1}`, so
$$
H \cong \pi_1(\Sigma_{k+1}) \quad\text{for every index-}k\text{ subgroup } H.
$$
Hence all index-`k` subgroups are isomorphic to one another.

## Complete Proof

Let `F=\Sigma_2` be the closed orientable surface of genus `2`, `G=\pi_1(F)`, and `\chi(F)=2-2\cdot2=-2`. Fix
an integer `k\ge1` and let `H\le G` be any subgroup of index `[G:H]=k`.

### Step 1: index-`k` subgroups are `\pi_1` of `k`-fold covers

`F` is connected, locally path-connected, and semilocally simply connected, so covering-space theory applies:
there is a connected covering `p:\widetilde F\to F` with `p_*\big(\pi_1(\widetilde F)\big)=H`, and the number
of sheets equals the index `[G:H]=k`. Since `p_*` is injective,
$$
H \cong \pi_1(\widetilde F).
$$
(Different index-`k` subgroups give different covers, but we only need each individual `H` realized this way.)

### Step 2: the cover is a closed orientable surface

- **Surface:** `p` is a local homeomorphism, so `\widetilde F` is a `2`-manifold.
- **Closed:** `F` is compact and `p` is a `k`-sheeted (finite) cover, so `\widetilde F` is compact;
  boundaryless because `F` is.
- **Orientable:** orientability lifts through a covering (pull back a coherent orientation via the local
  inverses of `p`), so `\widetilde F` is orientable.

Thus `\widetilde F` is a **closed orientable surface**.

### Step 3: Euler characteristic forces the genus

The Euler characteristic multiplies under a `k`-sheeted covering (triangulate `F`; lift the triangulation, so
each vertex/edge/face has exactly `k` preimages, multiplying the alternating count by `k`):
$$
\chi(\widetilde F) = k\,\chi(F) = k\cdot(-2) = -2k .
$$
A closed orientable surface of genus `g'` has `\chi = 2-2g'`, so
$$
2 - 2g' = -2k \implies g' = k+1 .
$$
Hence `\widetilde F` is a closed orientable surface of genus exactly `k+1`.

### Step 4: classification pins down the isomorphism type

By the **classification of closed orientable surfaces**, two such surfaces are homeomorphic iff they have the
same genus. Therefore every index-`k` cover `\widetilde F` is homeomorphic to the standard genus-`(k+1)`
surface `\Sigma_{k+1}`, and homeomorphic spaces have isomorphic fundamental groups:
$$
H \cong \pi_1(\widetilde F) \cong \pi_1(\Sigma_{k+1}) = \big\langle a_1,b_1,\dots,a_{k+1},b_{k+1} \ \big|\ \textstyle\prod_{i=1}^{k+1}[a_i,b_i]=1\big\rangle .
$$

### Conclusion

This holds for **every** subgroup `H\le G` of index `k`: each is isomorphic to `\pi_1(\Sigma_{k+1})`.
Consequently, all subgroups of `G` of index `k` are isomorphic to one another. ∎

**Remark.** The phenomenon is special to surface groups and is *purely numerical*: the only invariant of a
finite cover of `\Sigma_2` is its sheet number `k`, which fixes `\chi=-2k`, hence the genus `k+1`, hence the
homeomorphism type, hence `\pi_1` — there is simply nowhere for two index-`k` subgroups to differ. This fails
badly for general groups (free groups already have non-isomorphic... no — even free groups behave well by
Nielsen–Schreier, but generic groups do not: a group can have isomorphic-index subgroups of different
isomorphism type). The deeper statement is that finite-index subgroups of a genus-`g` surface group
(`g\ge2`) are exactly the genus-`(k(g-1)+1)` surface groups, the "Riemann–Hurwitz" relation `\chi(\widetilde
F)=k\chi(F)` doing all the work; here `g=2` gives genus `k+1`.
