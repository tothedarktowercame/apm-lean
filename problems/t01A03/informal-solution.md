<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t01A03: Retractions onto subsurfaces — three "no"s from three different functors (H₁, π₁, π₀)

## Why It's Hard

Each part asks whether a retraction `r : X \to A` exists. The single tool is **functoriality of the
retraction identity**: if `i : A \hookrightarrow X` is the inclusion and `r` a retraction, then `r \circ i
= \mathrm{id}_A`, so applying *any* functor `\mathcal F` (`\pi_0`, `\pi_1`, `H_1`, …) gives
$$
\mathcal F(r) \circ \mathcal F(i) = \mathrm{id}_{\mathcal F(A)} ,
$$
which forces `\mathcal F(i) : \mathcal F(A) \to \mathcal F(X)` to be **injective** (a split monomorphism).
To prove *no* retraction exists, it suffices to find *one* functor for which `\mathcal F(i)` fails to be
injective. The difficulty — and the elegance — is that the three parts are rigged so that **a different
functor is needed each time**, and choosing the wrong one fails to detect the obstruction:

- **(a)** needs `H_1`: the curve is *separating*, hence null-homologous, so `i_*` kills it.
- **(b)** is invisible to `H_1` (the inclusion is an isomorphism on `H_1`!) and requires the **nonabelian**
  `\pi_1`: the commutator that survives in the free group dies in the torus group.
- **(c)** needs only `\pi_0`: `A` is *disconnected* while `X` is connected, so no continuous image of `X`
  can be all of `A`.

Reaching for `H_1` in (b), or for `\pi_1`/`H_1` in (c), obscures the simple obstruction; the skill is
matching the part to the coarsest functor that already sees the failure.

## The Key Insight

`r \circ i = \mathrm{id}_A \Rightarrow \mathcal F(i)` is injective. Run down the hierarchy of functors:

- **(a)** The middle circle `A` *separates* the genus-2 surface `X`, so it bounds a subsurface and is
  **null-homologous**: `i_* : H_1(A) = \mathbb Z \to H_1(X)` is the **zero** map — not injective. No
  retraction.
- **(b)** `A = S^1 \vee S^1` has `\pi_1(A) = F_2` (free), while `\pi_1(X) = \pi_1(T^2) = \mathbb Z^2`; the
  inclusion induces **abelianization** `F_2 \to \mathbb Z^2`, whose kernel contains the nontrivial
  commutator `[a,b]`. Not injective. No retraction. (On `H_1` the same `i_*` is an *isomorphism*, so
  homology cannot detect this — `\pi_1` is essential.)
- **(c)** `A` is **two disjoint circles** (disconnected), `X` is connected. A retract of a connected space
  is connected, but `A` is not. No retraction. (Functorially: `\pi_0(i) : \pi_0(A) \to \pi_0(X)` sends a
  2-element set to a 1-element set, hence is not injective.)

## Complete Proof

**General principle.** Suppose `r : X \to A` is a retraction, `i : A \hookrightarrow X` the inclusion, so
`r \circ i = \mathrm{id}_A`. For any functor `\mathcal F` (`\pi_0`, `\pi_1` with compatible basepoints, or
`H_n`), functoriality gives `\mathcal F(r)\circ \mathcal F(i) = \mathcal F(\mathrm{id}_A) =
\mathrm{id}_{\mathcal F(A)}`. Hence `\mathcal F(i)` has a left inverse and is **injective**. We show in each
case that `\mathcal F(i)` is not injective for a suitable `\mathcal F`, so **no retraction exists**.

Let `X` be the closed orientable genus-2 surface ("two-holed torus"), with
$$
H_1(X) \cong \mathbb Z^4 = \langle a_1, b_1, a_2, b_2\rangle, \qquad
\pi_1(X) = \langle a_1,b_1,a_2,b_2 \mid [a_1,b_1][a_2,b_2]\rangle .
$$

### (a) Separating middle circle — no retraction (homology obstruction)

Here `A` is a circle that cuts `X` into two once-punctured tori; i.e. `A` is a **separating** simple closed
curve. Being separating, `A` is the common boundary of the two pieces: `A = \partial(\text{once-punctured
torus})`. A curve that bounds a subsurface is **null-homologous**, so `[A] = 0` in `H_1(X)`. Therefore the
map induced by inclusion on first homology,
$$
i_* : H_1(A) = \mathbb Z \longrightarrow H_1(X) = \mathbb Z^4, \qquad i_*(\text{generator}) = [A] = 0,
$$
is the **zero** homomorphism. If a retraction `r` existed, `r_* \circ i_* = \mathrm{id}_{H_1(A)} =
\mathrm{id}_{\mathbb Z}` would force `i_*` to be injective — impossible, since `i_* = 0` but `H_1(A) =
\mathbb Z \ne 0`. **No retraction.** ∎

### (b) Wedge of the two torus generators — no retraction (fundamental-group obstruction)

Here `X = T^2` and `A = S^1 \vee S^1` is the 1-skeleton of the standard CW structure on the torus (the two
generating loops `a, b` joined at the vertex), with `X = A \cup (\text{2-cell along } aba^{-1}b^{-1})`. Then
$$
\pi_1(A) = F_2 = \langle a, b\rangle \ (\text{free}), \qquad \pi_1(X) = \pi_1(T^2) = \mathbb Z^2 = \langle a,b \mid [a,b]\rangle ,
$$
and the inclusion induces the **abelianization** homomorphism `i_* : F_2 \to \mathbb Z^2`, `a \mapsto a, b
\mapsto b`. This is not injective: the commutator
$$
[a,b] = aba^{-1}b^{-1} \ne 1 \ \text{in } F_2, \qquad\text{but}\qquad i_*\big([a,b]\big) = [a,b] = 0 \ \text{in } \mathbb Z^2 .
$$
So `[a,b] \in \ker i_* \setminus\{1\}`. A retraction would give `r_* \circ i_* = \mathrm{id}_{\pi_1(A)}`,
forcing `i_*` injective — contradiction. **No retraction.** ∎

*Why homology is not enough here:* on `H_1`, `i_* : H_1(A) = \mathbb Z^2 \to H_1(X) = \mathbb Z^2` is the
identity, hence injective — so the homology test is *passed* and detects nothing. The obstruction is
genuinely nonabelian and only `\pi_1` sees it.

### (c) Two disjoint circles cutting `X` into a 4-holed sphere — no retraction (connectedness obstruction)

Cutting `X` along `A` yields a four-times-punctured sphere, a *single connected* genus-0 surface with **four**
boundary circles. Cutting a surface along a 1-submanifold produces two boundary circles per cut circle, so
four boundary circles means `A` consists of **two disjoint circles** `c_1, c_2` (a quick Euler-characteristic
check confirms the picture: `\chi(X) = -2`, and the 4-holed sphere has `\chi = 2 - 4 = -2`, consistent with
cutting along circles, which preserves `\chi`). In particular `A = c_1 \sqcup c_2` is **disconnected** (two
path-components), while `X` is path-connected.

Now suppose `r : X \to A` were a retraction. Then `r(X) \subseteq A`, and since `r|_A = \mathrm{id}_A` we
have `A \subseteq r(X)`; hence `r(X) = A`. But `X` is connected and `r` is continuous, so `r(X)` is
connected — whereas `A = c_1 \sqcup c_2` is disconnected. Contradiction. **No retraction.** ∎

*(Equivalently, via the `\pi_0` functor: `\pi_0(i) : \pi_0(A) \to \pi_0(X)` maps a 2-element set onto the
1-element set `\pi_0(X)`, so it is not injective, and `\pi_0(r)\circ\pi_0(i) = \mathrm{id}` is impossible.)*

### Summary

In all three cases **no retraction exists**, each blocked at a different level of the functorial hierarchy:

| Part | Subset `A` | Functor that obstructs | Reason `i_*` is not injective |
|:----:|:-----------|:----------------------:|:------------------------------|
| (a) | separating circle | `H_1` | `A` null-homologous, `i_* = 0` on `\mathbb Z` |
| (b) | `S^1 \vee S^1 \subset T^2` | `\pi_1` | commutator `[a,b] \in \ker(F_2 \to \mathbb Z^2)` |
| (c) | two disjoint circles | `\pi_0` | `A` disconnected, `X` connected |

**Remark.** The trio is a ladder of obstructions: connectedness `\pi_0` ⊂ fundamental group `\pi_1` ⊂
first homology `H_1` (abelianization of `\pi_1`). Part (c) fails the coarsest test; part (a) passes `\pi_0`
but fails `H_1`; part (b) passes `\pi_0` and `H_1` but fails the finer, nonabelian `\pi_1`. The lesson is to
test a candidate retraction against the **weakest invariant that already distinguishes `A` from its image in
`X`** — and that an existing retraction would have to split `\mathcal F(i)` for *every* functor
simultaneously.
