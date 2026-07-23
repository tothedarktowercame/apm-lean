<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t01A01: A non-surjective self-map of RP² is null-homotopic

## Why It's Hard

The hypothesis "`f` is not surjective" looks mild but is a powerful topological constraint, and the whole
problem is about extracting its consequences. Missing even a single point `q` forces `f` to land in
`\mathbb{RP}^2 \setminus \{q\}`, and the crucial — non-obvious — fact (the hint) is that puncturing the
projective plane *destroys its `2`-cell*, leaving a space homotopy equivalent to a **circle** (a Möbius
band, which retracts to its core `\mathbb{RP}^1 \cong S^1`). So `f` is really a map into `S^1`, whose
fundamental group `\mathbb Z` is **torsion-free**, while the source `\pi_1(\mathbb{RP}^2) = \mathbb Z/2` is
pure torsion. There is no nonzero homomorphism from a finite group to `\mathbb Z`, so `f_*` must be trivial.

The second part — upgrading "`f_*` trivial" to "`f` null-homotopic" — is where one must avoid the trap of
thinking trivial `\pi_1` action automatically gives null-homotopy (false in general). Here it works because
the target factor is `S^1`, whose universal cover `\mathbb R` is **contractible**: the lifting criterion lets
`f` lift to `\mathbb R` and then contract.

## The Key Insight

`\mathbb{RP}^2 \setminus \{q\}` deformation retracts onto a projective line `\mathbb{RP}^1 \cong S^1` (it is a
Möbius band), so `\pi_1(\mathbb{RP}^2 \setminus \{q\}) = \mathbb Z`. Non-surjectivity factors `f` as

$$\mathbb{RP}^2 \xrightarrow{\ g\ } \mathbb{RP}^2 \setminus \{q\} \simeq S^1 \xhookrightarrow{\ \iota\ } \mathbb{RP}^2.$$

- **`f_*` is trivial:** `g_* : \pi_1(\mathbb{RP}^2) = \mathbb Z/2 \to \pi_1(\mathbb{RP}^2\setminus\{q\}) = \mathbb Z`
  is a homomorphism from a torsion group to a torsion-free group, hence `g_* = 0`; so `f_* = \iota_* \circ g_* = 0`.
- **`f` is null-homotopic:** `g` is essentially a map `\mathbb{RP}^2 \to S^1` with `g_* = 0`; by the lifting
  criterion it lifts to the contractible universal cover `\mathbb R \to S^1`, so `g` (and hence `f`) is
  homotopic to a constant.

## Complete Proof

Let `f : \mathbb{RP}^2 \to \mathbb{RP}^2` be continuous and **not** surjective, so there is a point
`q \notin f(\mathbb{RP}^2)`. Then `f` factors through the inclusion:

$$f = \iota \circ g, \qquad g : \mathbb{RP}^2 \to \mathbb{RP}^2 \setminus \{q\}, \quad \iota : \mathbb{RP}^2 \setminus \{q\} \hookrightarrow \mathbb{RP}^2,$$

where `g` is just `f` with restricted codomain.

**Step 1 — `\mathbb{RP}^2 \setminus \{q\} \simeq S^1`.** Model `\mathbb{RP}^2 = D^2/(x \sim -x \text{ on } \partial D^2)`
and take `q` to be the image of the center `0 \in D^2`. Then `\mathbb{RP}^2 \setminus \{q\} = (D^2 \setminus \{0\})/\!\sim`.
The radial deformation retraction of `D^2 \setminus \{0\}` onto `\partial D^2` is antipodally equivariant, so it
descends to a deformation retraction of `\mathbb{RP}^2 \setminus \{q\}` onto `\partial D^2/(x \sim -x) = \mathbb{RP}^1 \cong S^1`.
(Equivalently, `\mathbb{RP}^2` minus a point is a Möbius band, which retracts to its core circle.) Hence

$$\pi_1\big(\mathbb{RP}^2 \setminus \{q\}\big) \cong \pi_1(S^1) = \mathbb Z.$$

**Step 2 — `f_*` is trivial.** On fundamental groups, `f_* = \iota_* \circ g_*` where

$$g_* : \pi_1(\mathbb{RP}^2) = \mathbb Z/2 \longrightarrow \pi_1(\mathbb{RP}^2 \setminus \{q\}) = \mathbb Z.$$

A group homomorphism sends the order-`2` generator `a` to an element `g_*(a)` with `2\,g_*(a) = g_*(a^2) = g_*(1) = 0`
in `\mathbb Z`; since `\mathbb Z` is torsion-free, `g_*(a) = 0`. Thus `g_* = 0`, and therefore

$$f_* = \iota_* \circ g_* = 0,$$

i.e. `f_* : \pi_1(\mathbb{RP}^2) \to \pi_1(\mathbb{RP}^2)` has image `\{1\}`. $\quad\checkmark$

**Step 3 — `f` is homotopic to a constant.** Compose `g` with the homotopy equivalence
`r : \mathbb{RP}^2 \setminus \{q\} \xrightarrow{\simeq} S^1` to get `h = r \circ g : \mathbb{RP}^2 \to S^1`, with
`h_* = r_* \circ g_* = 0` on `\pi_1` (Step 2, `r_*` an isomorphism). Let `p : \mathbb R \to S^1` be the universal
covering; its image on `\pi_1` is `p_*(\pi_1(\mathbb R)) = \{1\}`. Since

$$h_*\big(\pi_1(\mathbb{RP}^2)\big) = \{1\} \subseteq p_*\big(\pi_1(\mathbb R)\big) = \{1\},$$

the **lifting criterion** provides a lift `\tilde h : \mathbb{RP}^2 \to \mathbb R` with `p \circ \tilde h = h`
(`\mathbb{RP}^2` is path-connected and locally path-connected). The cover `\mathbb R` is **contractible**, so
`\tilde h` is homotopic to a constant map; pushing that homotopy down by `p`, `h = p \circ \tilde h` is
homotopic to a constant. Hence `g \simeq r^{-1} \circ h` and `f = \iota \circ g` are homotopic to constant maps:

$$\boxed{\ f \text{ is homotopic to a constant map.}\ }\qquad\blacksquare$$

**Remark.** The engine is the hint: removing a point collapses the `2`-cell of `\mathbb{RP}^2`, turning it into
(homotopically) a circle, and a circle's fundamental group `\mathbb Z` is torsion-free. The torsion class
`a \in \mathbb Z/2` simply cannot survive a map into `\mathbb Z`, which forces `f_* = 0`; and because the target
factor `S^1` has a contractible universal cover, trivial-on-`\pi_1` upgrades to genuinely null-homotopic. The
same argument shows any map from a space with torsion (or finite) fundamental group into `\mathbb{RP}^2` that
misses a point is null-homotopic. (Contrast: a *surjective* self-map of `\mathbb{RP}^2`, such as the identity,
can have `f_* = \mathrm{id}` — non-surjectivity is exactly what kills `f_*`.)
