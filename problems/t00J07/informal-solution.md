<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t00J07: Capping RP² with a disk — wedge with a sphere, or unwrap to a sphere

## Why It's Hard

Attaching a `2`-disk to `\mathbb{RP}^2` along an embedded circle `f : S^1 \to \mathbb{RP}^2` produces a new
space `X = \mathbb{RP}^2 \cup_f D^2`, and the difficulty is that the answer depends *entirely* on a single
piece of data: the homotopy class `[f] \in \pi_1(\mathbb{RP}^2) = \mathbb Z/2`. The same disk attached two
"different ways" (null-homotopic versus essential) gives genuinely different spaces, so one must (i) see that
only `[f]` matters — attaching along homotopic maps yields homotopy-equivalent spaces — and (ii) correctly
track its effect on both `\pi_1` (which gets a new relation) and homology (which needs the cellular chain
complex with the right attaching degrees).

The conceptual surprise is part (b): capping the *essential* circle does not just modify `\mathbb{RP}^2` a
little — it **unwraps it into a sphere**. The new disk supplies exactly the data needed to undo the antipodal
identification that made `\mathbb{RP}^2` projective in the first place, so `\pi_1` collapses from `\mathbb Z/2`
to trivial. Recognizing that the degree-`1` and degree-`2` attaching maps interact via `\gcd(2,1) = 1` is the
computational heart.

## The Key Insight

Use the CW structure `\mathbb{RP}^2 = e^0 \cup e^1 \cup e^2`, where the `2`-cell `e_1^2` is attached along `a^2`
(`a` the generator of `\pi_1 = \mathbb Z/2 = \langle a \mid a^2\rangle`). Attaching a further `2`-cell along
`[f]`:

- **adds the relation `[f] = 1`** to `\pi_1`: `\pi_1(X) = \pi_1(\mathbb{RP}^2)/\langle\langle [f]\rangle\rangle`;
- **adds a `2`-cell `e_2^2`** whose cellular boundary is `\partial e_2^2 = (\deg[f])\,a`.

Since `[f] \in \mathbb Z/2`:

- **(a) `[f] = 0`** (null): no relation, `\partial e_2^2 = 0`. So `X \simeq \mathbb{RP}^2 \vee S^2`, and
  `\pi_1 = \mathbb Z/2`, `H_* = (\mathbb Z, \mathbb Z/2, \mathbb Z)`.
- **(b) `[f] = a`** (essential): relation `a = 1` kills `\pi_1`, and `\partial e_2^2 = a`. The two
  `2`-cells now bound `2a` and `a`, and `\gcd(2,1) = 1` makes `H_1 = 0` while `H_2 = \mathbb Z`. So `X \simeq S^2`.

## Complete Proof

`\mathbb{RP}^2` has `\pi_1 = \mathbb Z/2 = \langle a \mid a^2\rangle` and homology
`H_0 = \mathbb Z`, `H_1 = \mathbb Z/2`, `H_2 = 0`. In its minimal CW structure, the chain groups are
`C_0 = \mathbb Z\langle e^0\rangle`, `C_1 = \mathbb Z\langle a\rangle`, `C_2 = \mathbb Z\langle e_1^2\rangle`,
with `\partial_1 = 0` and `\partial_2 e_1^2 = 2a` (the `2`-cell wraps the `1`-skeleton circle by degree `2`).
Attaching a disk to `\mathbb{RP}^2` along `f` adds one `2`-cell `e_2^2` with `\partial_2 e_2^2 = (\deg [f])\,a`,
where `\deg[f]` is the degree of `f` onto the `1`-skeleton (`0` if `[f]` is null, `1` if `[f] = a`, since `f`
is an embedded essential circle representing the generator).

### (a) `f` homotopically trivial

**Fundamental group.** Attaching a `2`-cell along the null class kills nothing:
`\pi_1(X) = \pi_1(\mathbb{RP}^2)/\langle\langle 1\rangle\rangle = \mathbb Z/2`. Indeed, since `f \simeq \text{const}`,
`X \simeq \mathbb{RP}^2 \cup_{\text{const}} D^2 = \mathbb{RP}^2 \vee S^2` (a constant attaching map collapses
`\partial D^2`, turning the disk into a wedged sphere).

$$\boxed{\ \pi_1(X) = \mathbb Z/2.\ }$$

**Homology.** With `\partial_2 e_2^2 = 0`, the cellular complex is
`0 \to \mathbb Z^2 \xrightarrow{\partial_2} \mathbb Z \xrightarrow{0} \mathbb Z \to 0`,
`\partial_2(e_1^2, e_2^2) = (2a, 0)`:

- `H_0 = \mathbb Z`;
- `H_1 = C_1/\operatorname{im}\partial_2 = \mathbb Z/\langle 2a, 0\rangle = \mathbb Z/2`;
- `H_2 = \ker\partial_2 = \{(m,n) : 2m = 0\} = \mathbb Z\langle e_2^2\rangle \cong \mathbb Z`.

$$\boxed{\ H_0 = \mathbb Z,\quad H_1 = \mathbb Z/2,\quad H_2 = \mathbb Z,\quad H_k = 0\ (k \ge 3).\ }$$

(Equivalently `\widetilde H_*(\mathbb{RP}^2 \vee S^2) = \widetilde H_*(\mathbb{RP}^2) \oplus \widetilde H_*(S^2)`.)

### (b) `f` homotopically nontrivial

**Fundamental group.** Now `[f] = a`, so attaching the disk adds the relation `a = 1`:

$$\pi_1(X) = \langle a \mid a^2,\, a\rangle = \langle a \mid a\rangle = 1.$$

$$\boxed{\ \pi_1(X) = 1 \ (\text{trivial}).\ }$$

**Homology.** With `\partial_2 e_2^2 = a`, the complex is
`0 \to \mathbb Z^2 \xrightarrow{\partial_2} \mathbb Z \xrightarrow{0} \mathbb Z \to 0`,
`\partial_2(e_1^2, e_2^2) = (2a, a)`, i.e. `\partial_2(m,n) = (2m + n)a`:

- `H_0 = \mathbb Z`;
- `H_1 = \mathbb Z/\langle 2a, a\rangle = \mathbb Z/\langle a\rangle = 0` (since `\gcd(2,1) = 1`, the image is all of `C_1`);
- `H_2 = \ker\partial_2 = \{(m,n) : 2m + n = 0\} = \mathbb Z\langle e_1^2 - 2e_2^2\rangle \cong \mathbb Z`.

$$\boxed{\ H_0 = \mathbb Z,\quad H_1 = 0,\quad H_2 = \mathbb Z,\quad H_k = 0\ (k \ge 3).\ }$$

Since `X` is simply connected with the homology of `S^2`, by Hurewicz and Whitehead `X \simeq S^2`. ∎

**Remark.** The two cases are distinguished by `\pi_1` (and by `H_1`): capping the *trivial* circle merely
glues on a sphere, `X \simeq \mathbb{RP}^2 \vee S^2`, leaving `\pi_1 = \mathbb Z/2`; capping the *essential*
circle imposes `a = 1`, which together with the pre-existing `a^2 = 1` trivializes `\pi_1` and "unwraps"
`\mathbb{RP}^2` into a sphere, `X \simeq S^2`. Cellularly, the magic is `\gcd(2,1) = 1`: the original
degree-`2` cell and the new degree-`1` cell jointly generate all of `H_1`, killing the torsion that made
`\mathbb{RP}^2` projective, while their kernel leaves one `\mathbb Z` in `H_2`. The new disk is precisely the
missing hemisphere whose absence (via antipodal gluing) created the projective plane.
