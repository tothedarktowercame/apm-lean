<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t97J04: Two punctured tori glued along a circle (one capped by a meridian disk)

## Why It's Hard

The space `X` is assembled from two pieces that look almost the same — a once-punctured torus `T` and a
once-punctured torus `M` with a **meridian disk** glued in — joined along their common boundary circle `C`. The
work is in reading the topology of `M` correctly: the meridian disk does **two** things at once. It **kills the
meridian generator** (`c = 1`), and — because the boundary `C` of a punctured torus is the commutator of the
two torus generators — it makes `C` **null-homotopic** in `M`. The trap in van Kampen is to think the gluing
relation `[a,b] = [c,d]` is vacuous because both sides are commutators (hence both die in homology). It is *not*
vacuous: once `c = 1` collapses `[c,d]` to `1`, the relation forces `[a,b] = 1`, **abelianizing the torus
part**. So `\pi_1(X) = \mathbb Z^2 * \mathbb Z`, not a free group and not `\mathbb Z^2 * \mathbb Z^2`. In
homology the same commutator fact makes *both* gluing maps on `H_1` vanish, so Mayer–Vietoris splits and — the
surprise — produces `H_2(X) = \mathbb Z` even though neither `T` nor `M` has any `H_2`.

## The Key Insight

Identify the pieces by their `\pi_1` and by where the gluing circle `C` goes:

- `T` = punctured torus: `\pi_1(T) = \langle a, b\rangle` (free), and `C = \partial T = [a,b]`.
- `M` = punctured torus `+` meridian disk: `\pi_1(M) = \langle c, d \mid c\rangle \cong \mathbb Z` (the disk
  kills the meridian `c`), and `C = \partial M = [c,d]`, which becomes `[1,d] = 1` — null-homotopic in `M`.

**Van Kampen** amalgamates over `\pi_1(C) = \mathbb Z`, identifying `[a,b] \sim [c,d]`:

$$\pi_1(X) = \langle a, b, c, d \mid c,\ [a,b] = [c,d]\rangle = \langle a, b, d \mid [a,b]\rangle \cong \mathbb Z^2 * \mathbb Z.$$

**Mayer–Vietoris**: `[C]` is a commutator on *both* sides, so it is null-homologous in both `H_1(T)` and
`H_1(M)`; the map `H_1(C) \to H_1(T)\oplus H_1(M)` is **zero**. The sequence splits to give

$$H_0(X) = \mathbb Z, \quad H_1(X) = \mathbb Z^3, \quad H_2(X) = \mathbb Z, \quad H_n(X) = 0\ (n \ge 3).$$

The clean model: gluing the two punctured-torus *surfaces* along `C` is a closed **genus-2 surface** `\Sigma_2`,
and `X \simeq \Sigma_2` with a disk attached along a (non-separating) meridian — which is exactly what kills one
`H_1` generator and leaves the genus-2 fundamental class as the generator of `H_2(X)`.

## Complete Proof

Thicken the union slightly into open sets `A \supseteq T` and `B \supseteq M` with `A \simeq T`, `B \simeq M`,
and `A \cap B \simeq C = S^1`. Both pieces are connected and `C \ne \varnothing`, so `X` is connected.

### The two pieces

**`T` (punctured torus).** A torus with an open disk removed deformation-retracts to `S^1 \vee S^1`, so
`\pi_1(T) = \langle a, b\rangle` is free of rank `2` and `H_*(T) = (\mathbb Z, \mathbb Z^2, 0)`. The boundary
circle is the commutator: `[C] = [\partial T] = aba^{-1}b^{-1} = [a,b]` in `\pi_1(T)`.

**`M` (punctured torus `+` meridian disk).** Start from a punctured torus with `\pi_1 = \langle c, d\rangle` and
boundary `[c,d]`, then attach a `2`-cell along the meridian `c`. This adds the relation `c = 1`:

$$\pi_1(M) = \langle c, d \mid c \rangle \cong \langle d \rangle \cong \mathbb Z.$$

Cellularly `M` is one `0`-cell, two `1`-cells `c, d`, one `2`-cell `e` with `\partial e = c`; so
`\partial_2(e) = c`, giving `H_0(M) = \mathbb Z`, `H_1(M) = \mathbb Z^2/\langle c\rangle = \mathbb Z\langle d\rangle`,
`H_2(M) = \ker\partial_2 = 0`. Thus `M \simeq S^1` and `H_*(M) = (\mathbb Z, \mathbb Z, 0)`. Its boundary circle
is `[C] = [\partial M] = [c,d]`, which equals `[1,d] = 1` in `\pi_1(M)` (and is null-homologous regardless,
being a commutator).

### (a) Fundamental group by van Kampen

With `\pi_1(A) = \langle a,b\rangle`, `\pi_1(B) = \langle c,d \mid c\rangle`, and `\pi_1(A\cap B) = \langle\gamma\rangle`
(`\gamma = [C]`), van Kampen identifies the two images of `\gamma`: `i_*(\gamma) = [a,b]` in `A` and
`j_*(\gamma) = [c,d]` in `B`. Hence

$$\pi_1(X) = \langle a, b, c, d \mid \underbrace{c}_{\text{meridian disk}},\ \underbrace{[a,b] = [c,d]}_{\text{glue along }C}\rangle.$$

Substituting `c = 1` collapses `[c,d] = [1,d] = 1`, so the gluing relation becomes `[a,b] = 1`, and `d` survives
freely. Eliminating `c`:

$$\boxed{\ \pi_1(X) = \langle a, b, d \mid aba^{-1}b^{-1} \rangle \;\cong\; \mathbb Z^2 * \mathbb Z.\ }$$

(The torus generators `a,b` commute — coming from `T`'s now-capped surface — while `d` is a free `\mathbb Z`
factor.)

### (b) Homology by Mayer–Vietoris

Inputs: `H_*(A) = (\mathbb Z, \mathbb Z^2, 0)`, `H_*(B) = (\mathbb Z, \mathbb Z, 0)`,
`H_*(A\cap B) = (\mathbb Z, \mathbb Z, 0)`. The key computation is the `H_1` boundary map
`\varphi : H_1(C) \to H_1(T) \oplus H_1(M)`. Since `[C] = [a,b]` is a commutator, it is **null-homologous** in
`H_1(T)`; since `[C] = [c,d]` is a commutator (and `c = 0`), it is null-homologous in `H_1(M)`. Hence

$$\varphi([C]) = (0, 0), \qquad \varphi = 0.$$

The reduced Mayer–Vietoris sequence

$$0 = H_2(T)\oplus H_2(M) \to H_2(X) \to H_1(C) \xrightarrow{\ \varphi = 0\ } H_1(T)\oplus H_1(M) \to H_1(X) \to \widetilde H_0(C) = 0$$

now reads off directly:

- **`H_2(X)`:** the map `H_2(X) \to H_1(C)` is injective (previous term `0`) with image `\ker\varphi = H_1(C) = \mathbb Z`. So `H_2(X) = \mathbb Z`.
- **`H_1(X)`:** since `\varphi = 0`, the map `H_1(T)\oplus H_1(M) \to H_1(X)` is injective, and it is onto because the next term `\widetilde H_0(C) = 0`. So `H_1(X) = H_1(T)\oplus H_1(M) = \mathbb Z^2 \oplus \mathbb Z = \mathbb Z^3`.
- **`H_0(X)`** `= \mathbb Z` (connected); `H_n(X) = 0` for `n \ge 3` (a `2`-complex, and the sequence gives `0`).

$$\boxed{\ H_0(X) = \mathbb Z,\quad H_1(X) = \mathbb Z^3,\quad H_2(X) = \mathbb Z,\quad H_n(X) = 0\ (n \ge 3).\ }$$

**Consistency checks.** Abelianizing the presentation `\langle a,b,d \mid [a,b]\rangle` (the relation `[a,b]`
becomes trivial in the abelianization) gives `H_1(X) = \mathbb Z^3`, matching MV. And Euler characteristics
agree: `\chi(X) = \chi(T) + \chi(M) - \chi(C) = (-1) + 0 - 0 = -1`, while `1 - 3 + 1 = -1` from the homology.

**Remark (where `H_2` comes from).** Glue the two punctured-torus *surfaces* `T` and `M_{\text{surf}}` along `C`:
two genus-`1` surfaces-with-one-boundary joined along that boundary form a **closed genus-`2` surface**
`\Sigma_2 \subset X`. Its fundamental class generates `H_2(X) \cong \mathbb Z` — this is the unexpected
`2`-cycle, present even though neither `T` nor `M` alone has any `H_2`. The meridian disk is then a `2`-cell
attached to `\Sigma_2` along the meridian `c`, a *non-separating* simple closed curve: this attaches `\partial e = c`,
so it kills one `H_1` generator (`H_1(\Sigma_2) = \mathbb Z^4 \rightsquigarrow \mathbb Z^3`) but leaves
`\ker\partial_2 = H_2 = \mathbb Z` untouched, and in `\pi_1` it sets `c = 1`, turning the genus-`2` relation
`[a,b][c,d] = 1` into `[a,b] = 1`. So `X \simeq \Sigma_2 \cup_c (\text{disk})`, which is the geometry behind both
answers. `\blacksquare`
