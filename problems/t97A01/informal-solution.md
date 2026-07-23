<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t97A01: The genus-3 non-orientable surface, two ways (Dyck's theorem)

## Why It's Hard

`X = \mathbb{RP}^2 \# \mathbb{RP}^2 \# \mathbb{RP}^2` is the non-orientable surface `N_3`, and the problem
asks to see it through **two different decompositions** and confirm they agree — a check of **Dyck's
theorem** that `N_3 \cong T^2 \# \mathbb{RP}^2`. The polygon/CW route (a,b) needs the right edge word and a
careful cellular boundary; the cut-and-paste route (c) needs the homology classes of the *gluing circle* on
each side, which are non-obvious: on the torus side it is a commutator (null-homologous), on the projective
side it is *twice* the Möbius core (the source of the `\mathbb Z/2` torsion). The recurring trap is the
factor of `2`: the crosscaps each contribute `\partial = 2(\cdot)`, and tracking those evens is exactly what
produces the torsion in `H_1` and the relation `[a,b] = c^2` in `\pi_1`. Getting the two computations to
match is the real content.

## The Key Insight

`N_3` has the hexagon presentation with edge word `a^2 b^2 c^2`: one vertex, three edges `a,b,c`, one face
attached by `aabbcc`, so the cellular boundary is `\partial_2 f = 2a + 2b + 2c = 2(a+b+c)`. This single
relation gives

$$H_1 = \mathbb Z^3/\langle 2(a+b+c)\rangle = \mathbb Z^2 \oplus \mathbb Z/2, \qquad H_2 = 0, \qquad H_0 = \mathbb Z.$$

Viewing the *same* surface as `T^2 \# \mathbb{RP}^2 = A \cup B` with `A = T^2 \setminus \text{disk} \simeq S^1 \vee S^1`,
`B = \mathbb{RP}^2 \setminus \text{disk} = \text{Möbius} \simeq S^1`, `A \cap B \simeq S^1`: the gluing circle
is the commutator `[a,b]` in `A` (boundary of the holed torus, null-homologous) and `c^2` in `B` (the Möbius
boundary wraps twice around the core `c`). Mayer–Vietoris recovers `H_1 = \mathbb Z^2 \oplus \mathbb Z/2`, and
van Kampen gives `\pi_1 = \langle a,b,c \mid [a,b] = c^2\rangle` — whose abelianization is again
`\mathbb Z^2 \oplus \mathbb Z/2`. The two decompositions agree.

## Complete Proof

### (a) A CW decomposition of `X = N_3`

`N_3` is the quotient of a regular **hexagon** by the edge identifications spelling the word `a^2 b^2 c^2` (i.e.
`a\,a\,b\,b\,c\,c` read around the boundary). The CW structure:

- **`0`-cells:** one vertex `v` (all six corners are identified to a single point under the word `a^2b^2c^2`);
- **`1`-cells:** three edges `a, b, c` (each appearing twice on the boundary);
- **`2`-cell:** one face `f`, the hexagon, attached along `a^2 b^2 c^2`.

(Check: `\chi = V - E + F = 1 - 3 + 1 = -1`, the Euler characteristic of `N_3`.)

### (b) Homology from the CW decomposition

Cellular chain complex `0 \to C_2 \xrightarrow{\partial_2} C_1 \xrightarrow{\partial_1} C_0 \to 0` with
`C_0 = \mathbb Z\langle v\rangle`, `C_1 = \mathbb Z\langle a,b,c\rangle`, `C_2 = \mathbb Z\langle f\rangle`.

- `\partial_1 = 0`: each edge is a loop at `v`, so `\partial a = v - v = 0`, etc.
- `\partial_2 f`: each generator's coefficient is its total exponent in the attaching word `a^2 b^2 c^2`, all
  `+2` (the two occurrences of each letter have the same orientation, the non-orientable feature). So
  `\partial_2 f = 2a + 2b + 2c = 2(a+b+c)`.

Homology:

- `H_0 = C_0/\operatorname{im}\partial_1 = \mathbb Z`.
- `H_1 = \ker\partial_1/\operatorname{im}\partial_2 = \mathbb Z^3/\langle 2(a+b+c)\rangle`. Change basis to
  `\{a, b, u\}` with `u = a+b+c`; then `\mathbb Z^3/\langle 2u\rangle = \mathbb Z\langle a\rangle \oplus \mathbb Z\langle b\rangle \oplus \mathbb Z\langle u\rangle/2\mathbb Z\langle u\rangle = \mathbb Z^2 \oplus \mathbb Z/2`.
- `H_2 = \ker\partial_2`: `\partial_2 f = 2(a+b+c) \ne 0`, so `\partial_2` is injective, `H_2 = 0`.
- `H_k = 0` for `k \ge 3`.

$$\boxed{\ H_0 = \mathbb Z,\quad H_1 = \mathbb Z^2 \oplus \mathbb Z/2,\quad H_2 = 0,\quad H_k = 0\ (k\ge3).\ }$$

### (c) `X = T^2 \# \mathbb{RP}^2` (Dyck's theorem: same surface)

Write `X = A \cup B`: `A = T^2 \setminus (\text{open disk}) \simeq S^1 \vee S^1` (`\pi_1(A) = \langle a,b\rangle`,
`H_1(A) = \mathbb Z^2`), `B = \mathbb{RP}^2 \setminus (\text{open disk}) = `Möbius band `\simeq S^1`
(`\pi_1(B) = \langle c\rangle`, `H_1(B) = \mathbb Z`), and `A \cap B \simeq S^1` (the gluing circle, generator
`\gamma`). The two key facts:

- in `A`, the boundary circle is `\gamma = [a,b] = aba^{-1}b^{-1}`, a **commutator**, so `[\gamma] = 0` in
  `H_1(A)`;
- in `B`, the Möbius boundary wraps **twice** around the core: `\gamma = c^2`, so `[\gamma] = 2[c]` in
  `H_1(B) = \mathbb Z`.

#### (c-i) Homology by Mayer–Vietoris

`H_*(A) = (\mathbb Z, \mathbb Z^2, 0)`, `H_*(B) = (\mathbb Z, \mathbb Z, 0)`, `H_*(A\cap B) = (\mathbb Z, \mathbb Z, 0)`.
The relevant `H_1`-map `\varphi : H_1(A\cap B) = \mathbb Z \to H_1(A)\oplus H_1(B) = \mathbb Z^2 \oplus \mathbb Z`
sends the gluing class to `([\gamma]_A,\, [\gamma]_B) = (0,\ 2[c])`, i.e. `\varphi(1) = (0,0,2)` (up to sign).

Reading the sequence `\cdots \to H_2(A)\oplus H_2(B) = 0 \to H_2(X) \to H_1(A\cap B) \xrightarrow{\varphi} H_1(A)\oplus H_1(B) \to H_1(X) \to H_0(A\cap B) \xrightarrow{\psi} H_0(A)\oplus H_0(B) \to \cdots`:

- `\varphi` is injective (`(0,0,2) \ne 0`), so `H_2(X) = \ker\varphi = 0`.
- `\psi : \mathbb Z \to \mathbb Z^2`, `1 \mapsto (1,-1)`, is injective, so the map `H_1(X) \to H_0(A\cap B)` is
  zero, giving `H_1(X) = \operatorname{coker}\varphi = (\mathbb Z^2 \oplus \mathbb Z)/\langle(0,0,2)\rangle = \mathbb Z^2 \oplus \mathbb Z/2`.
- `H_0(X) = \mathbb Z` (connected).

$$H_0(X) = \mathbb Z,\quad H_1(X) = \mathbb Z^2 \oplus \mathbb Z/2,\quad H_2(X) = 0,$$

**matching part (b)** — the two decompositions describe the same surface.

#### (c-ii) Fundamental group by van Kampen

With `\pi_1(A) = \langle a,b\rangle` (free), `\pi_1(B) = \langle c\rangle`, and `\pi_1(A\cap B) = \langle\gamma\rangle`,
van Kampen identifies the two images of `\gamma`: `i_*(\gamma) = [a,b]` in `A` and `j_*(\gamma) = c^2` in `B`.
Hence

$$\boxed{\ \pi_1(X) = \langle a, b, c \mid aba^{-1}b^{-1} = c^2\rangle = \langle a,b,c \mid [a,b] = c^2\rangle.\ }$$

(Abelianizing — set `[a,b] = 0` — gives `\langle a,b,c \mid 2c = 0\rangle = \mathbb Z^2 \oplus \mathbb Z/2`,
consistent with `H_1`.) ∎

**Remark.** The whole problem is one surface (`N_3 = T^2 \# \mathbb{RP}^2`, Dyck's theorem) computed two ways,
and the answers agree by construction. The signature of non-orientability is the **factor of `2`**: in the
polygon it is the same-orientation pairing `a^2 b^2 c^2` giving `\partial_2 = 2(a+b+c)`; in the connected-sum
picture it is the Möbius boundary `c^2` (the crosscap wrapping twice). Either way the lone even relation
produces the torsion `\mathbb Z/2` in `H_1` and the relation `[a,b] = c^2` in `\pi_1`. (`H_2 = 0` is the
homological signature of non-orientability — no fundamental class over `\mathbb Z`.)
