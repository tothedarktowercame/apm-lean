<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t03J03: Double covers of the genus-3 non-orientable surface, and lifting cylinders

## Why It's Hard

`X = \mathbb{RP}^2 \# \mathbb{RP}^2 \# \mathbb{RP}^2` is the non-orientable surface `N_3` (Dyck's surface),
with `\chi(X) = -1`, and the problem tests two layers of covering-space theory. Part (a) asks for the
*homeomorphism types* of the `2`-fold covers, which means combining the algebraic classification (index-`2`
subgroups `\leftrightarrow` surjections `\pi_1(X) \to \mathbb Z/2`) with the topological constraint that any
double cover of a surface is again a surface with `\chi` doubled — and then deciding *which* surfaces arise
and which are orientable. The non-orientability of `X` is what makes this interesting: exactly one double
cover (the orientation cover) is orientable.

Part (b) is a lifting question dressed up geometrically. The temptation is to think a cylinder might fail to
lift the way a Möbius band would. The key realization is that "`Y` orientable" pins `Y` down to *the
orientation double cover*, so lifting is governed entirely by the orientation character `w_1`: a loop lifts
iff it is orientation-preserving. An **embedded cylinder** has a `2`-sided core (it *is* an annular
neighborhood of its core), and `2`-sided `\Leftrightarrow` orientation-preserving — so the lifting criterion
is automatically satisfied. Seeing that "embedded cylinder" forces `2`-sidedness is the crux.

## The Key Insight

`\pi_1(X) = \langle a,b,c \mid a^2 b^2 c^2\rangle`, so `H_1(X) = \mathbb Z^2 \oplus \mathbb Z/2`, and
`\operatorname{Hom}(H_1, \mathbb Z/2) = (\mathbb Z/2)^3`.

- **(a)** Connected `2`-fold covers `\leftrightarrow` the `7` nonzero homomorphisms `\pi_1(X) \to \mathbb Z/2`,
  and every one has `\chi = 2\chi(X) = -2`, hence is either the orientable genus-`2` surface `\Sigma_2`
  (`\chi = 2 - 2g = -2`) or the non-orientable `N_4` (`\chi = 2 - k = -2`). The orientation character
  `w_1 : a,b,c \mapsto 1` gives the *orientation cover* `\Sigma_2`; it is the **only** orientable one (any
  orientable double cover has `\pi_1(Y) \subseteq \ker w_1`, forcing equality by index `2`). The other `6`
  covers are `N_4`. (Plus the disconnected trivial cover `X \sqcup X`.)

- **(b)** "`Y` orientable" forces `Y = \Sigma_2 =` orientation cover, so `\pi_*\pi_1(Y) = \ker w_1`. A map of
  a cylinder `C` lifts iff its core class lands in `\ker w_1`, i.e. is orientation-preserving. An **embedded**
  cylinder's core is `2`-sided, hence orientation-preserving, so it always lifts. **True.**

## Complete Proof

`X = N_3`, with `\pi_1(X) = \langle a,b,c \mid a^2 b^2 c^2 = 1\rangle`. Abelianizing,
`H_1(X) = \mathbb Z^3 / \langle 2(a+b+c)\rangle \cong \mathbb Z^2 \oplus \mathbb Z/2`, and `\chi(X) = 2 - 3 = -1`.

### (a) The `2`-fold coverings

A connected `2`-fold cover corresponds to an index-`2` (automatically normal) subgroup, equivalently a
surjection `\varphi : \pi_1(X) \to \mathbb Z/2`. These factor through `H_1(X)`, so they are the nonzero
elements of `\operatorname{Hom}(H_1(X), \mathbb Z/2) = \operatorname{Hom}(\mathbb Z^2 \oplus \mathbb Z/2,\, \mathbb Z/2) = (\mathbb Z/2)^3`
— exactly `7` of them.

**The total spaces.** A `2`-fold cover `\widetilde X \to X` is a closed surface with `\chi(\widetilde X) = 2\,\chi(X) = -2`.
A closed surface with `\chi = -2` is either:

- **orientable** genus `g` with `2 - 2g = -2`, i.e. `g = 2` — the genus-`2` surface `\Sigma_2`; or
- **non-orientable** genus `k` with `2 - k = -2`, i.e. `k = 4` — the surface `N_4 = \#^4 \mathbb{RP}^2`.

**Which is which.** The orientation character `w_1 : \pi_1(X) \to \mathbb Z/2` (sending each crosscap
generator `a, b, c \mapsto 1`; well-defined since `w_1(a^2b^2c^2) = 6 \equiv 0`) is nontrivial because `X` is
non-orientable. Its kernel gives the **orientation double cover**, whose total space is **orientable**, hence
`\Sigma_2`. Conversely, if a connected double cover `\widetilde X` is orientable then `\pi_1(\widetilde X) \subseteq \ker w_1`,
and since both have index `2` they are equal — so the orientation cover is the *unique* orientable one. The
remaining `6` covers are all non-orientable, hence each homeomorphic to `N_4`.

**Covering maps.** For the orientation cover (`\varphi = w_1`, `a,b,c \mapsto 1`): `\Sigma_2 \to X` is the
standard orientation double cover (the two sheets are the two local orientations of `X`). For a non-orientable
example (`\varphi : a \mapsto 1,\ b,c \mapsto 0`, which satisfies `\varphi(a^2b^2c^2) = 2 \equiv 0` and is
onto): the associated cover `N_4 \to X` unwraps the `a`-crosscap while leaving `b, c` doubled. In all cases
the cover is the one classified by the subgroup `\ker\varphi`. (Including the disconnected trivial cover
`X \sqcup X \to X` for the zero homomorphism.)

$$\boxed{\ \text{The connected }2\text{-fold covers are }\Sigma_2\ (\text{orientation cover, unique orientable one})\ \text{and }N_4\ (\text{the other }6).\ }$$

### (b) Every embedded cylinder lifts — TRUE

Let `Y` be orientable with `\pi : Y \to X` a `2`-fold cover. Since `X` is non-orientable, the disconnected
cover `X \sqcup X` is non-orientable, so `Y` is connected; by part (a) the *only* orientable connected double
cover is the orientation cover, so

$$Y = \Sigma_2, \qquad \pi_*\pi_1(Y) = \ker w_1.$$

Let `f : C \hookrightarrow X` be an embedding of a cylinder `C = S^1 \times [0,1]`, with core circle
`K = f(S^1 \times \{\tfrac12\})` generating `f_*\pi_1(C) = \langle [K]\rangle \cong \mathbb Z`.

**The core is `2`-sided, hence orientation-preserving.** Inside the embedded cylinder, `K` has the annular
neighborhood `f(S^1 \times (\tfrac12 - \varepsilon, \tfrac12 + \varepsilon))`, i.e. `K` has a neighborhood
homeomorphic to `S^1 \times (-\varepsilon, \varepsilon)` — a `2`-sided (orientable) neighborhood. A simple
closed curve in a surface is `2`-sided iff it is orientation-preserving (`w_1([K]) = 0`); a `1`-sided curve
would instead have a Möbius-band neighborhood. So `w_1([K]) = 0`, i.e. `[K] \in \ker w_1`.

**Apply the lifting criterion.** Since `C` is path-connected and locally path-connected, `f` lifts to `Y` iff

$$f_*\pi_1(C) = \langle [K]\rangle \subseteq \pi_*\pi_1(Y) = \ker w_1,$$

which holds because `[K] \in \ker w_1`. Therefore `f` lifts to `Y`. As the embedded cylinder was arbitrary,
**every** embedding of a cylinder into `X` lifts to `Y`. The statement is **true**. $\qquad\blacksquare$

**Remark.** The hypotheses are exactly tuned. "`Y` orientable" is what makes `Y` the orientation cover, so
that lifting is decided by the single character `w_1`. "Cylinder, **embedded**" is what guarantees a `2`-sided
core: the annulus is itself the orientable neighborhood, forcing `w_1 = 0` on the core. If instead one
embedded a **Möbius band**, its core is `1`-sided (`w_1 = 1 \notin \ker w_1`), and it would *not* lift —
indeed a Möbius band exists in `N_3` precisely because `X` is non-orientable. So the contrast between cylinder
(`2`-sided, lifts) and Möbius band (`1`-sided, does not) is the geometric heart of the orientation double cover.
