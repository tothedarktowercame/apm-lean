<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t01J01: Two disjoint separating curves on a genus-2 surface cobound an annulus

## Why It's Hard

The statement is geometric — two curves bound an annulus `S^1 \times I`, i.e. they are "parallel" — but the
hypotheses are *algebraic and homotopical*: each `\gamma_i` is null-homologous (`[\gamma_i] = 0`) yet not
null-homotopic. One must translate these into surface topology and then *rule out every other configuration*
the two curves could be in. The difficulty is that, a priori, two disjoint simple closed curves on a genus-2
surface could be linked in many ways; the conclusion that they must specifically cobound an annulus has to be
forced.

The right translation is the classical fact that on an **orientable** surface a simple closed curve is
null-homologous **iff it separates**. So both `\gamma_i` are separating, and "not null-homotopic" means
neither bounds a disk. The remaining work is a rigidity argument: cutting along `\gamma_1` chops the genus-2
surface into two pieces of *minimal* genus (genus `1` each), and inside such a small piece a separating
non-trivial curve has essentially nowhere to go except parallel to the boundary. Pinning this down is pure
Euler-characteristic bookkeeping — the genus-2 hypothesis is exactly what leaves no other room.

## The Key Insight

On an orientable surface, `[\gamma] = 0 \in H_1 \iff \gamma` separates. So:

- `\gamma_1` separates `S` (genus `2`) into two subsurfaces; since it is not null-homotopic, neither is a
  disk, and Euler characteristic forces each piece to be a **once-holed torus** (genus `1`, one boundary):
  `g_1 + g_2 = 2`, both `\ge 1`, so `g_1 = g_2 = 1`.
- `\gamma_2` is disjoint from `\gamma_1`, so it lies in one piece, say `T_1`. Because `\gamma_2` separates `S`
  while the *other* piece `T_2` stays attached on the `\gamma_1`-side, `\gamma_2` must already **separate
  `T_1`**.
- A separating simple closed curve in a once-holed torus splits it (by Euler characteristic) into either
  **disk + once-holed torus** (so `\gamma_2` is null-homotopic — excluded) or **annulus + once-holed torus**.
  The latter is the only surviving case: `\gamma_2` is parallel to `\partial T_1 = \gamma_1`, and the annulus
  `A` between them has `\partial A = \gamma_1 \cup \gamma_2`.

## Complete Proof

`S` is a closed orientable surface of genus `2`, so `\chi(S) = 2 - 2\cdot 2 = -2`. Recall the standard fact:
on an orientable surface, a simple closed curve `\gamma` is null-homologous **iff** it separates the surface.
Both `\gamma_1, \gamma_2` are null-homologous, hence **separating**, and neither bounds a disk (else it would
be null-homotopic).

**Step 1 — Cutting along `\gamma_1` yields two once-holed tori.** Since `\gamma_1` separates,
`S = \Sigma_1 \cup_{\gamma_1} \Sigma_2`, where `\Sigma_i` has the single boundary circle `\gamma_1`. A
subsurface of genus `g` with one boundary circle has `\chi = 2 - 2g - 1 = 1 - 2g`. Cutting along a circle is
additive on `\chi`, so

$$\chi(\Sigma_1) + \chi(\Sigma_2) = \chi(S) = -2 \implies (1 - 2g_1) + (1 - 2g_2) = -2 \implies g_1 + g_2 = 2.$$

Since `\gamma_1` is not null-homotopic, neither `\Sigma_i` is a disk (genus `0`, one boundary), so `g_i \ge 1`;
hence `g_1 = g_2 = 1`. Write `T_1 = \Sigma_1`, `T_2 = \Sigma_2`: each is a **once-holed torus** with boundary
`\gamma_1` and `\chi(T_i) = -1`.

**Step 2 — `\gamma_2` lies in one piece and separates it.** `\gamma_2` is disjoint from `\gamma_1`, so it sits
in the interior of one piece; say `\gamma_2 \subset T_1` (the case `\gamma_2 \subset T_2` is symmetric). We
claim `\gamma_2` separates `T_1`. Suppose not: then `T_1 \setminus \gamma_2` is connected. Since `T_2` is
attached to `T_1` along `\gamma_1 \subset T_1 \setminus \gamma_2` (a connected set), `S \setminus \gamma_2 = (T_1 \setminus \gamma_2) \cup T_2`
would be connected — contradicting that `\gamma_2` separates `S` (Step 0). Hence `\gamma_2` **separates
`T_1`** into two subsurfaces.

**Step 3 — The separation must be annulus + once-holed torus.** Let `\gamma_2` split `T_1` into `\Sigma_a`
(the piece containing the old boundary `\gamma_1`) and `\Sigma_b`. Then `\Sigma_a` has two boundary circles
(`\gamma_1` and `\gamma_2`) and `\Sigma_b` has one (`\gamma_2`). With genera `g_a, g_b`,

$$\chi(\Sigma_a) + \chi(\Sigma_b) = \chi(T_1) = -1, \quad \chi(\Sigma_a) = 2 - 2g_a - 2 = -2g_a, \quad \chi(\Sigma_b) = 2 - 2g_b - 1 = 1 - 2g_b,$$

so `-2g_a + 1 - 2g_b = -1`, giving `g_a + g_b = 1`. Thus `(g_a, g_b) \in \{(0,1),\, (1,0)\}`:

- `(g_a, g_b) = (1, 0)`: then `\Sigma_b` is genus `0` with one boundary, i.e. a **disk**, so `\gamma_2` bounds
  a disk and is null-homotopic — **excluded** by hypothesis.
- `(g_a, g_b) = (0, 1)`: then `\Sigma_a` is genus `0` with two boundary circles, i.e. an **annulus**, and
  `\Sigma_b` is a once-holed torus.

Only the second case survives. Set `A = \Sigma_a`. Then `A \cong S^1 \times I` is an annulus with

$$\partial A = \gamma_1 \cup \gamma_2.$$

Since `A \subset T_1 \subset S`, this is the desired embedded annulus in `S`. $\qquad\blacksquare$

**Remark.** The argument is a rigidity statement powered entirely by Euler characteristic, and the genus-`2`
hypothesis is essential: it forces `\gamma_1` to split `S` into the smallest possible non-disk pieces
(once-holed tori), inside which a separating non-null-homotopic curve has no room to be anything but
boundary-parallel. The homological hypothesis (`[\gamma_i] = 0`) is what makes the curves separating, and the
homotopical hypothesis (not null-homotopic) is what rules out the disk; together they pin the configuration
to "parallel curves cobounding an annulus." On a higher-genus surface the pieces could have genus `\ge 2`,
and then a disjoint separating curve could split off, say, a genus-`1` subsurface instead of an annulus — so
the conclusion is special to genus `2`.
