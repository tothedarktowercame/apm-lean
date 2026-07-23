<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t02A02: Identifying the surface of the gluing word aabcc⁻¹d⁻¹bd⁻¹ — the Klein bottle

## Why It's Hard

A polygon edge-word hides its surface behind a maze of identifications, and the temptation is to try to
*visualize* the gluing directly — hopeless for an octagon. The disciplined route is the **classification of
closed surfaces**: a closed surface is determined up to homeomorphism by exactly two computable invariants,
**orientability** and **Euler characteristic**. So the work is purely bookkeeping, but each piece has a
characteristic pitfall:

- **Orientability** is read off the *signs* of repeated letters: a letter occurring twice with the *same*
  exponent (like `a\cdots a`) forces a crosscap and non-orientability, whereas opposite exponents
  (`c\cdots c^{-1}`) are orientable handles. One must scan all four letters, not stop at the first.
- **Euler characteristic** needs the **vertex count after identification**, and this is where errors breed:
  the eight corners of the octagon collapse into equivalence classes determined by chasing the edge
  identifications around, and miscounting even one class throws off `\chi` (and hence the answer).
- A subtlety: the word is *not* in normal form, so the surface is not "obvious" — one either reduces the
  word by cut-and-paste, or (cleaner) computes the two invariants directly and invokes classification. The
  adjacent cancelling pair `c\,c^{-1}` is a red herring that can be removed first to shrink the bookkeeping.

## The Key Insight

Don't picture the gluing — compute the two invariants:

- **Non-orientable**, because the letter `a` appears as `a\cdots a` (same exponent): a crosscap. (So do `b`
  and `d^{-1}`.)
- **Euler characteristic `\chi = 0`**: one face, four edges (`a,b,c,d`), and the eight octagon vertices
  collapse to **three** classes, so `\chi = 3 - 4 + 1 = 0`.

A closed surface that is non-orientable with `\chi = 0` is, by the classification theorem, uniquely
$$
N_2 = \mathbb{RP}^2 \,\#\, \mathbb{RP}^2 = \textbf{the Klein bottle}.
$$

## Complete Proof

The word is `w = a\,a\,b\,c\,c^{-1}\,d^{-1}\,b\,d^{-1}`, the boundary of an octagon read cyclically.

### Step 0: it is a closed surface

Each of the four letters `a, b, c, d` occurs **exactly twice** in `w`, so every edge of the octagon is
glued to exactly one other edge. A polygon with all edges identified in pairs yields a **closed surface**
(compact, without boundary). Hence the classification of closed surfaces applies.

### Step 1: orientability — non-orientable

A pairing is orientation-reversing (a crosscap) precisely when a letter occurs twice with the **same**
exponent. In `w`:

- `a` occurs as `a \dots a` — **same** exponent (crosscap),
- `b` occurs as `b \dots b` — **same** exponent,
- `d` occurs as `d^{-1} \dots d^{-1}` — **same** exponent,
- `c` occurs as `c \dots c^{-1}` — opposite (orientable pair).

Since at least one letter (indeed three) is identified with the same orientation, the surface is
**non-orientable**.

### Step 2: Euler characteristic — `\chi = 0`

Take `F = 1` face (the octagon) and `E = 4` edges (`a, b, c, d` after identification). For `V`, label the
octagon's corners `0,1,\dots,7` so that edge in position `k` runs from vertex `k` to vertex `k+1 \pmod 8`:

| pos | letter | directed edge |
|----:|:------:|:-------------:|
| 0 | `a`      | `0 \to 1` |
| 1 | `a`      | `1 \to 2` |
| 2 | `b`      | `2 \to 3` |
| 3 | `c`      | `3 \to 4` |
| 4 | `c^{-1}` | `4 \to 5` |
| 5 | `d^{-1}` | `5 \to 6` |
| 6 | `b`      | `6 \to 7` |
| 7 | `d^{-1}` | `7 \to 0` |

Gluing the two copies of each letter as **directed** edges (tail-to-tail, head-to-head, after reversing any
`{}^{-1}` occurrence) gives the vertex identifications:

- `a`: `(0\to1)` with `(1\to2)` ⟹ `0 = 1`, `1 = 2`.
- `b`: `(2\to3)` with `(6\to7)` ⟹ `2 = 6`, `3 = 7`.
- `c`: `(3\to4)` with `(4\to5)` read as `c` reversed `(5\to4)` ⟹ `3 = 5`, `4 = 4`.
- `d`: `(5\to6)` and `(7\to0)`, each a `d^{-1}`, read as `d` reversed: `(6\to5)` and `(0\to7)` ⟹ `6 = 0`, `5 = 7`.

Chase the equivalences:
$$
\{0,1,2\}\ \xrightarrow{\,2=6\,}\ \{0,1,2,6\}\ \xrightarrow{\,6=0\,}\ \text{(closed)}; \qquad \{3,7\}\ \xrightarrow{\,3=5\,}\ \{3,5,7\}\ \xrightarrow{\,5=7\,}\ \text{(closed)}; \qquad \{4\}\ \text{(alone)}.
$$
All eight corners fall into **three** vertex classes — `\{0,1,2,6\}`, `\{3,5,7\}`, `\{4\}` — so `V = 3`.
Therefore
$$
\chi = V - E + F = 3 - 4 + 1 = 0 .
$$

*(Sanity check by simplification: the adjacent pair `c\,c^{-1}` cancels — a valid homeomorphism — reducing
`w` to the hexagon word `a\,a\,b\,d^{-1}\,b\,d^{-1}`. Recomputing there gives `F=1`, `E=3`, and two vertex
classes `\{0,1,2,4\}, \{3,5\}`, so `V = 2` and `\chi = 2 - 3 + 1 = 0` — the same value, as it must be.)*

### Step 3: classification

By the **classification theorem for closed surfaces**, orientability together with Euler characteristic is a
complete homeomorphism invariant. The non-orientable closed surfaces are `N_k = \#^k\,\mathbb{RP}^2` with
`\chi(N_k) = 2 - k`. Our surface is non-orientable (Step 1) with `\chi = 0` (Step 2), and `2 - k = 0`
gives `k = 2`. Hence
$$
\boxed{\,F \cong N_2 = \mathbb{RP}^2 \,\#\, \mathbb{RP}^2 = \text{the Klein bottle}.\,}
$$
∎

**Remark.** The two invariants pin the answer with no need to picture the gluing: three same-sign letter
pairs already kill orientability, and the vertex collapse to `\chi = 0` selects `N_2` among the
non-orientable surfaces. Equivalently, cut-and-paste reduces `w` to the two-crosscap normal form
`a\,a\,b\,b`, which is exactly `\mathbb{RP}^2 \# \mathbb{RP}^2`; recall the standard identity `\mathbb{RP}^2
\# \mathbb{RP}^2 \cong` Klein bottle (`= N_2`), so the connected-sum description and the Klein-bottle
description agree. Had even one of the repeated letters been an orientable pair throughout, the count could
have landed on an orientable surface (`\chi = 0`, orientable `\Rightarrow` the torus) — which is why reading
the signs in Step 1 is decisive.
