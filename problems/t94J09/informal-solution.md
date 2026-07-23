<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t94J09: Classifying a polygon by orientability and Euler characteristic

## Why It's Hard

A `2n`-gon with paired edges is a closed surface, and the classification theorem says it is determined by
just **two invariants**: orientability and Euler characteristic. The difficulty is computing these from the
raw edge word without getting lost. Orientability requires scanning how each letter's two occurrences are
oriented (same orientation anywhere `\Rightarrow` non-orientable). The Euler characteristic needs the vertex
count `V`, and *vertex-tracing through edge identifications is the genuinely tedious part* — corners of the
polygon get glued in nonobvious patterns. Here the problem hands us that count (two vertex classes), which is
exactly the input that pins `\chi`. The trap is to trust a cut-and-paste *reduction* algorithm that may
mis-track vertices; the safe path is to compute the two invariants directly, since they are a complete and
unambiguous classification.

## The Key Insight

The word is `w = a\,c\,d^{-1}g^{-1}\,f\,e^{-1}\,b\,c^{-1}\,d^{-1}g^{-1}\,e^{-1}\,f\,a\,b` (a `14`-gon; the
seven letters `a,\dots,g` each appear twice, all edges paired, so the surface is closed).

- **Non-orientable:** `a` occurs as `a \dots a` (both unbarred — same orientation), so the surface is
  non-orientable. (Indeed `a,b,d,e,f,g` all occur as same-orientation pairs; only `c` occurs as `c \dots c^{-1}`.)
- **Euler characteristic:** `F = 1` (one face), `E = 7` (seven distinct edge labels), and `V = 2` (given: one
  big vertex class plus the second class formed by the two corners between `d^{-1}` and `g^{-1}`). So

$$\chi = V - E + F = 2 - 7 + 1 = -4.$$

A **non-orientable** closed surface with `\chi = -4` is `N_k` with `2 - k = -4`, i.e. `k = 6`: the **connected
sum of six real projective planes**.

## Complete Proof

Label the edges around the `14`-gon: `e_1 = a,\ e_2 = c,\ e_3 = d^{-1},\ e_4 = g^{-1},\ e_5 = f,\ e_6 = e^{-1},\ e_7 = b,\ e_8 = c^{-1},\ e_9 = d^{-1},\ e_{10} = g^{-1},\ e_{11} = e^{-1},\ e_{12} = f,\ e_{13} = a,\ e_{14} = b.`
Each of the seven letters `a,b,c,d,e,f,g` appears exactly twice, so every edge is glued to exactly one other:
the quotient is a **closed surface** (compact, no boundary).

**Step 1 — Orientability.** A polygon surface is non-orientable iff some letter appears twice with the *same*
exponent (a pair `x \dots x` or `x^{-1} \dots x^{-1}`), and orientable iff every letter appears once barred and
once unbarred. Checking each:

| letter | occurrences | type |
|---|---|---|
| `a` | `a` (e₁), `a` (e₁₃) | same `\Rightarrow` twisted |
| `b` | `b` (e₇), `b` (e₁₄) | same `\Rightarrow` twisted |
| `c` | `c` (e₂), `c^{-1}` (e₈) | opposite |
| `d` | `d^{-1}` (e₃), `d^{-1}` (e₉) | same `\Rightarrow` twisted |
| `e` | `e^{-1}` (e₆), `e^{-1}` (e₁₁) | same `\Rightarrow` twisted |
| `f` | `f` (e₅), `f` (e₁₂) | same `\Rightarrow` twisted |
| `g` | `g^{-1}` (e₄), `g^{-1}` (e₁₀) | same `\Rightarrow` twisted |

Since at least one letter (in fact six of them) appears as a same-orientation pair, the surface is
**non-orientable**.

**Step 2 — Euler characteristic.** Build the CW structure of the quotient:

- `F = 1`: the single `14`-gon is the only `2`-cell.
- `E = 7`: the seven letters `a,b,c,d,e,f,g` become the seven distinct edges after gluing.
- `V = 2`: by the given vertex identification, the `14` corners fall into exactly two equivalence classes —
  one class containing the two corners situated between `d^{-1}` and `g^{-1}` (positions `e_3\,e_4` and
  `e_9\,e_{10}`), and one class containing all the rest.

Therefore

$$\chi = V - E + F = 2 - 7 + 1 = -4.$$

**Step 3 — Classify.** By the classification of closed surfaces, a non-orientable surface is `N_k = \#^k \mathbb{RP}^2`
with `\chi(N_k) = 2 - k`. Solving `2 - k = -4` gives `k = 6`. Hence

$$\boxed{\ \text{the polygon is the connected sum of } 6 \text{ real projective planes, } N_6\ (\text{non-orientable, } \chi = -4).\ }$$

∎

**Remark.** The classification rests on the two *complete* invariants — orientability and Euler characteristic
— and the **given vertex count `V = 2` is the decisive input**, since it fixes `\chi = 2 - 7 + 1 = -4`. (A
cut-and-paste reduction algorithm in some notes reports `N_3`, but `N_3` has `\chi = -1`, which would require
`V = 5`; that is inconsistent with the stated two-vertex identification and reflects a vertex-bookkeeping slip
in the reduction — exactly the kind of error the invariant computation avoids. The honest invariants give
`\chi = -4`, hence `N_6`.) Equivalently, the surface has non-orientable genus `6` (six crosscaps).
