<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t91A06: Baire category in compact Hausdorff spaces — a countable intersection of dense opens is dense

## Why It's Hard

This is the **Baire Category Theorem**, but in the *compact Hausdorff* setting rather than the familiar
complete-metric one — so the standard proof (nested closed balls of radius `\to 0`, Cauchy sequence,
completeness) is unavailable: there is no metric, no radius, no Cauchy sequence. One must find the two
substitutes that compact-Hausdorff provides:

- **Completeness is replaced by compactness.** Instead of extracting a limit of a Cauchy sequence, one
  produces a point in a nested intersection of nonempty *closed* sets via the **finite intersection
  property** of compact spaces. This is the engine that guarantees the desired point exists.
- **Shrinking balls are replaced by regularity.** To nest the closures, one needs, inside any open set `O`
  around a point `x`, a smaller open `V` with `\overline V \subseteq O`. This "shrinking room" is exactly
  **regularity**, which is *not assumed* — it must be *derived* from "compact + Hausdorff." Forgetting that
  this derivation is needed (and using Hausdorff as if it gave regularity for free) is the classic gap.

The proof is a recursion: at stage `n` use density of `U_n` to enter `U_n`, then use regularity to shrink to
a closure trapped inside `U_n` and the previous set; compactness then harvests a point common to all of
them and to the test set `W`.

## The Key Insight

To prove `\bigcap_i U_i` is dense, show it meets every nonempty open `W`. Build a **nested sequence of
nonempty open sets** `V_1 \supseteq \overline{V_1}\supseteq V_2 \supseteq \overline{V_2}\supseteq\cdots`
with `\overline{V_n}\subseteq U_n \cap V_{n-1}` (and `\overline{V_1}\subseteq U_1\cap W`), using:

- **density of `U_n`** to make `U_n \cap V_{n-1}` nonempty (so the recursion never stalls), and
- **regularity** (from compact Hausdorff) to shrink to a `V_n` whose closure sits inside.

The closures `\overline{V_n}` are nested nonempty closed subsets of the compact `X`, so by the **finite
intersection property** their intersection contains a point `x`. That `x` lies in `W` (`\subseteq
\overline{V_1}`) and in every `U_n` (`\subseteq \overline{V_n}`), hence in `W \cap \bigcap_i U_i`.

## Complete Proof

Let `X` be compact Hausdorff and `\{U_i\}_{i\ge 1}` a countable family of dense open subsets; put
`G = \bigcap_{i\ge 1} U_i`. To prove `G` is dense, fix an arbitrary **nonempty open** set `W\subseteq X`;
we find a point of `G` in `W`.

### Lemma (compact Hausdorff is regular: shrinking closures)

> For any point `x` and open set `O` with `x\in O`, there is an open `V` with `x\in V\subseteq \overline V
> \subseteq O`.

*Proof.* Let `C = X\setminus O`, a closed set with `x\notin C`. Since `X` is compact, `C` is compact. By
Hausdorffness, for each `c\in C` choose disjoint open sets `A_c\ni x` and `B_c\ni c`. The `\{B_c\}_{c\in C}`
cover the compact `C`, so finitely many suffice: `C\subseteq B := B_{c_1}\cup\cdots\cup B_{c_k}`. Put
`V := A_{c_1}\cap\cdots\cap A_{c_k}`, an open neighborhood of `x`. Then `V\cap B = \varnothing` (each
`A_{c_i}` is disjoint from `B_{c_i}`, so `V\subseteq A_{c_i}` is disjoint from `B_{c_i}`, hence from the
union `B`). Thus `V\subseteq X\setminus B`, which is closed, so
$$
\overline V \subseteq X\setminus B \subseteq X\setminus C = O .
$$
Hence `x\in V\subseteq\overline V\subseteq O`. ∎

### The recursive construction

**Base step.** `U_1` is dense and `W` is nonempty open, so `U_1\cap W` is a **nonempty open** set; pick a
point `x_1\in U_1\cap W`. By the Lemma there is a nonempty open `V_1` with
$$
x_1\in V_1\subseteq \overline{V_1}\subseteq U_1\cap W .
$$

**Inductive step.** Suppose a nonempty open `V_n` has been chosen. Since `U_{n+1}` is dense and `V_n` is
nonempty open, `U_{n+1}\cap V_n` is **nonempty open**; pick `x_{n+1}\in U_{n+1}\cap V_n`. By the Lemma there
is a nonempty open `V_{n+1}` with
$$
x_{n+1}\in V_{n+1}\subseteq \overline{V_{n+1}}\subseteq U_{n+1}\cap V_n .
$$

This produces, for every `n\ge 1`, a nonempty open `V_n` with `\overline{V_n}\subseteq U_n\cap V_{n-1}`
(reading `V_0 := W`). In particular each `\overline{V_n}` is nonempty, and they are **nested**:
$$
\overline{V_{n+1}}\subseteq V_n\subseteq \overline{V_n}, \qquad\text{so}\qquad \overline{V_1}\supseteq \overline{V_2}\supseteq \overline{V_3}\supseteq\cdots .
$$

### Compactness harvests the point

Each `\overline{V_n}` is a closed subset of the compact space `X`, hence compact, and nonempty; the family
`\{\overline{V_n}\}_{n\ge 1}` is nested, so every finite subfamily has nonempty intersection (it equals the
smallest member). By the **finite intersection property** characterization of compactness,
$$
\bigcap_{n\ge 1} \overline{V_n} \ne \varnothing .
$$
Choose `x \in \bigcap_{n\ge 1}\overline{V_n}`. Then:

- `x\in\overline{V_1}\subseteq U_1\cap W\subseteq W`, so `x\in W`;
- for every `n\ge 1`, `x\in\overline{V_n}\subseteq U_n\cap V_{n-1}\subseteq U_n`, so `x\in U_n`.

Hence `x\in\bigcap_{n\ge 1}U_n = G` **and** `x\in W`, i.e. `W\cap G\ne\varnothing`.

### Conclusion

Since every nonempty open set `W` meets `G`, the set `G = \bigcap_{i} U_i` is **dense** in `X`. ∎

**Remark.** The proof is the exact structural analogue of the complete-metric Baire theorem, with the two
defining properties of `X` playing the two roles that completeness-and-metric play there: *Hausdorff (plus
compact) ⇒ regularity*, which supplies the "shrinking room" `\overline V\subseteq O` (the analogue of
choosing a smaller ball), and *compactness ⇒ finite intersection property*, which supplies the limit point
(the analogue of completeness producing a Cauchy limit). Density of the `U_n` is what keeps the recursion
alive at each stage. The conclusion is the Baire category statement: a countable intersection of dense
opens is dense, so a compact Hausdorff space is a **Baire space** — it is not a countable union of nowhere-
dense sets (take complements: a countable union of closed sets with empty interior has empty interior).
