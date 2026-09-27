# Common face of adjacent path swaps

`ConstructionTargets.ProductSimplexAdjacentSwapCommonFace` compares a
`MaximalPath p q` with `adjacentSwapPath z h i`, where `h : n + 1 = p + q`
and `i : Fin n`. It reuses the balanced-word coordinate formula, reconstructed
path vertices, `face_objEquiv`, and `productAffine_comp_face`.

- `adjacentSwap_prefix_counts` preserves both prefix counts at every index
  whose value differs from `i.val + 1`. The private `prefix_card_swap` proves
  this by a bijection of the filtered prefix sets.
- `adjacentSwap_vertex` gives equality from source to swapped grid vertices
  away from that intermediate corner.
- `adjacentSwap_retained_vertex` specializes this equality to all vertices
  retained by deleting `(finCongr h i.castSucc).succ`.
- `adjacentSwap_simplicial_face` equates the source and swapped simplicial
  faces after transporting the simplex dimension along `h` and deleting
  `i.succ.castSucc`. The private `objEquiv_cast` handles dimension transport.
- `adjacentSwap_affine_face` equates the source and swapped `productAffine`
  maps composed with `faceAffine n i.succ.castSucc`, using vertex transport
  through `finCongr (congrArg (· + 1) h)`.
- `adjacentSwap_corner_ne` proves distinct intermediate corners when the
  source balanced word `(wordPathEquiv p q).symm z` has unequal letters at
  `finCongr h i.castSucc` and `finCongr h i.succ`.

The retained-vertex and face equalities do not require unequal letters;
that hypothesis is used only for corner distinctness. Both face comparisons
are exact equalities directed from the source path to its adjacent swap.

This supplies the common-face step for `t03J05`, `t96J06`, and `t97A04`.
Shuffle parity change and internal-face cancellation remain before
cross-product assembly. This packet assigns no signs, constructs no chains
or cross products, edits no consumers, and claims no consumer closure.
