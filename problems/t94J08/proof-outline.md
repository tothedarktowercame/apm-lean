# Proof Outline: t94J08

## Compiled progress

`t94J08NormalizedLink_neg` proves that the normalized linking map of `-v` is
exactly the antipodal map composed with the normalized linking map of `v`.
This includes reconciliation of the two dependent nonvanishing witnesses.

## Remaining Lean boundary

The proof still needs the top integral singular homology of the encoded sphere,
the antipodal action on its generator, and multiplicativity of
`t94J08HasDegree`. Because that predicate existentially chooses an orientation
isomorphism, multiplicativity first needs an orientation-independence lemma.
No packaged sphere generator or degree API was found in Mathlib or the
repository.

## Closer hop 2 (2026-08-08)

The abstract degree machinery is now complete.  The lemma
`t94J08HasDegree_with_orientation` proves that the scalar equation is
independent of the existentially selected orientation by first identifying the
induced map with intrinsic integer scalar multiplication.  The lemma
`t94J08HasDegree.comp` then proves multiplicativity using singular-homology
functoriality.  This generalizes the same-orientation composition lemma found
in sibling `t02A08`.

Using those lemmas and `t94J08NormalizedLink_neg`, the entire second conjunct
of the main theorem now compiles: a linking map for `-v` is the antipodal map
composed with the linking map for `v`, and its degree is the required product.
The sole remaining `sorry` is confined to the antipodal-degree family itself,
which still needs the concrete top singular homology of the encoded sphere and
the antipodal action on its generator.  The frozen statement is unchanged.

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal "Relate orientation parity to degrees and local indices for the antipodal map and vector fields." 
 :terms [{:name "degree parity"
          :meaning "For maps S^n → S^n, the degree detects whether the map preserves or reverses orientation; antipodal map has degree (-1)^{n+1}."
          :needed-because "Once the degree is known, the local index statements follow from how vector fields transform under orientation reversal."}
         {:name "local index"
          :meaning "Degree of the normalized vector field map S^{n-1} → S^{n-1} surrounding an isolated zero."
          :needed-because "This definition lets us compare the indices of v and -v by understanding the effect of negating the vector field on that sphere map."}
         {:name "orientation reversal"
          :meaning "The antipodal map acts by −Id on tangent spaces, reversing orientation iff n is even."
          :needed-because "Determining whether −Id preserves orientation is the key step in computing both the map degree and the sign change of the local index."}]
 :strategy [{:id :s1
             :formal-dependency "degree_of_linear_orientation_map"
             :informal-dependency "Stage 1 part (a) uses the determinant of −Id"
             :why-this-now "The degree equals the determinant sign of the linear approximation, which for −Id is (−1)^{n+1}."
             :lean-target "degree_antipodal_and_index_negation"
             :mathlib-status "Mathlib has linear-algebra facts about determinants, but sphere-degree and local-index APIs are still sparse."}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't94J08'
  :frame-id 'apm-v2-t94J08-1775011677105'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-2-completed
  :summary "Explained the determinant-based computation of the antipodal degree and the resulting sign rule for local indices; execute.md now contains the full write-up and dependency graph."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-attempt
  :summary "Attempted to start the Lean proof, but Mathlib lacks both a general sphere-degree API and the definition of vector-field local index; Main.lean therefore remains a stub."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** Students often misinterpret “degree” as just counting preimages and forget it is an *oriented* count; similarly, the local index of a vector field is defined via the degree of a map on the link of the zero. Both statements boil down to orientation bookkeeping, so the trap is to chase coordinates and get lost instead of invoking the determinant of the linearized map.

**Key insight.** The antipodal map is represented in every tangent space by the linear map \(-\mathrm{Id}\), whose determinant is \((-1)^{n+1}\). Degree equals the determinant sign of any orientation-preserving local chart. For the local index, the definition says \(\mathrm{ind}_p(v)=\deg(\varphi)\) where \(\varphi:S^{n-1}\to S^{n-1}\) sends a small linking sphere to the normalized vector values. Replacing \(v\) by \(-v\) multiplies \(\varphi\) by the antipodal map on the *target* sphere, so the index is multiplied by the degree of the antipodal map on \(S^{n-1}\), i.e. by \((-1)^n\).

**Complete proof.**

(a) Let \(A:S^n\to S^n\) be the antipodal map. In local coordinates around any point we may view \(A\) as the restriction of the linear map \(-\mathrm{Id}_{\mathbb{R}^{n+1}}\). The derivative \(dA_x\) is the linear map \(-\mathrm{Id}_{T_x S^n}\) with determinant \((-1)^n\) relative to any positively oriented basis of \(T_x S^n\). As \(A\) reverses orientation iff \(n\) is even, the degree is \(\deg A = (-1)^{n+1}\): +1 for odd \(n\) (orientation-preserving) and −1 for even \(n\) (orientation-reversing). More formally, the degree of a smooth self-map equals the sign of the Jacobian determinant of the derivative at any regular point, hence \((-1)^{n+1}.\)

(b) Take a small sphere \(S^{n-1}_\epsilon\) centered at \(p\) inside \(X\) and consider the map \(\varphi : S^{n-1}_\epsilon \to S^{n-1}\) given by \(x \mapsto v(x)/\|v(x)\|\). Its degree is, by definition, the local index \(\mathrm{ind}_p(v) = d\). For the negated field, \(-v\), the analogous map is \(x \mapsto -v(x)/\|v(x)\| = -\varphi(x)\). Therefore the normalized map for \(-v\) is the composition of \(\varphi\) with the antipodal map on \(S^{n-1}\). Degrees multiply under composition, so
\[
\mathrm{ind}_p(-v) = \deg(\text{antipodal on }S^{n-1})\cdot \deg(\varphi) = (-1)^n \cdot d.
\]
Thus the index flips sign when \(n\) is odd and stays the same when \(n\) is even.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Degree of linear maps.** Formal dependency: if \(L\in\mathrm{GL}_{n+1}(\mathbb{R})\) induces a self-map of \(S^n\), then \(\deg(L|_{S^n}) = \operatorname{sgn}(\det L)\). Needed to handle part (a).
- **Local index = degree of normalized vector field.** Formal dependency: the definition via a small linking sphere. Needed to translate the antipodal factor into the multiplicative rule for degrees.
- **Degree multiplicativity.** Formal dependency: \(\deg(f\circ g) = \deg f \, \deg g\) for self-maps of the sphere. Used in part (b) to incorporate the antipodal factor.

Lean search terms: `sphere_degree_linear`, `VectorField.localIndex`, `degree_mul`, `antipodal`.  
Intended Lean target: `degree_antipodal_and_index_negation`.  
Mathlib status: degree computations for spheres exist only for some linear maps, and local index isn’t formalized yet.

**Stage 3 — LEAN FORMALIZATION**

Mathlib currently lacks (i) a general API for the degree of smooth self-maps of \(S^n\) beyond low-dimensional cases, and (ii) any definition of the local index of a vector field. After inspecting `/home/joe/code/apm-lean/ApmCanaries/Frames/T94J08/Apm_v2_t94J08_1775011677105/Main.lean`, I found no existing constants to build on: there is no `VectorField.localIndex`, and the degree machinery for higher spheres is missing. Consequently the Lean development is blocked at the statement level; completing this problem formally would first require contributing those abstractions to Mathlib. `lake build ...` still fails because the relevant definitions simply do not exist yet.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The informal argument uses only three ingredients—determinants, the definition of local index, and multiplicativity of degree. A future Lean proof must introduce the same abstractions: define the degree of the antipodal map via the determinant of \(-\mathrm{Id}\), implement the local-index-as-degree definition, and use degree multiplicativity. Highlighting these dependencies makes it clear what infrastructure Mathlib needs before this exercise can be formalized.

## Closer hop 3

The point-set antipodal map is now proved involutive and fixed-point-free on
every unit metric sphere. Together with the previously compiled homological
degree composition and normalized-link identity, this removes all nonhomology
bookkeeping. The remaining gap is exactly an orientation isomorphism for top
singular homology of metric spheres and computation of the induced antipodal
map; even the required `H₀(S⁰)` orientation is not packaged in the corpus.
