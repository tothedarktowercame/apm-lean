# Blueprint for m99J06

## Triage and repair

**Verdict: the canonical statement is unfaithful.** Since commit `dec7377d8`, part (d) asserts only convergence of a subsequence, whereas `problem.md` asks that the full Galerkin sequence converge weakly. The stronger statement is true.

Let `u` be the unique weak solution furnished by Riesz representation. Galerkin orthogonality and discrete uniqueness give

```text
(uSeq n : H) = (V n).starProjection u.
```

The adjacent inclusions imply `Monotone V`, while density of `⋃ n, V n` implies that the topological closure of `⨆ n, V n` is `⊤`. Mathlib's checked theorem `Submodule.starProjection_tendsto_self` therefore gives convergence to `u` in norm. Composing with the continuous identity into `toWeakSpace` gives full-sequence weak convergence. No compactness or subsequence argument is needed.

`RevisedMain.lean` changes only part (d): the subsequence and `StrictMono` quantifiers disappear, leaving `∃u`, weak convergence of `uSeq n`, and the weak-solution property. The existing `L²`-quotient repair for weak derivatives remains necessary and unchanged.

Degenerate checks: if `H` is trivial, all projections and solutions are zero. If `f=0`, uniqueness makes the full sequence constantly zero. Repeated nested subspaces are harmless; density forces eventual approximation even if some stages repeat. Zero subspaces cannot form a dense family unless `H` is trivial.

## Reused completed work

The file retains compiled proofs for the `H¹₀` model's zero/additive/scalar closure, integrability of inner-product components, uniqueness of represented elements, and uniqueness of Galerkin solutions. The wrappers deriving finite-dimensional existence and ambient weak-solution existence from the shared Riesz lemma are also proved without `sorry`.

## Remaining lemmas

### `apm_m99J06_weak_iff_strong`

The weak variational equation is equivalent to an `L²` second derivative satisfying `u-u''=f` almost everywhere. Strong-to-weak is integration by parts using absolute continuity and zero traces. Weak-to-strong tests against compactly supported smooth functions and applies the one-dimensional characterization of weak derivatives by absolutely continuous representatives. **Estimate:** 230–300 lines. **Dependencies:** compiled model algebra. **Check:** `f=u=0`; for smooth endpoint-zero functions, ordinary integration by parts gives the encoded sign.

### `apm_m99J06_riesz_on_complete_submodule`

For any complete submodule `V`, the forcing functional has a unique Riesz representative satisfying the Galerkin equation. Use the compiled additivity/scalar infrastructure to bundle

```text
v ↦ ∫ f * M.val v
```

as a continuous linear functional, bounded by Hölder and the `M.inner_eq` energy norm, then apply real Hilbert-space Riesz representation. This single shared lemma supplies both the finite-dimensional Galerkin solutions and the ambient weak solution (`V=⊤`), avoiding duplicate functional construction. **Estimate:** 150–240 lines. **Dependencies:** compiled model algebra and component integrability. **Check:** on a one-dimensional subspace it produces `ℓ(e)e`; on the zero subspace it produces zero.

### `apm_m99J06_galerkin_norm_le`

Every discrete solution satisfies `‖uₙ‖≤‖f‖₂`. Test with itself, apply Hölder, and use `M.inner_eq` to bound the `L²` norm of its value component by its Hilbert norm; divide in the nonzero case. **Estimate:** 70–130 lines. **Dependencies:** compiled integrability lemmas only. **Check:** the zero solution is immediate; equality is possible when the derivative energy vanishes.

### `apm_m99J06_galerkin_eq_starProjection`

If `u` is the ambient weak solution and `uV` solves the Galerkin equation in finite-dimensional `V`, then its ambient value equals `V.starProjection u`. For every `v∈V`, subtract the weak and Galerkin equations to obtain `⟪u-uV,v⟫=0`; use the characterization of orthogonal projection. **Estimate:** 50–90 lines. **Dependencies:** no unfinished analytic lemma; only the two equation hypotheses and Mathlib projection API. **Check:** for `V=⊥`, both sides are zero; if `u∈V`, both sides are `u`.

### `apm_m99J06_starProjection_convergence`

For nested finite-dimensional subspaces with dense union, any sequence equal to the corresponding projections of `u` converges to `u` both in norm and weakly. Derive `Monotone V` by induction from `hnested`, convert `hdense` to `⊤ ≤ (⨆n,V n).topologicalClosure`, and apply the checked theorem `Submodule.starProjection_tendsto_self`. Norm convergence implies weak convergence through the continuous map `toWeakSpaceCLM`. **Estimate:** 70–120 lines. **Dependencies:** projection identity is supplied as an explicit hypothesis, so this seat is independent of the preceding proof. **Check:** a constant family `V n=⊤` gives the constant sequence `u`; repeated stages do not affect the monotone-limit theorem.

## Dependency layers

- **Layer 1, parallel:** weak/strong equivalence, shared Riesz bridge, Galerkin norm bound, projection characterization, and abstract projection convergence.
- **Layer 2, already proved wrappers:** finite-dimensional existence and ambient weak-solution existence use the shared Riesz bridge.
- **Layer 3, already proved assembly:** identify every `uSeq n` with the projection of the one weak solution, apply full-sequence convergence, and return its weak limit. The main theorem has no direct `sorry`.

## Compilation and axioms

Both `RevisedMain.lean` and `Blueprint.lean` compile under the prescribed memory scope. The final output is:

```text
'apm_m99j06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The five warnings correspond exactly to the five remaining lemmas above.

## Doubt

No mathematical doubt remains about full-sequence convergence. The largest formal task is still the custom Sobolev weak/strong bridge; the projection route itself is directly supported by current Mathlib.
