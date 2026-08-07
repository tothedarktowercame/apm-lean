import Mathlib

/-!
# APM t01A01

## Statement repairs

None.

## Encoding questions

The real projective plane is encoded as the actual projectivization of `ℝ³`
with quotient topology. Triviality of the induced fundamental-group map is
stated at every basepoint; its codomain is based at `f x`, as required for a
not-necessarily-basepoint-preserving map.
-/

open scoped LinearAlgebra.Projectivization

abbrev apm_t01A01_RP2 := Projectivization ℝ (Fin 3 → ℝ)

noncomputable instance : TopologicalSpace apm_t01A01_RP2 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ (Fin 3 → ℝ))))

/-- A nonsurjective continuous self-map factors continuously through the
complement of a point that it misses. -/
lemma apm_t01A01_factor_through_complement
    (f : C(apm_t01A01_RP2, apm_t01A01_RP2))
    (hnot_surj : ¬Function.Surjective f) :
    ∃ q : apm_t01A01_RP2,
      ∃ g : C(apm_t01A01_RP2, {y : apm_t01A01_RP2 // y ≠ q}),
        ∀ x, (g x : apm_t01A01_RP2) = f x := by
  obtain ⟨q, hq⟩ : ∃ q : apm_t01A01_RP2, ∀ x, f x ≠ q := by
    simpa [Function.Surjective] using hnot_surj
  refine ⟨q, ⟨fun x ↦ ⟨f x, hq x⟩, ?_⟩, ?_⟩
  · exact f.continuous.subtype_mk _
  · intro x
    rfl

/-- Null-homotopy of the complement-valued factor descends through the
inclusion to null-homotopy of the original map. -/
lemma apm_t01A01_nullhomotopic_of_factor
    (f : C(apm_t01A01_RP2, apm_t01A01_RP2))
    (q : apm_t01A01_RP2)
    (g : C(apm_t01A01_RP2, {y : apm_t01A01_RP2 // y ≠ q}))
    (hfg : ∀ x, (g x : apm_t01A01_RP2) = f x)
    (p : {y : apm_t01A01_RP2 // y ≠ q})
    (hg : ContinuousMap.Homotopic g (ContinuousMap.const _ p)) :
    ContinuousMap.Homotopic f
      (ContinuousMap.const apm_t01A01_RP2 (p : apm_t01A01_RP2)) := by
  let inclusion : C({y : apm_t01A01_RP2 // y ≠ q}, apm_t01A01_RP2) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have hcomp := ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.refl inclusion) hg
  have hleft : inclusion.comp g = f := by
    ext x
    exact hfg x
  simpa [hleft, inclusion] using hcomp

theorem apm_t01a01 :
    ∀ f : C(apm_t01A01_RP2, apm_t01A01_RP2),
      ¬Function.Surjective f →
      (∀ (x : apm_t01A01_RP2) (γ : FundamentalGroup apm_t01A01_RP2 x),
        FundamentalGroup.map f x γ = 1) ∧
      ∃ p : apm_t01A01_RP2,
        ContinuousMap.Homotopic f (ContinuousMap.const _ p) := by
  intro f hnot_surj
  have hfactor := apm_t01A01_factor_through_complement f hnot_surj
  /-
  Boundary (closer hop 2): factorization through the complement of a missed point is proved
  above. Completing the frozen theorem requires the specific topology of real
  projective space: `RP² \ {q}` deformation retracts to `RP¹ ≃ S¹`,
  `π₁(RP²) ≃ ZMod 2`, and the circle's universal-cover lifting criterion.
  I searched Mathlib's `Projectivization`, `FundamentalGroup`, homotopy,
  covering-map lifting, sphere/circle, and quotient APIs. None of those
  projective-space computations or the punctured-plane deformation retraction
  is available, so the factorization cannot presently be converted into the
  two requested conclusions without a substantial new topology development.
  The partial siblings `t00J07` and `t92J05` confirm that the required `RP²`
  fundamental-group and cell-attachment computations are not packaged; the
  wedge-cover sibling `t98A03` is blocked by the same quotient-space gap. No
  relevant bridge occurs in `ConstructionTargets/` or `YoungL2.lean`.

  Closer hop 1 additionally searched `LEMMA-INDEX.md` and all fully closed
  artifacts for projectivization/fundamental-group lemmas. The only new
  Mathlib neighbor found was `OnePoint.equivProjectivization`, which treats
  the projective line rather than the projective plane and supplies no
  punctured-plane retraction. Git history contains only the statement-bank
  commit and the two earlier partial passes. The proved elementary bridge has
  now been extracted as `apm_t01A01_factor_through_complement`; the remaining
  proof hole is confined to the unavailable RP² topology computation.

  This hop additionally proves `apm_t01A01_nullhomotopic_of_factor`: a
  null-homotopy of the complement-valued factor composes with the subtype
  inclusion to give exactly the frozen null-homotopy conclusion for `f`.
  Thus no further continuous-map composition or endpoint transport remains
  after the punctured-RP² factor has been contracted.

  Closer hop 3 inspected Mathlib's lower-level homotopy-invariance machinery.
  `FundamentalGroupoidFunctor.homotopicMapsNatIso` does give a natural
  isomorphism between the functors induced by homotopic maps, and hence offers
  a route from the eventual null-homotopy to the first (fundamental-group)
  conjunct.  Its components change basepoints by conjugation, so this is not a
  direct rewriting lemma for the frozen `FundamentalGroup.map`; nevertheless a
  constant map has trivial image and conjugation preserves the identity.  This
  sharpens the dependency graph but does not produce the missing null-homotopy.
  Renewed searches of `FundamentalGroupoid/InducedMaps.lean`, the projective-
  space sources, `LEMMA-INDEX.md`, the closed corpus, and git history still
  found no contraction of `RP² \ {q}`, no `RP²` fundamental-group computation,
  and no covering-space lifting theorem specialized enough to construct it.
  The frozen theorem therefore remains honestly open at that topology bridge.
  -/
  sorry
