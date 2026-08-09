import Mathlib

/-! # APM t95J02: retractions of the Klein bottle onto its core circles

## Statement repairs

None.

## Encoding question

The standard square picture is encoded as the quotient of `ℝ × ℝ` generated
by vertical translation and a horizontal glide reflection. The two circles
are the images of the coordinate axes, bundled as subspaces of that concrete
quotient, and their inclusions are the corresponding continuous subtype maps.
-/

open CategoryTheory

noncomputable section

/-- Generating identifications `(x,y) ∼ (x+1,-y)` and
`(x,y) ∼ (x,y+1)` for the Klein bottle. -/
inductive t95J02KleinRel : (ℝ × ℝ) → (ℝ × ℝ) → Prop
  | glide (x y : ℝ) : t95J02KleinRel (x, y) (x + 1, -y)
  | vertical (x y : ℝ) : t95J02KleinRel (x, y) (x, y + 1)

def t95J02KleinBottleType :=
  Quotient (Relation.EqvGen.setoid t95J02KleinRel)

noncomputable instance : TopologicalSpace t95J02KleinBottleType :=
  TopologicalSpace.coinduced
    (fun p : ℝ × ℝ ↦ Quotient.mk (Relation.EqvGen.setoid t95J02KleinRel) p)
    inferInstance

def t95J02QuotientPoint (p : ℝ × ℝ) : t95J02KleinBottleType :=
  Quotient.mk _ p

/-- The vertical period holds as an equality in the concrete quotient. -/
lemma t95J02QuotientPoint_vertical (x y : ℝ) :
    t95J02QuotientPoint (x, y) = t95J02QuotientPoint (x, y + 1) := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _ (t95J02KleinRel.vertical x y))

/-- The glide reflection holds as an equality in the concrete quotient. -/
lemma t95J02QuotientPoint_glide (x y : ℝ) :
    t95J02QuotientPoint (x, y) = t95J02QuotientPoint (x + 1, -y) := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _ (t95J02KleinRel.glide x y))

/-- Applying the glide twice produces the horizontal period two in the
quotient.  This is the point-set shadow of squaring the horizontal generator
in the usual Klein-bottle presentation. -/
lemma t95J02QuotientPoint_glide_twice (x y : ℝ) :
    t95J02QuotientPoint (x, y) = t95J02QuotientPoint (x + 2, y) := by
  calc
    t95J02QuotientPoint (x, y) = t95J02QuotientPoint (x + 1, -y) :=
      t95J02QuotientPoint_glide x y
    _ = t95J02QuotientPoint (x + 2, y) := by
      convert t95J02QuotientPoint_glide (x + 1) (-y) using 1
      all_goals ring_nf

/-- A vertical translate is carried by the glide to the inverse vertical
translate.  This compiles the concrete endpoint identity underlying the
presentation relation `b a b⁻¹ = a⁻¹`; only its transport to loops or
homology remains unavailable. -/
lemma t95J02QuotientPoint_glide_vertical_inverse (x y : ℝ) :
    t95J02QuotientPoint (x, y + 1) =
      t95J02QuotientPoint (x + 1, -y - 1) := by
  convert t95J02QuotientPoint_glide x (y + 1) using 1
  all_goals ring_nf

def t95J02KleinBottle : TopCat := TopCat.of t95J02KleinBottleType

/-- The horizontal core circle in the standard quotient picture. -/
def t95J02CircleA : TopCat :=
  TopCat.of {z : t95J02KleinBottleType // ∃ x : ℝ, z = t95J02QuotientPoint (x, 0)}

/-- The vertical core circle in the standard quotient picture. -/
def t95J02CircleB : TopCat :=
  TopCat.of {z : t95J02KleinBottleType // ∃ y : ℝ, z = t95J02QuotientPoint (0, y)}

def t95J02InclusionA : t95J02CircleA ⟶ t95J02KleinBottle :=
  ⟨Subtype.val, continuous_subtype_val⟩

def t95J02InclusionB : t95J02CircleB ⟶ t95J02KleinBottle :=
  ⟨Subtype.val, continuous_subtype_val⟩

def HasT95J02Retraction {A X : TopCat} (i : A ⟶ X) : Prop :=
  ∃ r : X ⟶ A, i ≫ r = 𝟙 A

private def t95J02CollapseARaw (p : ℝ × ℝ) : t95J02CircleA :=
  ⟨t95J02QuotientPoint (p.1, 0), ⟨p.1, rfl⟩⟩

private lemma t95J02CollapseARaw_generator
    {p q : ℝ × ℝ} (h : t95J02KleinRel p q) :
    t95J02CollapseARaw p = t95J02CollapseARaw q := by
  cases h with
  | glide x y =>
      apply Subtype.ext
      change t95J02QuotientPoint (x, 0) = t95J02QuotientPoint (x + 1, 0)
      have hg : t95J02KleinRel (x, 0) (x + 1, 0) := by
        simpa using t95J02KleinRel.glide x 0
      exact Quotient.sound (Relation.EqvGen.rel _ _ hg)
  | vertical x y => rfl

private lemma t95J02CollapseARaw_eqvGen
    {p q : ℝ × ℝ} (h : Relation.EqvGen t95J02KleinRel p q) :
    t95J02CollapseARaw p = t95J02CollapseARaw q := by
  exact Relation.EqvGen.rec
    (fun _ _ hrel => t95J02CollapseARaw_generator hrel)
    (fun _ => rfl)
    (fun _ _ _ ih => ih.symm)
    (fun _ _ _ _ _ ih₁ ih₂ => ih₁.trans ih₂) h

private lemma t95J02CollapseARaw_continuous : Continuous t95J02CollapseARaw := by
  exact (continuous_coinduced_rng.comp
    (continuous_fst.prodMk continuous_const)).subtype_mk _

private def t95J02RetractionA : t95J02KleinBottle ⟶ t95J02CircleA :=
  ⟨Quotient.lift t95J02CollapseARaw
    (fun _ _ h => t95J02CollapseARaw_eqvGen h),
    t95J02CollapseARaw_continuous.quotient_lift _⟩

private lemma t95J02RetractionA_comp_inclusion :
    t95J02InclusionA ≫ t95J02RetractionA = 𝟙 t95J02CircleA := by
  ext z
  rcases z with ⟨z, ⟨x, rfl⟩⟩
  rfl

/-- Integral first singular homology, used only to state the missing invariant
without assuming a presentation for the quotient's fundamental group. -/
abbrev apm_t95J02_H1 (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def apm_t95J02_H1Map {X Y : TopCat} (f : X ⟶ Y) :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map f

/-- Why this unblocks `apm_t95j02`: this is the missing concrete invariant
calculation. It identifies a nonzero integral first-homology class of the
vertical core whose image in the Klein bottle vanishes (the class twice a
circle generator, since the vertical class has order two after abelianizing). -/
theorem apm_t95J02_bridge_vertical_H1_kernel :
    ∃ gamma : apm_t95J02_H1 t95J02CircleB,
      gamma ≠ 0 ∧
      apm_t95J02_H1Map t95J02InclusionB gamma = 0 := by
  sorry

/-- Why this unblocks `apm_t95j02`: functoriality makes the first-homology map
of any retract inclusion injective. Combined with
`apm_t95J02_bridge_vertical_H1_kernel`, this rules out a retraction onto the
vertical core without requiring any further quotient computation. -/
theorem apm_t95J02_bridge_retraction_injective
    (hret : HasT95J02Retraction t95J02InclusionB) :
    Function.Injective
      (apm_t95J02_H1Map t95J02InclusionB) := by
  sorry

theorem apm_t95j02 :
    HasT95J02Retraction t95J02InclusionA ∧
    ¬HasT95J02Retraction t95J02InclusionB := by
  constructor
  · exact ⟨t95J02RetractionA, t95J02RetractionA_comp_inclusion⟩
  · /-
    PARTIAL boundary (closer hop 1).

    New progress: the positive half is closed constructively.  The raw map
    `t95J02CollapseARaw (x,y) = [(x,0)]` respects both generating Klein-bottle
    identifications.  `t95J02CollapseARaw_eqvGen` extends this through the
    equivalence closure using `Relation.EqvGen.rec`; quotient continuity then
    follows from `Continuous.quotient_lift`.  The descended map
    `t95J02RetractionA` restricts definitionally to the identity on circle A.

    The negative half requires detecting that circle B represents the
    order-two class in the Klein bottle's abelianized fundamental group.  A
    retraction would split its induced map to `H₁(B) ≃ ℤ`, contradicting that
    torsion.  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, all closed
    artifacts, Mathlib's quotient/fundamental-group/singular-homology APIs,
    and git history found no computation of the fundamental group or integral
    first homology of this custom `Relation.EqvGen` quotient.  In particular,
    the quotient has not been related to a packaged mapping torus or CW
    complex, so the presentation `⟨a,b | bab⁻¹ = a⁻¹⟩` cannot yet be used by
    the formal proof.  The remaining bridge is precisely that invariant
    computation and identification of the B inclusion with its torsion
    generator.

    Closer hop 2 exposes the two defining quotient identities as public
    compiled lemmas `t95J02QuotientPoint_vertical` and
    `t95J02QuotientPoint_glide`. In particular the latter is the concrete
    point-set identification from which the inversion conjugacy relation must
    eventually be derived. These equalities do not themselves compute the
    induced loop or homology classes, so the invariant bridge remains open.

    Closer hop 3 compiles two derived presentation identities.
    `t95J02QuotientPoint_glide_twice` proves the horizontal period-two
    equality obtained by applying the glide twice, while
    `t95J02QuotientPoint_glide_vertical_inverse` proves directly that the
    glide carries a positive vertical translate to a negative translate.
    The latter is the concrete endpoint equality behind the inversion
    conjugacy relation. Searches of the quotient, mapping-torus,
    fundamental-group, and singular-homology APIs still found no mechanism
    transporting these endpoint equalities to the required loop or `H₁`
    calculation, so the no-retraction invariant remains open and the frozen
    statement is unchanged.
    -/
    sorry
