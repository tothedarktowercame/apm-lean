import Mathlib

open Filter Topology

namespace t00J02_ModelProduct

/-- **S4 (abstract).**  A locally determined, unique, `±1`-valued label on the regular parameters of a
circle, with regular parameters arbitrarily close to every point, is globally constant. -/
theorem side_label_global (Q : Circle → ℤ → Prop) (reg : Circle → Prop)
    (huniq : ∀ t l₁ l₂, Q t l₁ → Q t l₂ → l₁ = l₂)
    (hpm : ∀ t l, Q t l → l = 1 ∨ l = -1)
    (hloc : ∀ t, ∃ l, ∀ᶠ t' in 𝓝 t, reg t' → Q t' l)
    (hfreq : ∀ t, ∃ᶠ t' in 𝓝 t, reg t') :
    ∃ l, (l = 1 ∨ l = -1) ∧ ∀ t, reg t → Q t l := by
  let A : ℤ → Set Circle := fun l => {t | ∀ᶠ t' in 𝓝 t, reg t' → Q t' l}
  have hAopen : ∀ l, IsOpen (A l) := by
    intro l
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact ht.eventually_nhds
  have hwit : ∀ t l, t ∈ A l → ∃ t', reg t' ∧ Q t' l := by
    intro t l ht
    obtain ⟨t', hr, hq⟩ := ((hfreq t).and_eventually ht).exists
    exact ⟨t', hr, hq hr⟩
  have hcover : ∀ t, t ∈ A 1 ∨ t ∈ A (-1) := by
    intro t
    obtain ⟨l, hl⟩ := hloc t
    obtain ⟨t', -, hq⟩ := hwit t l hl
    rcases hpm t' l hq with rfl | rfl
    · exact Or.inl hl
    · exact Or.inr hl
  have hdisj : ∀ t, t ∈ A 1 → t ∈ A (-1) → False := by
    intro t h1 h2
    have : ∀ᶠ t' in 𝓝 t, reg t' → Q t' 1 ∧ Q t' (-1) := by
      filter_upwards [h1, h2] with t' a b using fun hr => ⟨a hr, b hr⟩
    obtain ⟨t', hr, hq⟩ := ((hfreq t).and_eventually this).exists
    have := huniq t' 1 (-1) (hq hr).1 (hq hr).2
    norm_num at this
  have hcompl : (A 1)ᶜ = A (-1) := by
    ext t
    constructor
    · intro h; exact (hcover t).resolve_left h
    · intro h h1; exact hdisj t h1 h
  have hclopen : IsClopen (A 1) :=
    ⟨by rw [← isOpen_compl_iff, hcompl]; exact hAopen _, hAopen _⟩
  have hreg_of : ∀ l, A l = Set.univ → ∀ t, reg t → Q t l := by
    intro l hl t hr
    have ht : t ∈ A l := hl ▸ Set.mem_univ t
    exact ht.self_of_nhds hr
  have hsurj : Function.Surjective Circle.exp :=
    fun z => ⟨Complex.arg (z : ℂ), Circle.exp_arg z⟩
  haveI : ConnectedSpace Circle := hsurj.connectedSpace Circle.exp.continuous
  rcases isClopen_iff.mp hclopen with h | h
  · refine ⟨-1, Or.inr rfl, hreg_of _ ?_⟩
    rw [← hcompl, h, Set.compl_empty]
  · exact ⟨1, Or.inl rfl, hreg_of _ h⟩

end t00J02_ModelProduct
