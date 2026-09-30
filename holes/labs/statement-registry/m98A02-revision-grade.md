# Fidelity grade — m98A02 proposed revision (`[Nontrivial X]` on part (b))

Grader: read-only. Nothing was built, run, edited, staged or committed apart from this file. Files read: `problems/m98A02/problem.md`, `problem.tex`, `informal-solution.md`, `problems/m98A02/lean/Main.lean` (bank), `holes/labs/solve-loop/revisions/m98A02/Main.lean` (proposed), `holes/labs/solve-loop/refutations/m98A02/{Refute.lean,REFUTATION.md}`, `holes/labs/solve-loop/revisions/README.md`. I did not compile anything. The refutation is a four-line `Subsingleton.elim` argument, and I checked it by reading.

| id | grade | one-line reason | repair classification | prelim-defect? |
|---|---|---|---|---|
| m98A02 | narrower (only the restriction the prelim needs to be true) | The only statement change is `[Nontrivial X]` on the part (b) conjunct. This excludes exactly X = {0}, where the printed lower bound is false. Otherwise (b) matches the prelim, with the X → X specialization that `I − A` forces. Part (a) is unchanged, but its "B(X,Y) is Banach" conjunct is weak (see note 4) | correction (the bank statement is false, as Refute.lean shows; the repair makes it true and adds nothing beyond X ≠ {0}) | yes: on X = {0}, I − A = 0 is invertible with inverse 0, so ‖(I−A)⁻¹‖ = 0 < 1 = 1/(1+‖A‖). The prelim as printed is false unless X ≠ {0} |

## Evidence note

**1. Statement diff.** `diff problems/m98A02/lean/Main.lean holes/labs/solve-loop/revisions/m98A02/Main.lean`: the only change inside the `theorem apm_m98a02 :` statement is line 28 → 25.
```
<     (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
>     (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X]
```
The other hunks are header docstring text, removal of the helper lemma `apm_m98a02_trivial_space_obstruction`, and replacement of the `sorry` proof body. Parts (a)(i) and (a)(ii) and the whole body of (b) (`∃ B, B ∘ (I−A) = I ∧ (I−A) ∘ B = I ∧ 1/(1+‖A‖) ≤ ‖B‖ ∧ ‖B‖ ≤ 1/(1−‖A‖)`) are identical in the two files.

**2. Prelim defect.** Take X = {0}. It is a Banach space, and A = 0 has ‖A‖ = 0 < 1. Then I − A = 0 = I is invertible with (I−A)⁻¹ = 0, whose norm is 0. The printed bound says 1/(1+0) = 1 ≤ 0, which is false. The informal solution's lower-bound step is `1 = ‖I‖ ≤ ‖(I−A)⁻¹‖‖I−A‖` (informal-solution.md l.86), and `‖I‖ = 1` holds only when X ≠ {0}. The upper bound and invertibility still hold on {0}. So the prelim needs the unstated nondegeneracy assumption X ≠ {0}. The bank encoding reproduced this defect faithfully, and `Refute.lean` (`hneumann (Fin 0 → ℝ) 0`, `B = 0` by `Subsingleton.elim`, `1 ≤ 0`) certifies it for the whole conjunction. `[Nontrivial X]` is exactly X ≠ {0} and excludes nothing else, so it is the smallest repair. The printed (b) is false, so the repair is a correction, not a scope choice.

**3. Part (b) encoding otherwise.**
- The X → X specialization (`(A : X →L[ℝ] X)`) is forced. `I − A` with `I : X → X` makes sense only when the codomain is X. The header docstring states this.
- "Invertible" is encoded as a two-sided inverse in `X →L[ℝ] X` (the inverse `B` must be bounded). That is at least as strong as bijectivity, and the two are equivalent on Banach spaces by the open mapping theorem. It is also the reading the prelim uses, since it takes ‖(I−A)⁻¹‖. Two-sided inverses are unique, so ‖B‖ is ‖(I−A)⁻¹‖.
- `‖A‖` is Mathlib's operator norm, which is ‖A‖_{B(X,Y)}.

**4. Differences in part (a).** These are unchanged by the revision but do not quite say what problem.md says.
- Boundedness equivalence:
  ```
  (∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : X →ₗ[ℝ] Y),
    (∃ C ≥ 0, ∀ x, ‖A x‖ ≤ C * ‖x‖) ↔ Continuous A)
  ```
  This is faithful, and slightly more general because completeness is not assumed, which is harmless. The "define bounded" part is supplied inline as `∃ C ≥ 0, ‖A x‖ ≤ C‖x‖`, which is the standard definition.
- B(X,Y) is Banach:
  ```
  (∀ (X Y : Type*) ... [CompleteSpace Y],
    Nonempty (CompleteSpace (X →L[ℝ] Y)))
  ```
  This is weaker than the prelim in substance. The type `X →L[ℝ] Y` already carries Mathlib's operator-norm `NormedSpace` structure and a `CompleteSpace` instance, so the conjunct is closed by `⟨inferInstance⟩` (as both files do). The library supplies the content: the norm axioms and the Cauchy-limit argument. The conjunct does not tie `X →L[ℝ] Y` to the set defined by the ∃C predicate. That link follows from conjunct (a)(i), but it is not stated. Grade for this conjunct taken alone: hypothesis-carries-core (library instance). It does not change the verdict on the revision, which leaves it untouched.
- Scalars are fixed to ℝ. The prelim leaves the field unspecified, and ℂ is equally standard. This is a mild narrowing of the kind the registry usually accepts.

**5. Proposer's README claim.** The claim is "a defect in problem.md itself, and the narrower statement is the intended one". I agree, with the reasoning in note 2. I did not check the README's compile claim ("compiles with the full proof"), because building was out of scope. The proof body reads as a standard `isUnit_one_sub_of_norm_lt_one` / `NormedRing.inverse_one_sub` argument, and its lower-bound step uses `norm_one`, which is where `[Nontrivial X]` is used.
