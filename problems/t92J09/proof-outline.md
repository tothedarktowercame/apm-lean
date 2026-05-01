# Proof Outline: t92J09

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:problem-id 't92J09
 :frame-id 'apm-v2-t92J09-1775009066645
 :goal "Compute ∫_{S^2} i^*(x dy∧dz) using Stokes’ theorem and the standard orientation."
 :terms [{:name "2-form ω = x dy∧dz"
          :meaning "The differential 2-form whose value on vectors is x times the oriented area element in the y–z plane."
          :needed-because "We must understand its exterior derivative when applying Stokes."
         }
         {:name "exterior derivative"
          :meaning "Operator d sending k-forms to (k+1)-forms (here dω = dx∧dy∧dz)."
          :needed-because "Stokes equates ∫_{∂B^3} ω with ∫_{B^3} dω."
         }
         {:name "orientation and Stokes’ theorem"
          :meaning "Oriented boundary of the unit ball matches the given orientation on S^2."
          :needed-because "Determines the sign of the integral when transferring from the sphere to the ball."}]
 :strategy [{:id :s1
             :formal-dependency "Stokes’ theorem, computation of dω, volume of unit ball"
             :informal-dependency "Apply Stokes: ∫_{S^2} i^*ω = ∫_{B^3} dω.  Compute dω = dx∧dy∧dz, the standard volume form.  Integrate over the unit ball to get its volume 4π/3."
             :why-this-now "Direct evaluation is painful; Stokes gives the result immediately via volume."
             :lean-target "ApmCanaries.Frames.T92J09.Apm_v2_t92J09_1775009066645.integral_form_on_sphere"
             :mathlib-status "Mathlib has Stokes’ theorem and the known volume of the unit ball in ℝ^3; we will assemble them."}]
 :stage-status {:stage1 :done
                :stage2 :done
                :stage3 :in-progress
                :stage4 :pending}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 't92J09'
  :frame-id 'apm-v2-t92J09-1775009066645'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full reader-facing solution (why hard, key insight, proof, connections) using Stokes’ theorem."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Documented the Stokes → dω → volume dependency chain in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-completed
  :summary "Added the Lean lemma `integral_form_on_sphere` (volume of the unit ball) and ran `lake build`."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage4-completed
  :summary "Explained how the Lean computation isolates the analytic heart of the Stokes argument."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.**  Directly integrating a 2-form over a sphere usually means introducing spherical coordinates, computing a pullback matrix, and watching signs.  That’s tedious and a common source of orientation mistakes.  The trap is forgetting that the unit sphere is the boundary of the unit ball: Stokes’ theorem turns the entire calculation into a volume integral, but only if you keep the induced orientation straight.

**Key insight.**  Take Stokes at face value: `∫_{S^2} i^*(ω) = ∫_{B^3} dω`.  The exterior derivative is trivial—`d(x dy∧dz) = dx∧dy∧dz`, the standard volume form.  So the problem collapses to “what is the volume of the unit ball in ℝ³?”, namely `4π/3`.

**Complete proof.**  The inclusion map `i : S^2 → ℝ^3` is the oriented boundary of the unit ball `B^3`.  Because ω is smooth, Stokes’ theorem gives
```
∫_{S^2} i^*(ω) = ∫_{B^3} dω.
```
Compute `dω`: since `ω = x dy∧dz`, we have `dω = dx∧dy∧dz` because `dx` is the only differential whose coefficient is nonconstant.  This 3-form is exactly the usual volume form on ℝ³.  Therefore `∫_{B^3} dω` equals the Euclidean volume of the unit 3-ball, which is `4π/3`.  Because the orientation on `S^2` is the outward normal orientation, no sign flips occur.  Hence `∫_{S^2} i^*(ω) = 4π/3`.

**What connects.**  This is the differential forms version of the divergence theorem: `ω = x dy∧dz` corresponds to the vector field `F = (x,0,0)` whose divergence is `1`.  The same idea powers flux computations, electrostatics via Gauss’ law, and any question where a surface integral becomes a volume integral.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Stokes’ theorem (boundary orientation).**  Converts the surface integral into a volume integral and fixes the sign.
- **Exterior derivative of a simple 2-form.**  Shows `dω = dx∧dy∧dz`, i.e., the standard volume form.
- **Volume of the unit ball.**  Provides the numerical evaluation `4π/3`.  These combine in the order: Stokes ⇒ compute `dω` ⇒ integrate the volume form.

**Stage 3 — LEAN FORMALIZATION**

- Added `integral_form_on_sphere` in `ApmCanaries/Frames/T92J09/Apm_v2_t92J09_1775009066645/Main.lean`.  The lemma proves `(volume (Metric.ball (0 : ℝ^3) 1)).toReal = (4/3)·π` using Mathlib’s `EuclideanSpace.volume_ball_fin_three`.
- Mathlib does not yet expose Stokes’ theorem for differential forms or surface integrals on spheres, so the Lean statement captures the right-hand side of the argument (the volume computation).  Tying it back to the boundary integral would require the missing Stokes infrastructure.
- Ran `lake build`; it finished successfully, with only unrelated existing warnings about other files.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean development forced me to isolate the only analytic ingredient we actually need—`volume(B^3) = 4π/3`.  This highlights that every other part of the paper proof is purely formal (Stokes + computing `dω`).  Once Mathlib gains Stokes for differential forms, the Lean lemma can serve as the final numerical step.
