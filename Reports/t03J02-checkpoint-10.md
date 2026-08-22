# t03J02 strategy checkpoint 10

```clojure
{:solver/strategy
 {:summary "The staleness audit is complete. The pinned Mathlib has neither topological Seifert--van Kampen nor singular Mayer--Vietoris; its similarly named APIs are categorical-colimit and sheaf-cohomology results. Contrary to the first-pass note, this pin also lacks HomotopyInvarianceTopCat, so the inherited local cylinder bridge remains live. The sphere-homology increment, singular subdivision, and excision are usable. The primary theorem has been tested to close directly from the two frozen bridges. A reproducible declaration-reachability command now computes the union of all three target closures. The remaining route separates a general open-cover Mayer--Vietoris trunk from the deeper shared geometric seam: arbitrary embedded circles in the torus must be promoted to collars/cofibrations so the closed EqvGen quotient can be compared with a homotopy pushout."
  :obligations
  ["Commit the reproducible union reachability syntax, driver, and runner."
   "Build the general singular Mayer--Vietoris short exact chain complex and homology exactness interface from subcomplexChains_isPushout."
   "Compute integral singular homology of Circle and Circle × Circle in the production ModuleCat encoding."
   "Compute the fundamental group of Circle and derive the based product computation for the torus."
   "Prove the embedded-circle collar/cofibration seam and compare the frozen EqvGen quotient with the associated homotopy pushout."
   "Build topological Seifert--van Kampen for that pushout and identify the result with the frozen two-commutator PresentedGroup."
   "Apply singular Mayer--Vietoris to the pushout, use both nullhomotopies to zero the attachment maps, and derive ranks 1, 4, 3 with higher vanishing."
   "Close both bridge co-targets and the primary theorem, then run frozen-statement, axiom, build, warning, reachability, and cleanliness gates."]
  :decomposition
  [{:obligation "Build the general singular Mayer--Vietoris short exact chain complex and homology exactness interface from subcomplexChains_isPushout."
    :decision :sequential
    :reason "The inherited pushout and all-degree subdivision comparison make this the smallest immediately compilable library increment; it fixes the interface consumed by the later geometric comparison."}
   {:obligation "Compute integral singular homology of Circle and Circle × Circle in the production ModuleCat encoding."
    :decision :sequential
    :reason "The torus computation depends on selecting the Mayer--Vietoris or product route exposed by the first increment and must use its exact interface."}
   {:obligation "Compute the fundamental group of Circle and derive the based product computation for the torus."
    :decision :delegate
    :reason "This is independent of singular homology and was audited separately; Mathlib supplies circleExp covering data and fundamental-groupoid product preservation but no circle computation."}
   {:obligation "Prove the embedded-circle collar/cofibration seam and compare the frozen EqvGen quotient with the associated homotopy pushout."
    :decision :sequential
    :reason "Both invariant layers depend on the same geometric comparison. The frozen summand images are closed, so an open-cover theorem alone cannot apply."}
   {:obligation "Build topological Seifert--van Kampen for that pushout and identify the result with the frozen two-commutator PresentedGroup."
    :decision :sequential
    :reason "This consumes the circle and torus group computations plus the geometric seam."}
   {:obligation "Apply singular Mayer--Vietoris to the pushout, use both nullhomotopies to zero the attachment maps, and derive ranks 1, 4, 3 with higher vanishing."
    :decision :sequential
    :reason "This consumes the general MV interface, torus homology, and the geometric seam."}]
  :next-plan "Commit this checkpoint alone, then commit the already-tested union reachability tooling. Next add the canonical short exact chain complex attached to a two-subcomplex union, expose its connecting morphism and exactness lemmas, compile it standalone, and rerun the union closure before starting torus-specific work."
  :reachability
  {:target "union(apm_t03j02, apm_t03J02_bridge_1, apm_t03J02_bridge_2)"
   :closure-command "bash scripts/t03J02-declaration-reachability.sh"
   :added
   [{:decl "DeclarationReachability.declarationReachabilityUnionStx"
     :module "Tools.DeclarationReachability"
     :reachable? false
     :serves "Commit the reproducible union reachability syntax, driver, and runner."}]
   :orphans
   [{:decl "DeclarationReachability.declarationReachabilityUnionStx"
     :module "Tools.DeclarationReachability"
     :disposition :retain
     :reason "Acceptance tooling is explicitly retained to make the mandated union closure reproducible; it is not imported by the mathematical target by design."}]}}}
```

Measured command output before this checkpoint: target-union closure 18,060
constants; the pre-existing target module has 13 reachable and 13 orphan
declarations. No mathematical declaration has yet been added in this episode.
The 13 target-module orphans predate the branch and therefore receive no
checkpoint disposition here.
