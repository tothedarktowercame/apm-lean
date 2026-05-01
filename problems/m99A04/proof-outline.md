# Proof Outline: m99A04

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:problem-id 'm99A04
 :frame-id 'apm-v2-m99A04-1775007855572
 :goal "Extend a uniformly continuous map f : A → Y, where A is dense in the complete metric space X and Y is complete, to a unique continuous F : X → Y."
 :terms [{:name "dense-approximation sequence"
          :meaning "For every x ∈ X choose (a_n) ⊆ A with a_n → x."
          :needed-because "This lets us define the candidate extension by limits of points already in the domain."}
         {:name "uniformly-continuous ⇒ Cauchy control"
          :meaning "Uniform continuity sends Cauchy sequences in A to Cauchy sequences in Y."
          :needed-because "Ensures the limit lim f(a_n) exists in Y (which is complete) and is independent of the approximating sequence."}
         {:name "unique extension via density"
          :meaning "If two continuous maps on X agree on the dense subset A, they agree everywhere."
          :needed-because "Delivers uniqueness once the continuous extension has been defined."}]
 :strategy [{:id :s1
             :formal-dependency "metric completion lemmas for dense subsets and uniform continuity"
             :informal-dependency "Stage 1 discussion: define F(x)=lim f(a_n) and check well-definedness + continuity"
             :why-this-now "One construction handles existence, continuity, and uniqueness simultaneously, so structuring the Lean target around it avoids duplicated limit arguments."
             :lean-target "ApmCanaries.Frames.M99A04.Apm_v2_m99A04_1775007855572.extend_uniformContinuous_dense"
             :mathlib-status "Mathlib already contains `UniformContinuous.extend` for dense embeddings; reuse that API if possible."}]
 :stage-status {:stage1 :done
                :stage2 :done
                :stage3 :done
                :stage4 :done}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id 'm99A04'
  :frame-id 'apm-v2-m99A04-1775007855572'
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the reader-facing explanation (why hard/key insight/full proof/what connects) in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Populated execute.md with the lemma dependency graph linked to the dense-extension strategy."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-completed
  :summary "Implemented `extend_uniformContinuous_dense` in Main.lean, ran `lake build`, and recorded external warnings."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage4-completed
  :summary "Back-ported the Lean insights (use of `Dense.extend`, domain completeness irrelevance) into the informal write-up."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** Students usually remember that continuous maps on dense subsets extend, but they forget which hypotheses keep the limit well-defined: you need uniform control to make the image of any Cauchy sequence Cauchy, and you need completeness of the codomain to ensure convergence. Without that clarity the proof devolves into juggling epsilons for every single point of \(X\), and it is easy to lose track of where density and completeness enter.

**Key insight.** Fix \(x\in X\). Because \(A\) is dense we can choose a sequence \((a_n)\subseteq A\) with \(a_n\to x\). Uniform continuity of \(f\) guarantees \((f(a_n))\) is Cauchy, hence convergent in \(Y\) (which is complete). Define \(F(x)\) to be this limit. The uniform modulus makes the limit independent of the chosen sequence, and every continuity/uniqueness check boils down to comparing two approximating sequences inside \(A\).

**Complete proof.**  
Let \(x\in X\). Since \(A\) is dense, there exists a sequence \((a_n)\subseteq A\) with \(a_n\to x\). Uniform continuity means: for any \(\varepsilon>0\) there is \(\delta>0\) such that \(d_Y(f(a),f(b))<\varepsilon\) whenever \(d_X(a,b)<\delta\). Because \(a_n\to x\) is Cauchy, we can pick \(N\) so that for \(m,n\ge N\) both \(d_X(a_m, x)\) and \(d_X(a_n, x)\) are \(<\delta/2\); then \(d_X(a_m,a_n)<\delta\) and consequently \(d_Y(f(a_m),f(a_n))<\varepsilon\). Thus \((f(a_n))\) is a Cauchy sequence in \(Y\), hence convergent (here we use completeness of \(Y\)). Define \(F(x):=\lim_{n\to\infty}f(a_n)\).

To see that \(F(x)\) is independent of the sequence chosen, let \((b_n)\subseteq A\) be another sequence converging to \(x\). Interleave the two sequences: \(c_{2n}=a_n\), \(c_{2n+1}=b_n\). The same uniform-continuity argument shows \(f(c_n)\) is Cauchy, hence both subsequences \((f(a_n))\) and \((f(b_n))\) converge to the same limit. Therefore \(F\) is well defined.

The defining property also shows that \(F\) extends \(f\): if \(x\in A\), take the constant sequence \(a_n=x\). Then \(F(x)=\lim f(x)=f(x)\). Continuity of \(F\) follows by chasing sequences: pick \(x_k\to x\) in \(X\) and approximate each \(x_k\) by a sequence in \(A\); a diagonal argument shows \(F(x_k)\to F(x)\). Equivalently, given \(\varepsilon>0\), choose \(\delta>0\) from uniform continuity and use the same Cauchy estimate to control \(d_Y(F(x),F(y))\) whenever \(d_X(x,y)<\delta\).

For uniqueness, suppose \(G:X\to Y\) is continuous and agrees with \(f\) on \(A\). Let \(x\in X\) and choose \(a_n\in A\) with \(a_n\to x\). Then
\[
G(x)=\lim_{n\to\infty}G(a_n)=\lim_{n\to\infty}f(a_n)=F(x),
\]
where the first equality uses continuity of \(G\) and the second uses the agreement on \(A\). Hence \(G=F\). (Notably, the completeness of \(X\) never entered the argument; the hypothesis is harmless but unnecessary.)

**What connects.** This construction is the metric-space avatar of extending uniformly continuous maps along dense embeddings, a staple in approximation theory, completion theory, and the Stone–Weierstrass toolkit. The “approximate by a sequence, use uniform continuity to push limits” manoeuvre also appears when defining the Bochner integral, extending isometries, or proving that isometries between dense subsets of Banach spaces extend uniquely.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- `:s1 (dense approximation + uniform Cauchy control)` — supplies the limit definition of \(F(x)\) and shows it is well defined; formally this is `Dense.extend`, which packages the “choose sequences in the dense set” trick.
- `:s2 (continuity + uniform continuity of the extension)` — uses the previous limit control to prove \(F\) is continuous and extends \(f\), matching the lemmas `Dense.uniformContinuous_extend` and `Dense.extend_of_ind`.
- `:s3 (uniqueness-on-dense-set)` — a standard density argument (`Dense.extend_unique`) showing that a continuous map agreeing with \(f\) on \(A\) must coincide with \(F`.

**PROOF-PLAN.EDN**

The machine-readable plan lives at:
/home/joe/code/futon6/.state/proof-frames/m99A04/apm-v2-m99A04-1775007855572/proof-plan.edn

The formal/informal alignment artifact lives at:
/home/joe/code/futon6/.state/proof-frames/m99A04/apm-v2-m99A04-1775007855572/formal-alignment.edn

**Stage 3 — LEAN FORMALIZATION**

- Implemented `extend_uniformContinuous_dense` in `/home/joe/code/apm-lean/ApmCanaries/Frames/M99A04/Apm_v2_m99A04_1775007855572/Main.lean`.  
- The proof is a thin wrapper around mathlib’s `Dense.extend` API: we instantiate it with the dense inclusion `A ↪ X`, obtain the uniformly continuous extension, record its continuity, and invoke `Dense.extend_unique` for uniqueness.  
- `lake build` succeeds; the only warnings come from pre-existing files `ApmCanaries/C2Analysis.lean` and `ApmCanaries/C4Functional.lean` (unused variables/section vars), exactly as noted in earlier frames.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean proof highlighted that we never actually need completeness of \(X\); the density hypothesis already produces the approximating nets, and all the heavy lifting sits in `Dense.extend`. Translating back to prose, I emphasized the “interleaving sequences” argument for well-definedness (mirroring `Dense.extend_of_ind`) and the density-based uniqueness argument (mirroring `Dense.extend_unique`). The formal result also makes continuity automatic via uniform continuity ⇒ continuity, so the informal proof now references the same modulus-of-continuity reasoning instead of re-deriving a bespoke epsilon–delta estimate.
