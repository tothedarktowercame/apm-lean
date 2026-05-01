# Informal Solution: t96J08

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Why it’s hard.** Students often try to guess a potential for ω or integrate directly on the hemisphere, but here ω is *not* closed, so there is no primitive, and parametrizing the curved surface is painful. The trick is to observe that a 2-form in ℝ³ of the shape `x dy∧dz + y dx∧dz + z dx∧dy` is the flux form of a vector field, so classical divergence-theorem computations apply.

**Key insight.** Write ω as the interior product of the volume form with the vector field V=(x,−y,z). Then dω = (div V) dx∧dy∧dz = dx∧dy∧dz, so ω is neither closed nor exact. The integral of ω over S is the outward flux of V across S, which we evaluate by closing S with the flat disk and applying the divergence theorem.

**Complete proof.**
1. **Closed/exact?** Compute dω term-by-term. Since d(x dy∧dz)=dx∧dy∧dz, d(y dx∧dz)=dy∧dx∧dz=−dx∧dy∧dz, and d(z dx∧dy)=dz∧dx∧dy=dx∧dy∧dz, we get dω=dx∧dy∧dz≠0. Hence ω is not closed and therefore not exact.
2. **Flux form.** Note that ι_V(dx∧dy∧dz)=x dy∧dz + y dx∧dz + z dx∧dy precisely when V=(x,−y,z). Thus ∫_S ω = ∫_S ι_V(vol) equals the oriented flux of V through S.
3. **Divergence theorem.** Let E be the half-ball bounded by S together with the base disk D in the plane z=1. Since div V = ∂x/∂x + ∂(−y)/∂y + ∂z/∂z = 1−1+1=1, the flux through the closed surface S∪D is ∭_E 1 dV = Vol(E) = (1/2)(4π/3)=2π/3. The disk D, oriented downward to match the outward orientation, has unit normal −k, so V·(−k)=−z=−1 on D, and its flux is −Area(D)=−π. Therefore the flux through S is flux(S∪D)−flux(D)= (2π/3) − (−π)=5π/3.
4. This equals ∫_S ω with the specified orientation (outward normal at (0,0,2) paired with the tangent basis (1,0,0),(0,1,0)).

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Exterior derivative computation.** Shows dω=dx∧dy∧dz, so ω is neither closed nor exact.
- **Interior product interpretation.** Recognizes ω as the flux form of V=(x,−y,z) and reduces the surface integral to a vector-field flux.
- **Divergence theorem.** Converts the flux over the hemispherical cap into a volume integral minus the flux across the base disk, producing 5π/3.

**Stage 3 — LEAN FORMALIZATION**

Current Mathlib support for differential forms exists, but there is no surface-integration or divergence-theorem API for curved surfaces such as hemispheres. To formalize this problem we would need (i) a definition of ∫_S ι_V(vol) over smooth 2-surfaces, (ii) the divergence theorem relating that flux to ∭ div V, and (iii) an orientation interface for hemispheres. Without these, `/home/joe/code/apm-lean/ApmCanaries/Frames/T96J08/Apm_v2_t96J08_1775012649049/Main.lean` merely records a TODO comment.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once surface integrals and the divergence theorem are available in Mathlib, the formal proof will align with Stage 1: compute dω, identify ω with ι_V(vol), apply the divergence theorem to the half-ball, subtract the disk flux, and obtain 5π/3.
