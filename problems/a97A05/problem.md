# Problem a97A05

## Source

Origin: `apm/a97A05.tex` (UT Austin prelim corpus).

Provenance: produced by `apm-daily-batch.md` on 20260502 via claude-1.
Raw batch trace: `futon3c/data/apm-informal-proofs/apm-a97A05.md`.

## Statement

```
Let $H=\{z\in \C\}\pipe \Im(z)>0\}$, and let $f:H\rightarrow \C$ be
analytic. Suppose that the map defined by $z\mapsto \Re(f(z))$ is
bounded on $H$. Prove that $f(z)=g(z)/h(z)$, where $g$ and $h$ are
both analytic and bounded on $H$. Hint: consider
$\varphi(z)=(af(z)+b)/(cf(z)+d)$, and recall that the map defined by
$z\mapsto (az+b)/(cz+d)$ takes the half-plane $\{z\in \C\pipe
\Re(z)>0\}$ onto the open unit disk. 
```

See `informal-solution.md` for the worked solution and
`proof-outline.md` for the Lean formalization plan.
