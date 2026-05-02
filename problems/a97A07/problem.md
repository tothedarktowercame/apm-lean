# Problem a97A07

## Source

Origin: `apm/a97A07.tex` (UT Austin prelim corpus).

Provenance: produced by `apm-daily-batch.md` on 20260502 via claude-1.
Raw batch trace: `futon3c/data/apm-informal-proofs/apm-a97A07.md`.

## Statement

```
Let $z_1,\ldots ,z_n$ be distinct complex numbers situated in the
interior of a Jordan curve $\gamma$, and let $p$ be the polynomial
$p(z)=\prod_{k=1}^n(z-z_k)$. Let $f$ be analytic inside and on the
curve $\gamma$. Prove that the function $P:\C\rightarrow \C$ defined
by $P(z)=(1/2\pi
i)\int_{\gamma}(f(\zeta)/p(\zeta))((p(\zeta)-p(z))/(\zeta-z))d\zeta$
is a polynomial of degree $n-1$ and that $P(z_k)=f(z_k)$ for all
$k=1,\ldots ,n$.
```

See `informal-solution.md` for the worked solution and
`proof-outline.md` for the Lean formalization plan.
