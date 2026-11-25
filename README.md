# Li–Liu spectral Hypothesis S

This repository contains the English research manuscript and the code and data for its finite-modulus certificates. Hypothesis S remains open.

- [Manuscript (PDF)](output/pdf/hypothesis_s_paper.pdf)
- [LaTeX source](output/pdf/hypothesis_s_paper.tex)
- [Lean verification of the product cutoff geometry](formalization/CriticalCollar.lean)

## Research checkpoint · 26 November 2026

Theorem 9.2 shows that, for any fixed $C\ge 1$, decay of the norm with the sharp product cutoff $xy\le CN^2$ is equivalent to uniform decay of signed rectangle counting discrepancies. The equivalence is unconditional for the physical arithmetic form. Under modulus-specific GRH, if $E_N$ is the full norm divided by the singular series, the sharp restriction has normalized norm $O_C(E_N^{1/3}+N^{-c})$. The improvement uses a linear upper-collar bound at fixed $C$.

A proof of Hypothesis S still needs uniform cancellation in the counts near $xy\asymp N^2$ and control of the full operator across the larger retained product range.

## Reproducibility

With Elan installed, run the Lean check from the repository root.

```sh
elan toolchain install leanprover/lean4:v4.35.0
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/CriticalCollar.lean
```

The Lean module covers vertex exclusion and width bounds on the reflection and difference lines. Its axiom audit lists only `propext`, `Classical.choice` and `Quot.sound`. The manuscript supplies the analytic proofs of the sieve and operator estimates.

The manuscript's reproducibility section lists the commands for the finite certificates. The scripts and rational witness data are at the repository root. The manuscript acknowledges assistance from OpenAI Codex.
