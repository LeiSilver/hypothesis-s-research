# Li–Liu spectral Hypothesis S

This repository contains the English research manuscript and the code and data for its finite-modulus certificates. Hypothesis S remains open.

- [Manuscript (PDF)](output/pdf/hypothesis_s_paper.pdf)
- [LaTeX source](output/pdf/hypothesis_s_paper.tex)
- [Lean verification of the finite conductor moment identities](formalization/ConductorMoments.lean)
- [Lean verification of macroscopic congruence line isolation](formalization/MacroscopicLines.lean)
- [Lean verification of the product cutoff geometry](formalization/CriticalCollar.lean)
- [Lean verification of the prefix rectangle test](formalization/CriticalPrefix.lean)
- [Lean verification of the signed progression rows](formalization/CriticalArithmetic.lean)

## Research checkpoint · 26 November 2026

Theorem 10.8 bounds the proportion of odd characters with large conductor loss. With $L=\log N$, the proportion with $\log(N/q_\chi)>A(\log L)^2/\log\log L$ is at most $L^{-A+o(1)}$, with a matching exponent on primorial moduli. Under Dirichlet GRH, their contribution to the full normalized operator norm is $O_{A,\epsilon}(L^{2-A+\epsilon})$.

Theorem 3.2 gives a quantitative equivalence between norm decay on each fixed window $x,y<RN$ and vanishing Hardy–Littlewood discrepancies on its individual sum and difference lines. In particular, Hypothesis S would imply the expected asymptotic for prime pairs $(p,p+N)$ with $aN<p<bN$, for fixed $0<a<b$ and all even $N$ tending to infinity.

The manuscript cites the [Alpöge–Claude Lean proof announcement](https://alpo.ge/remark.pdf) and independent [MIT](https://math.mit.edu/~drew/grh/) and [Waterloo](https://mrubinst.github.io/grh-lean-verification/) verification records. The verified Dirichlet GRH statements cover the zero-location inputs used here.

Theorem 9.2 shows that, for any fixed $C\ge 1$, decay of the norm with the sharp product cutoff $xy\le CN^2$ is equivalent to uniform decay of signed rectangle counting discrepancies. The equivalence is unconditional for the physical arithmetic form. Under modulus-specific GRH, if $E_N$ is the full norm divided by the singular series, the sharp restriction has normalized norm $O_C(E_N^{1/3}+N^{-c})$. The improvement uses a linear upper-collar bound at fixed $C$.

Theorem 9.3 reduces this discrepancy to $O(\log N)$ prefix rectangle counts at fixed precision. Its signed continuous-model estimate allows all but a bounded number of the counts to use only the arithmetic measure, with a controlled error.

Theorem 13.2 proves unconditionally that proper prime powers contribute a vanishing mean-square norm through a fixed cap $xy\le CN^2$ across all even moduli. At a single modulus, the large proper powers have a uniform tail bound. The remaining proper-power contribution is governed by fixed opposite-residue prime counts.

A proof of Hypothesis S still needs uniform cancellation in the counts near $xy\asymp N^2$ and control of the full operator across the larger retained product range.

## Reproducibility

With Elan installed, run the Lean check from the repository root.

```sh
elan toolchain install leanprover/lean4:v4.35.0
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/ConductorMoments.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/MacroscopicLines.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/CriticalCollar.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/CriticalPrefix.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/CriticalArithmetic.lean
```

The Lean modules cover the finite moment identity and product support bound, isolation of individual congruence lines, vertex exclusion and line widths, the four-prefix inclusion–exclusion bound, the counts of dyadic index pairs, and the congruence branches and reduced prime-power threshold. Their axiom audits use only `propext`, `Classical.choice` and `Quot.sound`. The manuscript supplies the analytic proofs of the sieve and operator estimates.

The manuscript's reproducibility section lists the commands for the finite certificates. The scripts and rational witness data are at the repository root. The manuscript acknowledges assistance from OpenAI Codex.
