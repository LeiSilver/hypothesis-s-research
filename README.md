# Li–Liu spectral Hypothesis S

This repository contains the English research manuscript and the code and data for its finite-modulus certificates. Hypothesis S remains open.

- [Manuscript (PDF)](output/pdf/hypothesis_s_paper.pdf)
- [LaTeX source](output/pdf/hypothesis_s_paper.tex)
- [Lean verification of the trapezoidal endpoint term](formalization/PrimorialModel.lean)
- [Lean verification of the pair-height symmetry](formalization/PairHeightSymmetry.lean)
- [Lean verification of the finite zero-concentration inequalities](formalization/ZeroConcentration.lean)
- [Lean verification of the bin bound for short zero gaps](formalization/ZeroGapBins.lean)
- [Lean verification of the local conductor partition](formalization/ConductorInclusionExclusion.lean)
- [Lean verification of the finite conductor moment identities](formalization/ConductorMoments.lean)
- [Lean verification of macroscopic congruence line isolation](formalization/MacroscopicLines.lean)
- [Lean verification of the product cutoff geometry](formalization/CriticalCollar.lean)
- [Lean verification of the prefix rectangle test](formalization/CriticalPrefix.lean)
- [Lean verification of the signed progression rows](formalization/CriticalArithmetic.lean)

## Research checkpoint · 26 November 2026

Theorem 10.13 computes the deterministic covariance correction for moduli divisible by the primorial up to $y$ with $\log N=O(y)$. The correction is multiplication by a function of the integrated Buchstab function throughout every fixed log-power window. For every fixed power threshold there are primorial packets beyond it where deleting this correction incurs an error of order the singular series.

Theorem 10.14 gives the covariance formula with error $O((\log N)^{-D})$ for supports beginning at $N(\log N)^{A_D}$ outside $O_K(Y(\log Y)^{-K})$ even moduli in $[Y,2Y]$ under Dirichlet GRH. The support exponent $A_D$ is independent of $K$.

Under Dirichlet GRH, Theorem 10.12 lowers the support threshold for the zero covariance formula to $N\exp(A_D(\log\log N)^2/\log\log\log N)$, with operator error $O((\log N)^{-D})$. It gives a mixed microscopic estimate across the transition and, under Hypothesis S, the sine-kernel gap law in shrinking height windows with $H\log N\to\infty$.

Theorem 10.11 bounds the mean square of the zero count in a window of radius $c_0/(K\log N)$ in terms of the high-support covariance norm. A mean square of central-zero multiplicities bounded below by a positive constant forces $\|T_N\|\gg\log N$. Under Hypothesis S the proportion of odd characters with vanishing central value is $O(1/\log\log N)$.

Theorem 10.8 bounds the proportion of odd characters with large conductor loss. With $L=\log N$, the proportion with $\log(N/q_\chi)>A(\log L)^2/\log\log L$ is at most $L^{-A+o(1)}$, with a matching exponent on primorial moduli. Under Dirichlet GRH, their contribution to the full normalized operator norm is $O_{A,\epsilon}(L^{2-A+\epsilon})$.

Theorem 10.9 gives a two-way criterion for the high-support covariance. It suffices to retain odd characters with full conductor exponent at every prime factor above $(\log N)^\rho$, for fixed $0<\rho<1$. Both directions use only nearby even divisors of $N$ and have bounded comparison constants.

Theorem 10.10 bounds the normalized short-gap part of the centered covariance by $O((1+u)L e^{-H/L})$ with a smooth product cutoff beyond $xy=e^H$, for gaps at most $u/L$ and $L=\log N$. This is a pointwise estimate at each even modulus under Dirichlet GRH. The same-label correction also has its own bound when the log supports are separated by less than $2\log N$ by the margin specified in the manuscript.

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
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/PrimorialModel.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/PairHeightSymmetry.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/ZeroConcentration.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/ZeroGapBins.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/ConductorInclusionExclusion.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/ConductorMoments.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/MacroscopicLines.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/CriticalCollar.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/CriticalPrefix.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/CriticalArithmetic.lean
```

The Lean modules cover the trapezoidal endpoint term, pair-height symmetry, the finite zero-concentration inequalities, the zero-gap bin bound, the conductor partition and finite moment identity, congruence line geometry, prefix identities, and the prime-power threshold. Their axiom audits use only `propext`, `Classical.choice` and `Quot.sound`. The manuscript supplies the analytic proofs of the sieve and operator estimates.

The manuscript's reproducibility section lists the commands for the finite certificates. The scripts and rational witness data are at the repository root. The manuscript acknowledges assistance from OpenAI Codex.
