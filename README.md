# Li–Liu spectral Hypothesis S

This repository contains the English research manuscript and the code and data for its finite-modulus certificates. Hypothesis S remains open.

- [Manuscript (PDF)](output/pdf/hypothesis_s_paper.pdf)
- [LaTeX source](output/pdf/hypothesis_s_paper.tex)
- [Lean verification of the clipped Fourier line and its sampling period](formalization/CriticalFourierWindow.lean)
- [Lean verification of the local progression density cases](formalization/ProgressionLocalDensity.lean)
- [Lean verification of the truncated inclusion-exclusion bound](formalization/TruncatedInclusionExclusion.lean)
- [Lean verification of coprime factors of squarefree values](formalization/SquarefreeFactors.lean)
- [Lean verification of signed residue counts in complete and incomplete blocks](formalization/ResidueBlocks.lean)
- [Lean verification of the finite prefix estimate](formalization/PrefixPersistence.lean)
- [Lean verification of the centered product collar](formalization/CenteredProduct.lean)
- [Lean verification of the finite Euler-factor residue calculation](formalization/EulerOrthogonality.lean)
- [Lean verification of the divisor-grid cutoff and endpoints](formalization/DivisorGrid.lean)
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

Theorem 9.11 removes small-denominator rational arcs from the screened Type II forms through every fixed product cap $xy\le CN^2$. Under Dirichlet GRH the normalized operator error saves a power of $N$ uniformly over the even moduli. With one Type II weight, the deleted arcs have radius $P/(qY)$ for $q\le P=N^\lambda$, where $Y$ is the larger packet scale. With both weights replaced on supports $x,y\ge N^{1/2+\eta}$, the deleted arcs have radius $P/(qX)$, where $X$ is the smaller scale. The complementary integrals still require cancellation.

Theorem 9.9 replaces both von Mangoldt weights by screened Type II weights through $xy\le CN^2$ on supports $x,y\ge N^{1/2+\eta}$ for any fixed $\eta>0$ in the stated range. Under Dirichlet GRH the normalized operator error saves a power of $N$ uniformly over the even moduli. The proof samples Prachar's short-interval mean-square bound at the congruence-line centers and computes the matching Type I density, including nonunit residue classes.

Theorems 9.7 and 9.8 restrict the Type II approximation through each fixed critical product cap to squarefree expanded values with no prime factor at most $(\log N)^B$, for any fixed $B>0$. The two factors are consequently squarefree and coprime. Under Dirichlet GRH the discarded contributions have a power-saving normalized operator bound uniformly over the even moduli. Theorem 9.7 also bounds the Type II contribution restricted by any individual nontrivial square divisor.

Theorems 9.5 and 9.6 give a Type II approximation to the full critical product restriction $xy\le CN^2$. On separated inputs the Type I terms cancel by the difference of two residue counts. On the remaining packets Dirichlet GRH gives a Type I main term equal to the continuous singular-series model, with a uniform power-saving error in the normalized operator norm. For any fixed $0<\theta<1/6$, the resulting form retains only Type II weights with both factors exceeding $\lfloor N^\theta\rfloor$ in the expanded coordinate.

Theorem 13.4 gives an unconditional mean-square estimate for each bounded smaller input range, averaged over all even moduli. Up to $xy\le C_0N^2(\log Y)^B$ for $N\in[Y,2Y]$, the average squared normalized norm is $O((\log Y)^{B-2+\varepsilon})$. The same estimate holds for the progression correction to the identical zero labels. The proof converts the first-moment progression estimate of Bombieri, Friedlander and Iwaniec into a maximal estimate for the signed prefixes.

Theorem 9.4 approximates the critical product form on $x\le A\le N/8$ by sampling the larger test at $bN$ and keeping the signed weight $\Lambda(bN+n)-\Lambda(bN-n)$. The normalized operator error is $O_C(A/N+N^{-c})$ through $xy\le CN^2$. The larger values can be restricted to primes. Decay through every fixed critical cap is equivalent to decay of the individual macroscopic line discrepancies together with a limit of these centered norms on separated inputs.

Theorem 10.16 replaces the full contribution above a tapered product threshold $xy=e^H$ by bounded-height, separated zero pairs. The normalized operator error is $O(e^{-H/L}(L(1+u)+L^2/\sqrt T))$, where $L=\log N$, the retained ordinates have height at most $T$, and their gaps exceed $u/L$. This applies even when one physical input stays bounded. A character-orthogonality estimate controls the imprimitive Euler correction uniformly.

Theorem 10.15 gives a covariance formula for every even modulus on supports $x,y\ge N^\delta$ for any fixed $\delta>0$. Its explicit center uses partial sums of the singular-series divisor coefficients. For each fixed $D>0$ the error, normalized by the singular series, is $O_{\delta,D}((\log N)^{-D})$ in operator norm. The approximation to the continuous model uses no zero-location theorem. The covariance formula uses Dirichlet GRH.

Theorem 10.13 computes the deterministic covariance correction for moduli divisible by the primorial up to $y$ with $\log N=O(y)$. The correction is multiplication by a function of the integrated Buchstab function throughout every fixed log-power window. For every fixed power threshold there are primorial packets beyond it where deleting this correction incurs an error of order the singular series.

Theorem 10.14 gives the covariance formula with error $O((\log N)^{-D})$ for supports beginning at $N(\log N)^{A_D}$ outside $O_K(Y(\log Y)^{-K})$ even moduli in $[Y,2Y]$ under Dirichlet GRH. The support exponent $A_D$ is independent of $K$.

Under Dirichlet GRH, Theorem 10.12 lowers the support threshold for the zero covariance formula to $N\exp(A_D(\log\log N)^2/\log\log\log N)$, with operator error $O((\log N)^{-D})$. It gives a mixed microscopic estimate across the transition and, under Hypothesis S, the sine-kernel gap law in shrinking height windows with $H\log N\to\infty$.

Theorem 10.11 bounds the mean square of the zero count in a window of radius $c_0/(K\log N)$ in terms of the high-support covariance norm. A mean square of central-zero multiplicities bounded below by a positive constant forces $\|T_N\|\gg\log N$. Under Hypothesis S the proportion of odd characters with vanishing central value is $O(1/\log\log N)$.

Theorem 10.8 bounds the proportion of odd characters with large conductor loss. With $L=\log N$, the proportion with $\log(N/q_\chi)>A(\log L)^2/\log\log L$ is at most $L^{-A+o(1)}$, with a matching exponent on primorial moduli. Under Dirichlet GRH, their contribution to the full normalized operator norm is $O_{A,\epsilon}(L^{2-A+\epsilon})$.

Theorem 10.9 gives a two-way criterion for the high-support covariance. It suffices to retain odd characters with full conductor exponent at every prime factor above $(\log N)^\rho$, for fixed $0<\rho<1$. Both directions use only nearby even divisors of $N$ and have bounded comparison constants.

Theorem 10.10 bounds the normalized short-gap part of the centered covariance by $O((1+u)L e^{-H/L})$ with a smooth product cutoff beyond $xy=e^H$, for gaps at most $u/L$ and $L=\log N$. This is a pointwise estimate at each even modulus under Dirichlet GRH. The same-label correction also has its own bound when the log supports are separated by less than $2\log N$ by the margin specified in the manuscript.

Theorem 3.2 gives a quantitative equivalence between norm decay on each fixed window $x,y<RN$ and vanishing Hardy–Littlewood discrepancies on its individual sum and difference lines. In particular, Hypothesis S would imply the expected asymptotic for prime pairs $(p,p+N)$ with $aN<p<bN$, for fixed $0<a<b$ and all even $N$ tending to infinity.

We use the Alpöge–Claude Dirichlet GRH theorem for the zero-location inputs in the manuscript. The independent verification records include theorem-statement checks and kernel replays. [Proof announcement](https://alpo.ge/remark.pdf) · [MIT verification](https://math.mit.edu/~drew/grh/) · [Waterloo verification](https://mrubinst.github.io/grh-lean-verification/)

Theorem 9.2 shows that, for any fixed $C\ge 1$, decay of the norm with the sharp product cutoff $xy\le CN^2$ is equivalent to uniform decay of signed rectangle counting discrepancies. The equivalence is unconditional for the physical arithmetic form. Under modulus-specific GRH, if $E_N$ is the full norm divided by the singular series, the sharp restriction has normalized norm $O_C(E_N^{1/3}+N^{-c})$. The improvement uses a linear upper-collar bound at fixed $C$.

Theorem 9.3 reduces this discrepancy to $O(\log N)$ prefix rectangle counts at fixed precision. Its signed continuous-model estimate allows all but a bounded number of the counts to use only the arithmetic measure, with a controlled error.

Theorem 13.2 proves unconditionally that proper prime powers contribute a vanishing mean-square norm through a fixed cap $xy\le CN^2$ across all even moduli. At a single modulus, the large proper powers have a uniform tail bound. The remaining proper-power contribution is governed by fixed opposite-residue prime counts.

A proof of Hypothesis S still needs uniform cancellation in the counts near $xy\asymp N^2$ and control of the full operator across the larger retained product range.

## Reproducibility

With Elan installed, run the Lean check from the repository root.

```sh
elan toolchain install leanprover/lean4:v4.35.0
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/CriticalFourierWindow.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/ProgressionLocalDensity.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/TruncatedInclusionExclusion.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/SquarefreeFactors.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/ResidueBlocks.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/PrefixPersistence.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/CenteredProduct.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/EulerOrthogonality.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/DivisorGrid.lean
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
