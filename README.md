# Li–Liu spectral Hypothesis S

This repository contains the English research manuscript and the code and data for its finite-modulus certificates. Hypothesis S remains open.

- [Manuscript (PDF)](output/pdf/hypothesis_s_paper.pdf)
- [LaTeX source](output/pdf/hypothesis_s_paper.tex)
- [Lean verification of the short-divisor residue injection and screening period](formalization/ShortTypeIResidues.lean)
- [Lean verification of the common sampling period and conductor cofactor](formalization/ConductorPairSampling.lean)
- [Lean verification of the Farey arc determinant and neighbor congruences](formalization/FareyArcPartition.lean)
- [Lean verification of the reduced slope denominator and cofactor divisibility](formalization/ReducedSlopeModulus.lean)
- [Lean verification of the factorization and residue-class rule for periodic modulus weights](formalization/PeriodicModulus.lean)
- [Lean verification of residue translations and the common denominator divisor](formalization/AdditivePairOrder.lean)
- [Lean verification of the additive frequency denominator and cofactor](formalization/AdditiveDenominator.lean)
- [Lean verification of the complementary divisor cutoff and sign](formalization/ComplementaryDivisor.lean)
- [Lean verification of the determinant divisibility in the Type II form](formalization/TypeIIDeterminant.lean)
- [Lean verification of the signed progression roots and slope reflection](formalization/SignedProgressionLocal.lean)
- [Lean verification of the product variation in a grid cell](formalization/ProductGridCell.lean)
- [Lean verification of the prime-exponent injection for the divisor moment](formalization/DivisorMoment.lean)
- [Lean verification of the dyadic interval boundary count](formalization/DyadicIntervalBoundary.lean)
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

Theorem 13.22 evaluates the retained arc coefficients at their rational centers and replaces the larger prime weights by screened Vaughan Type II terms, with power-saving squared error under Dirichlet GRH. The construction preserves the large-conductor, square-divisor, character-power and conductor-pair restrictions. The cutoff $UW\le P Y^{-\zeta}$ permits $W=1$ and Möbius divisors $d>P Y^{-\zeta}$, with complementary factors $m\ll (V/P)Y^\zeta$. The remaining second moment is a finite conductor-pair sum with these explicit bilinear coefficients.

Theorem 13.20 evaluates the full-circle modulus pairing as a short sum of the product character. Under Dirichlet GRH it removes individual characters whose prescribed fixed powers have conductor at most $Y^{1/2+\xi/2}$, with squared error $O(Y^{3-\xi/16})$. The corresponding powers of every surviving product character have conductor exceeding $Y^{1+\xi/2}$. Proposition 13.21 constructs arbitrary functions on the retained prime-denominator arcs that satisfy the energy and pointwise bounds yet give a surviving second moment $\gg_\epsilon Y^{3-\epsilon}$ for each fixed $\epsilon>0$. The construction shows that a power saving needs further information about the actual prime coefficients.

Theorem 13.18 discards conductors whose largest square divisor is at least $Y^{\xi/4}$, with squared error $O(Y^{3-\xi/16})$ in the prime-prefix counts. For each remaining approximation denominator $q$, the product of primes that divide $q$ exactly once and divide the conductor accounts for all but a factor less than $Y^{7\xi/8}$. Proposition 13.19 uses the adjacent Farey fractions to describe the least-denominator arc assignment and expands the assigned prime coefficients into complete twisted Kloosterman sums. The induced Gauss factor vanishes unless the inducing cofactor is squarefree and coprime to the conductor. The surviving second moment still requires cancellation between different conductors.

Theorem 13.17 uses GRH short character sums and the wider spacing of reduced fractions whose denominators share a divisor. For $X\le Y^{1/2-\eta}$ it retains only primitive conductors $c>Q_*Y^{-\xi/4}$ with $Q_*=\lceil V/P\rceil$, and a squared error $O(Y^{3-\xi/8})$. In the second moment the pairs with $(c,c')\ge Y^{\xi/4}$ contribute the same error in signed sum. The pairs with $|c-c'|\le Y^{1+3\xi/4}$ enjoy the bound in absolute sum. Every surviving product of primitive characters has conductor $\gg Y^{2+\xi}$.

Theorem 13.16 regroups the residual terms by primitive inducing character before applying the dual multiplicative large sieve. This removes every conductor $c\le Y^{1-\xi/4}$ and every term with $d(k/c)\ge Y^{5\xi/8}$ from the expansion of Theorem 13.15. The squared error for the original count is $O(Y^{3-\xi/16})$, and the previous power saving for nearby denominator pairs persists.

Theorem 13.15 sums over approximation denominators before estimating the second moment. Under Dirichlet GRH the entire principal-character contribution, all denominators $q\le Y^{1+\xi/4}$ and the nonprincipal terms with small effective character sums can be removed with squared error $O(Y^{3-\xi/4})$ for $X\le Y^{\xi/8}$. Among the remaining denominator pairs, those with gaps at most $Y^{1-\xi/2}$ have total absolute contribution $O(Y^{3-\xi/4})$.

Theorem 13.14 groups the retained larger-prime frequencies by approximation denominator $q$. Pólya–Vinogradov and character orthogonality bound the nonprincipal terms. On disjoint low-denominator arcs, Dirichlet GRH bounds the remaining principal terms by cancellation between the two opposite prime classes. The sum of the absolute interactions on any set of denominator pairs with row and column degrees $O(Y^{\xi/2})$ is $O(Y^{3-\xi/4})$. This deletes all equal and nearby denominators, as well as pairs with $\max(q,q')/(q,q')\le Y^{\xi/4}$. The bound is uniform on measurable subsets of the modulus Fourier variable, so it applies inside the simultaneous cutoff of Theorem 13.13.

Theorem 13.13 applies Prachar's short-interval variance to the larger-prime Fourier sum. Sampling on the lines $h=bN$ then permits deletion of the rational arcs of denominators up to $P=Y^{1-\xi}/X$, with squared error $O(Y^{3-\xi})$ under Dirichlet GRH. Opposite slope residues cancel the Ramanujan main terms. On the small-input grid this combines with Theorem 13.12 to leave a second-moment integral restricted in both the modulus and larger-prime Fourier variables. After smoothing in the modulus, the kernel is restricted to $\|2(\alpha-b\theta)\|\le Y^{-1+2s}$ for small fixed $s>0$, with a power-saving error.

Theorem 13.12 uses the GRH form of the Assing–Blomer–Li progression estimate to bound the signed prefix sum over all even moduli against any bounded periodic weight of period at most $Y^\kappa$, with an absolute $\kappa>0$. The bound is $O(Y^{2-\kappa})$ on every subinterval of $[Y,2Y]$ for smaller input $X\le Y^\kappa$ at the critical product scale. Parseval then places the second moment on the complement of narrow arcs about the rationals with denominator at most $Y^{\kappa/4}$ in the modulus Fourier variable, with error $O(Y^{3-3\kappa/4})$.

Theorem 13.11 removes pairs of large-denominator frequencies whose sum or difference has reduced denominator at most $Y/(XH(\log Y)^{D+2M+10})$, with $M=D+6$ and $H=\sqrt X(\log Y)^{(2D+13)/2}$. The removed pairs contribute $O(Y^3(\log Y)^{-D})$ in absolute value on the moduli with $\tau(N)\le(\log Y)^M$. The original second moment on the other moduli has the same error bound. On the prime-prefix grid the four retained denominators have a common divisor of size at least $N/(\log Y)^{C_2}$ for fixed $C_2$. The remaining correlations still require cancellation.

The Dirichlet GRH input is the Alpöge–Claude theorem. The manuscript cites the independent verification of the original proof and the checks of the shorter Lean proof released on 25 November.

Theorem 13.10 gives the long Möbius replacement uniformly for every subset of additive frequency denominators $q\mid N$, with squared error $O(Y^3(\log Y)^{-D})$ over the even moduli. Under Dirichlet GRH one may retain only $q>N/H$ with $H=\sqrt X(\log Y)^{(D+9)/2}$. On the prime-prefix grid the cofactors $N/q$ are consequently bounded by a fixed power of $\log Y$. The remaining high-denominator projection still requires cancellation.

Theorem 13.9 permits cutoffs $UW\le B/H$ in the small-input second moment, with $B=V/Y$ and $H=\exp(A(\log\log Y)^2/\log\log\log Y)$. With $W=1$ and $U=\lfloor B/H\rfloor$, each retained factorization carries the weight $\mu(d)\log m$ with $d>B/H$ and $m\ll YH$. The coprimality conditions persist and the modulus for the two distinguished divisors exceeds $(B/H)^2$. The mean-square replacement and the discarded terms cost $O(Y^3(\log Y)^{-D})$ for any fixed $D$ with the stated choice of screening and cutoffs. A wider subpower loss gives a pointwise replacement at every modulus. These estimates are unconditional.

Theorem 13.8 replaces both larger prime weights in the second moment of the signed prefix counts by screened Vaughan Type II weights. For $X\le Y^{1/2-\eta}$ each expanded value has two factors above $\lfloor (V/Y)^{1/2-\kappa}\rfloor$. The four factors across the pair may be required to be pairwise coprime and coprime to the slopes, smaller primes, modulus, and the determinant of the two linear forms. The single-count replacement has a uniform power saving at every modulus. The discarded terms in the second moment cost $O(Y^3(\log Y)^{-D})$ for any fixed $D$ with the stated screening. These estimates are unconditional.

Theorem 13.7 expands the second moment of the signed prime prefix counts over all even moduli in $[Y,2Y]$ into prime-pair discrepancies for two linear forms. The local-density main terms cancel after summing over one slope. The unconditional error is $O_{C,Q,\eta}(Y^{3-\eta/100})$ uniformly over the prefix endpoints for $X\le Y^{1-\eta}$ and $Y^2/Q\le XV\le CY^2$. Cancellation of the signed prime-pair discrepancies would give decay in density through fixed critical caps.

Theorem 13.6 characterizes decay in density through all fixed critical product caps using $O(\log\log N)$ prime prefix counts per modulus at fixed precision. These signed counts use ordinary primes on both sides and have no product cutoff inside a prefix rectangle. The smaller variable ranges between a slowly growing lower bound and a fixed power of $\log N$. Lemma 13.5 gives the upper-support mean square with explicit dependence on the lower support threshold and allows a different product cap for each modulus. Cancellation of the remaining prefix counts is open.

Theorem 11.6 bounds the sum of squared normalized operator norms on supports $x,y\le N(\log N)^B$, over even $N\in[Y,2Y]$, by $O_B(Y^{1/2}(\log Y)^{A_B})$ under Dirichlet GRH. The estimate controls the supremum over moving tests. It follows from the mean square of maximal interval discrepancies on the sum and difference lines. The same theorem gives exponent $1/2+3\eta/2+\varepsilon$ on supports up to $N^{1+\eta}$ and exponent $1+\gamma-\delta/2+\varepsilon$ for the sharp product cap $xy\le CN^{2+\gamma}$ on supports $x,y\ge N^\delta$.

Theorem 9.13 removes rational arcs at the scale of the smaller variable using only one screened Type II weight. Under Dirichlet GRH the power-saving estimate holds on packets with smaller scale $X\ge N^{1/2+\eta}$. For denominators up to $P=(\log N)^K$, the arcs of radius $P/(qX)$ can be removed on packets with $X\ge \sqrt N(\log N)^{3K+2D+10}$ with an $O((\log N)^{-D})$ operator error. The other packets use the larger-scale arcs of Theorem 9.11. The new estimate uses the full progression variance and a translated dyadic interval decomposition.

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
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/ShortTypeIResidues.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/ConductorPairSampling.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/FareyArcPartition.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/ReducedSlopeModulus.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/PeriodicModulus.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/AdditivePairOrder.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/AdditiveDenominator.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/ComplementaryDivisor.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/TypeIIDeterminant.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/SignedProgressionLocal.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/ProductGridCell.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/DivisorMoment.lean
elan run leanprover/lean4:v4.35.0 lean -DwarningAsError=true formalization/DyadicIntervalBoundary.lean
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
