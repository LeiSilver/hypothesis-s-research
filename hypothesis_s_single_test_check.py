"""Exact checks for the divisor identities in Propositions 3.8 and 3.9."""

from fractions import Fraction
from math import gcd, isqrt, lcm, prod


def factors(n):
    primes = []
    for p in range(2, isqrt(n) + 1):
        while n % p == 0:
            primes.append(p)
            n //= p
    if n > 1:
        primes.append(n)
    return primes


def main():
    limit = 256
    divisors = [tuple(d for d in range(1, n + 1) if n % d == 0)
                for n in range(limit + 1)]
    prime_factors = [factors(n) for n in range(limit + 1)]
    mu = [(-1) ** len(ps) if len(ps) == len(set(ps)) else 0 for ps in prime_factors]
    phi = [sum(gcd(i, n) == 1 for i in range(n)) for n in range(limit + 1)]

    splits = 0
    for n in range(2, limit + 1):
        bases = set(prime_factors[n])
        exp_lambda = next(iter(bases)) if len(bases) == 1 else 1
        for cutoff in range(2, 18):
            short = prod(Fraction(cutoff, d) ** mu[d] for d in divisors[n] if d <= cutoff)
            tail = prod(Fraction(cutoff, d) ** mu[d] for d in divisors[n] if d > cutoff)
            if short * tail != exp_lambda:
                raise AssertionError(("divisor split", n, cutoff))
            splits += 1

    pairs = unit_pairs = 0
    for n in range(2, 33, 2):
        ram = {q: sum(d * mu[q // d] for d in divisors[gcd(q, n)]) for q in range(1, 13)}
        for d in range(1, 13):
            # Mean of the divisor indicator with the prime coordinate uniform on units.
            mixed = sum(Fraction(mu[q] * ram[q], phi[q]) for q in divisors[d]) / d
            if mixed != Fraction(int(gcd(d, n) == 1), phi[d]):
                raise AssertionError(("unit average", n, d))
            for e in range(1, 13):
                period = lcm(d, e)
                residues = [m for m in range(period) if m % d == 0 and (n - m) % e == 0]
                predicted = Fraction(sum(ram[q] for q in divisors[gcd(d, e)]), d * e)
                if Fraction(len(residues), period) != predicted:
                    raise AssertionError(("periodic mean", n, d, e))
                pairs += 1
                if gcd(period, n) != 1:
                    continue
                full_period = lcm(n, period)
                units = sum(gcd(m, n) == 1 for r in residues for m in range(r, full_period, period))
                if Fraction(units, full_period) != predicted * Fraction(phi[n], n):
                    raise AssertionError(("coprime periodic mean", n, d, e))
                unit_pairs += 1
    print(f"Verified {splits} divisor splits, {pairs} periodic means and {unit_pairs} coprime means.")


if __name__ == "__main__":
    main()
