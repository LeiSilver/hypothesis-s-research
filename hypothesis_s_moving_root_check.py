"""Compare the weights in Proposition 13.37 as exact exponentiated rationals."""

from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import isqrt, prod


def divisor_weight(primes):
    """Exponentiate the defining sum of mu(d) log(n/d) over d > sqrt(n)."""
    n = prod(primes)
    ratio = Fraction(1)
    for size in range(1, len(primes) + 1):
        for factors in combinations(primes, size):
            d = prod(factors)
            if d * d > n:
                ratio *= Fraction(n // d) ** ((-1) ** size)
    return ratio


def formula_weight(primes):
    n = prod(primes)
    if len(primes) == 1:
        return 1
    if len(primes) == 2:
        return Fraction(1, primes[0])
    if len(primes) == 3:
        a, b, c = primes
        return n if c < a * b else 1
    if len(primes) == 4:
        a, b, c, e = primes
        return min(a * a, Fraction(a * b * c, e))
    if len(primes) == 5:
        return Fraction(1, n**3)
    raise ValueError("expected one to five distinct primes")


def main():
    primes = [p for p in range(2, 72) if all(p % d for d in range(2, isqrt(p) + 1))]
    checked = Counter()
    branches = set()
    for size in range(1, 6):
        for factors in combinations(primes, size):
            # The endpoint screen implies n <= w^6 < P^-(n)^6.
            if prod(factors) >= factors[0] ** 6:
                continue
            actual = divisor_weight(factors)
            expected = formula_weight(factors)
            if actual != expected:
                raise AssertionError((factors, actual, expected))
            checked[size] += 1
            if size == 3:
                a, b, c = factors
                branches.add((size, c < a * b))
            if size == 4:
                a, b, c, e = factors
                branches.add((size, a * e < b * c))
    if branches != {(3, True), (3, False), (4, True), (4, False)}:
        raise AssertionError("missing a three- or four-prime case")
    print("Checked weights by number of prime factors:", dict(checked))


if __name__ == "__main__":
    main()
