"""Exact finite checks for the divisor identities and cutoffs of the single test."""

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


def check_rough_pairs():
    moduli = [*range(48, 450, 2), 1802, 2336]
    factorizations = [factors(m) for m in range(max(moduli))]
    patterns = set()
    checked = 0
    for n in moduli:
        for numerator, denominator in [(5, 12), (9, 20), (1, 2)]:
            threshold = n**numerator
            for m in range(5*n//12 + 1, (7*n-1)//12 + 1):
                if gcd(m, n) != 1:
                    continue
                pair = [factorizations[m], factorizations[n-m]]
                if any(ps[0]**denominator <= threshold for ps in pair):
                    continue
                counts = [sum(p*p <= k for p in set(ps))
                          for k, ps in zip((m, n-m), pair)]
                primes = int(all(len(ps) == 1 for ps in pair))
                if primes - (1 - sum(counts)) != prod(counts):
                    raise AssertionError(("rough-pair correction", n, m, counts))
                patterns.add(tuple(counts))
                checked += 1
    if patterns != {(0, 0), (1, 0), (0, 1), (1, 1)}:
        raise AssertionError(("missing rough-pair case", patterns))

    levels = 0
    for n in range(48, 100, 2):
        band = [r for r in (11, 13, 17) if n % r]
        for h in (1, 2, 3, 5, 6, 10, 15, 30):
            local = prod(1 if n % p == 0 else 2 for p in factors(h))
            for r in band:
                for t in band:
                    if r == t:
                        continue
                    start = r * ((n * pow(r, -1, t)) % t)
                    hits = sum(m*(n-m) % h == 0
                               for m in range(start, start+r*t*h, r*t))
                    if hits != local:
                        raise AssertionError(("rough-pair sieve density", n, h, r, t))
                    levels += 1
    print(f"Verified {checked} rough-pair corrections and {levels} overlap sieve densities.")


def check_sifted_twists():
    # In the basis 1, v the primitive roots satisfy v*v = sign*v - 1.
    def twice_real_power(k, sign):
        a, b = 1, 0
        for _ in range(k):
            a, b = -b, a + sign*b
        return 2*a + sign*b

    samples = [(p, m) for p in range(29, 250) if len(factors(p)) == 1
               for m in range(25, 300, 2) if gcd(p, m) == 1 and 5*(p+m) < 12*p < 7*(p+m)]
    # The fourth power survives even the 6/25 cutoff at this scale.
    fourth_power = 101**4
    nearby_prime = next(p for p in range(fourth_power+2, fourth_power+1000, 2)
                        if len(factors(p)) == 1)
    samples.append((nearby_prime, fourth_power))
    for numerator, denominator in [(1, 5), (6, 25)]:
        classes = set()
        for p, m in samples:
            ps = factors(m)
            sifted = int(min(ps)**denominator > (p+m)**numerator)
            k = len(ps)
            sixth = sifted * twice_real_power(k, 1)
            rotated_cubic = sifted * twice_real_power(k-1, -1)
            prime = int(k == 1)
            if sifted + sixth != 2*prime - sifted*int(k == 3):
                raise AssertionError(("sixth-root minorant", p, m))
            if sifted + rotated_cubic != 3*(prime + sifted*int(k == 4)):
                raise AssertionError(("cubic projection", p, m))
            classes.add(k if sifted else 0)
        if classes != set(range(5)):
            raise AssertionError(("missing sifted factor count", classes))
    print(f"Verified both twist identities on {len(samples)} prime shifts at each of two cutoffs.")


def check_twist_divisors():
    # Coordinates in the basis (1, v), where v**2 = v - 1.
    roots = [(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]
    checked = local = 0
    limit = 360
    ps = [factors(n) for n in range(limit + 1)]
    for z in (3, 5, 7):
        for n in range(1, limit + 1):
            small = [p for p in ps[n] if p <= z]
            large = [p for p in ps[n] if p > z]
            exponent = 3*len(small) + len(large) + len(set(large))
            predicted = roots[exponent % 6] if len(set(small)) == len(small) else (0, 0)
            a = b = 0
            for d in range(1, n + 1):
                if n % d or len(ps[d]) != len(set(ps[d])):
                    continue
                partner = ps[n//d]
                if partner and partner[0] <= z:
                    continue
                x, y = roots[len(partner) % 6]
                sign = (-1)**len(ps[d])
                a, b = a + sign*x, b + sign*y
            if (a, b) != predicted:
                raise AssertionError(("Mobius twist", z, n))
            if len(ps[n]) == len(set(ps[n])):
                x, y = roots[-len(large) % 6]
                sign = (-1)**len(ps[n])
                if (a, b) != (sign*x, sign*y):
                    raise AssertionError(("squarefree phase", z, n))
            checked += 1
            if len(set(ps[n])) == 1 and large:
                p, j = large[0], len(large)
                phi = (n//p)*(p-1)
                for component, value in enumerate((a, b)):
                    x = roots[j % 6][component]
                    prev = roots[(j-1) % 6][component]
                    model = Fraction(x, n) - Fraction(prev, phi)
                    if Fraction(value, phi) - model != Fraction(x, n*(p-1)):
                        raise AssertionError(("large-prime Euler correction", z, n))
                local += 1
    print(f"Verified {checked} divisor coefficients and {local} local Euler corrections.")


def check_twist_profile():
    # Row k encloses c_k(i/mesh) in units of 1/scale. On each cell
    # bound the increasing numerator and the reciprocal separately.
    mesh, scale = 100_000, 2**54
    points = 5*mesh + 1
    lower = [scale if i >= mesh else 0 for i in range(points)]
    upper = lower.copy()
    probes = (438_440, 438_480, 500_000)
    values = {}
    for k in (2, 3, 4):
        lo, hi = [0]*points, [0]*points
        for i in range(k*mesh + 1, points):
            j = i - mesh
            lo[i] = lo[i-1] + lower[j-1]//j
            hi[i] = hi[i-1] + (upper[j]+j-2)//(j-1)
        for i in (*probes, *(x//2 for x in probes)):
            values[k, i] = (Fraction(lo[i], scale), Fraction(hi[i], scale))
        lower, upper = lo, hi

    gaps = []
    for i in probes:
        lo2, hi2 = values[2, i]
        lo3, hi3 = values[3, i]
        lo4, hi4 = values[4, i]
        log_lo, log_hi = values[2, i//2]
        gaps.append(((1-hi2-2*hi3-hi4)/2 + 2*log_lo,
                     (1-lo2-2*lo3-lo4)/2 + 2*log_hi))
    if not (gaps[0][1] < 0 < gaps[1][0]
            and Fraction(2042, 10000) < gaps[2][0] <= gaps[2][1] < Fraction(2043, 10000)):
        raise AssertionError(("signed profile intervals", gaps))
    print("Certified the profile crossing in (4.3844, 4.3848) and the gap at 5 in (0.2042, 0.2043).")


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

    progressions = 0
    for n in range(30, 101, 2):
        for s in divisors[n]:
            x = n // s
            for d in range(1, 13):
                if gcd(d, n) != 1:
                    continue
                for e in range(2, 13):
                    if gcd(e, n) != 1:
                        continue
                    # Open support of the test, before taking the Fourier transform.
                    direct = [m for m in range(1, n) if 5*n < 12*m < 7*n
                              and m % s == 0 and m % d == 0 and (n-m) % e == 0]
                    sampled = []
                    if gcd(d, e) == 1:
                        residue = (x * pow(d, -1, e)) % e
                        sampled = [s*d*k for k in range(residue, x//d + 1, e)
                                   if 5*x < 12*d*k < 7*x]
                    if sampled != direct:
                        raise AssertionError(("reflected progression", n, s, d, e))
                    progressions += 1
    print(f"Verified {progressions} rescaled inverse progressions, including incompatible pairs.")

    square, product = Fraction(20, 39), Fraction(45, 44)
    if Fraction(39, 20)*square != 1 or Fraction(11, 10)*product - Fraction(1, 8) != 1:
        raise AssertionError("Kloosterman exponent endpoints")
    delta, b, c = Fraction(1, 1200), Fraction(1, 25), Fraction(1, 14)
    if not (40*delta < b < Fraction(1, 20)-7*delta
            and Fraction(1, 10)+12*delta-b < c < Fraction(1, 10)-4*delta-3*b/5
            and Fraction(1, 2)+delta < square-Fraction(1, 100)):
        raise AssertionError("three-factor ranges or strip overlap")
    check_rough_pairs()
    check_sifted_twists()
    check_twist_divisors()
    check_twist_profile()


if __name__ == "__main__":
    main()
