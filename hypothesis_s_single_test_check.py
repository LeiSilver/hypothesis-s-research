"""Exact finite checks for the divisor identities and cutoffs of the single test."""

from fractions import Fraction
from math import ceil, factorial, floor, gcd, isqrt, lcm, prod


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


def check_marked_divisors():
    checked = 0
    ps = [factors(n) for n in range(501)]
    for n_sum in range(40, 501, 2):
        for n in range(5*n_sum//12 + 1, (7*n_sum-1)//12 + 1):
            if gcd(n, n_sum) != 1:
                continue
            observed = {}
            for d in range(2, n+1):
                if n % d or len(set(ps[d])) != len(ps[d]):
                    continue
                marked = [r for r in ps[d] if r**5 > n_sum]
                if len(marked) == 1:
                    r = marked[0]
                    observed[r] = observed.get(r, 0) + (-1)**(len(ps[d])-1)
            expected = {r: 1 for r in set(ps[n])} if ps[n][0]**5 > n_sum else {}
            if {r: v for r, v in observed.items() if v} != expected:
                raise AssertionError(("one-large-prime expansion", n_sum, n, observed))
            for r in expected:
                if r**5 > n_sum**3 and len(ps[n//r]) > 1:
                    raise AssertionError(("large marked prime cofactor", n_sum, n, r))
            checked += 1
    print(f"Verified the marked divisor expansion on {checked} unit samples.")


def check_capped_factor_profile(mesh, scale, values, pair_lower, pair_upper):
    # The stored pair densities run from s=2 to 5/2. Across a cell
    # c_2(5(1-t)) decreases and 1/(t(1-t)) increases.
    targets = {51200, 51293, 51296, 55800}
    tails = {}
    lower = upper = 0
    for i in range(3*mesh//5-1, min(targets)-1, -1):
        j = 3*mesh-5*i
        left_den = i*(mesh-i)
        right_den = (i+1)*(mesh-i-1)
        lower += mesh*pair_lower[j-5]//left_den
        upper += (mesh*pair_upper[j]+right_den-1)//right_den
        if i in targets:
            tails[i] = (Fraction(lower, scale), Fraction(upper, scale))

    log_lo, log_hi = values[2, 5*mesh//2]  # log(3/2)
    tri_lo, tri_hi = values[3, 5*mesh]
    four_lo, four_hi = values[4, 5*mesh]
    if 4*(log_lo-four_hi) <= Fraction(384, 100)*tri_hi:
        raise AssertionError("necessary triple mass in the absence of prime and semiprime partners")

    def margin(u, v):
        # log(u/(1-u)) = 2 atanh(2u-1) for 0 <= 2u-1 < 1.
        x = Fraction(2*u, mesh)-1
        cap_lo = 2*sum(x**(2*j+1)/(2*j+1) for j in range(4))
        cap_hi = cap_lo + 2*x**9/(9*(1-x*x))
        j_lo, j_hi = tails[v]
        return (4*(log_lo-cap_hi-tri_hi-four_hi+j_lo),
                4*(log_hi-cap_lo-tri_lo-four_lo+j_hi))

    if not (margin(51200, 51200)[0] > Fraction(20, 1000)
            and margin(50000, 55800)[0] > Fraction(5, 1000)
            and margin(51293, 51293)[0] > 0 > margin(51296, 51296)[1]):
        raise AssertionError(("fifth-root cutoff margins", tails))
    print("Certified the fifth-root mass bounds and the crossing in (0.51293, 0.51296).")


def check_twist_profile():
    # Row k encloses c_k(i/mesh) in units of 1/scale. On each cell
    # bound the increasing numerator and the reciprocal separately.
    mesh, scale = 100_000, 2**54
    points = 5*mesh + 1
    lower = [scale if i >= mesh else 0 for i in range(points)]
    upper = lower.copy()
    probes = (438_440, 438_480, 500_000)
    values = {}
    # The marked-prime integral uses c_2 and c_3 at 5(1-x).
    q = 10_000
    cells = range(q//5, 2*q//5 + 1)
    marked_lo, marked_hi = [0]*len(cells), [0]*len(cells)
    for k in (2, 3, 4):
        lo, hi = [0]*points, [0]*points
        for i in range(k*mesh + 1, points):
            j = i - mesh
            lo[i] = lo[i-1] + lower[j-1]//j
            hi[i] = hi[i-1] + (upper[j]+j-2)//(j-1)
        for i in (*probes, *(x//2 for x in probes)):
            values[k, i] = (Fraction(lo[i], scale), Fraction(hi[i], scale))
        if k == 2:
            pair_lower = lo[2*mesh:5*mesh//2 + 1]
            pair_upper = hi[2*mesh:5*mesh//2 + 1]
        if k in (2, 3):
            for j, i in enumerate(cells):
                index = 5*(q-i)*mesh//q
                marked_lo[j] += lo[index]
                marked_hi[j] += hi[index]
        lower, upper = lo, hi

    gaps = []
    check_capped_factor_profile(mesh, scale, values, pair_lower, pair_upper)
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

    loss_lo = loss_hi = 0
    for j, i in enumerate(cells):
        # Includes the cell width 1/q. Accumulators are in units of 1/scale.
        weight = Fraction(2*q-5*i, 2*q)**5 * Fraction(q, i*(q-i))
        if j:
            loss_lo += floor(marked_lo[j]*weight)
        if j+1 < len(cells):
            loss_hi += ceil(marked_hi[j]*weight)
    baseline = (1-Fraction(loss_hi, scale), 1-Fraction(loss_lo, scale))
    if not (Fraction(9930, 10000) < baseline[0] <= baseline[1] < Fraction(9931, 10000)):
        raise AssertionError(("one-large-prime baseline", baseline))
    print("Certified the one-large-prime minorant constant in (0.9930, 0.9931).")


def check_upper_mark_sieve():
    # For decreasing integrands, left endpoints bound each cell above.
    mesh, scale = 500_000, 2**54
    intervals = []
    for j in (1, 2):
        lower = upper = 0
        for i in range(mesh//5, 2*mesh//5 + 1):
            numerator = scale * (2*mesh-5*i)**5 * mesh**j
            denominator = (2*mesh)**5 * i * (mesh-i)**j
            if i > mesh//5:
                lower += numerator//denominator
            if i < 2*mesh//5:
                upper += (numerator+denominator-1)//denominator
        intervals.append((Fraction(lower, scale), Fraction(upper, scale)))
    (lo1, hi1), (lo2, hi2) = intervals
    lower, upper = 1+lo1-4*hi2, 1+hi1-4*lo2
    if not (Fraction(97510, 100000) < lower <= upper < Fraction(97511, 100000)
            and 4*hi2 < Fraction(3086, 100000)):
        raise AssertionError(("upper-range sieve coefficients", intervals))
    print("Certified the upper-range lower coefficient in (0.97510, 0.97511) and width below 0.03086.")
    if 4*hi1 >= Fraction(2383, 100000) or 1-3*hi1 <= Fraction(98212, 100000):
        raise AssertionError(("semiprime product sieve coefficients", intervals[0]))
    print("Certified the semiprime width below 0.02383 and lower coefficient above 0.98212.")


def check_interval_proportions():
    primes = [p for p in range(3, 32, 2) if factors(p) == [p]]
    small = primes[:4]
    period = prod(small)
    values = [prod(Fraction(p, p-1) if n % p == 0 else Fraction(p*(p-2), (p-1)**2)
                   for p in small) for n in range(0, 2*period, 2)]
    second_moment = prod(1 + Fraction(1, (p-1)**3) for p in small)
    if sum(values) != period or sum(z*z for z in values) != period*second_moment:
        raise AssertionError("local singular-series moments on even residues")

    partial_product = prod(1 + Fraction(1, (p-1)**3) for p in primes)
    tail_sum_bound = Fraction(1, 2*31**2)
    variance_bound = Fraction(152, 1000)
    if partial_product/(1-tail_sum_bound) >= 1 + variance_bound:
        raise AssertionError("singular-series second-moment bound")
    for margin, fraction in [(Fraction(1, 2), Fraction(1, 20)),
                             (Fraction(1, 100), Fraction(3, 25))]:
        gap = (1-margin)/(4-margin) - fraction
        if gap <= 0 or gap**2 <= variance_bound*fraction*(1-fraction):
            raise AssertionError(("short-interval proportion", margin, fraction))
    print(f"Verified singular-series moments on {period} even residues and both interval proportions.")


def check_presifted_large_factor():
    kappa, eta = Fraction(1, 2000), Fraction(1, 64000)
    eps, beta = Fraction(1, 1000), Fraction(121, 200)
    b = Fraction(1, 2) - 2*kappa
    u = (1-b)/(1-beta) - 1
    log_upper = sum((-1)**(j-1)*u**j/j for j in range(1, 8))
    coefficient = 1-eps-(1+eps)*(b + 2*log_upper/(1-8*kappa))
    first_term = Fraction(3, 2)**13/factorial(13)
    ratio = Fraction(9, 4)/(14*15)
    if not (0 < u < 1 and coefficient > Fraction(1, 50)
            and 8*first_term/(1-ratio) < Fraction(1, 10000)
            and 29*eta < kappa and 8*(1-beta) > 1
            and (1-b)*(1-8*kappa)/2 < b):
        raise AssertionError("explicit logarithmic-moment and sieve levels")

    checked = 0
    for n in range(48, 101, 2):
        for q in (11, 13):
            if n % q == 0:
                continue
            for a in (1, 2, 3, 6):
                rho = prod(1 if n % p == 0 else 2 for p in factors(a))
                for d in (1, 5, 7, 35):
                    hits = sum(k*(n-q*k) % a == 0 and (n-q*k) % d == 0
                               for k in range(a*d))
                    if hits != rho:
                        raise AssertionError(("two sieve levels", n, q, a, d))
                    checked += 1
    print(f"Certified the 121/200 large-factor example and {checked} disjoint sieve densities.")


def check_exceptional_character_classes():
    # Primitive quadratic components listed by their values on odd units.
    two_parts = [(1, {0: 1}), (4, {1: 1, 3: -1}),
                 (8, {1: 1, 3: -1, 5: -1, 7: 1}),
                 (8, {1: 1, 3: 1, 5: -1, 7: -1})]
    checked = zero_classes = lifts = 0
    for two_part, local in two_parts:
        for odd in (1, 3, 5, 7, 11, 15, 21, 35, 105):
            q = two_part*odd
            if q == 1:
                continue
            ps = factors(odd)
            squares = {p: {a*a % p for a in range(1, p)} for p in ps}
            chi = [local.get(a % two_part, 0)
                   * prod(0 if a % p == 0 else 1 if a % p in squares[p] else -1 for p in ps)
                   for a in range(q)]
            d = len(local)
            base = odd//gcd(odd, 3)
            period = lcm(2, q)
            phi = sum(value != 0 for value in chi)
            vanishing = set()
            for n in range(0, period, 2):
                pairs = [(chi[a], chi[(n-a) % q]) for a in range(q) if chi[a] and chi[(n-a) % q]]
                signs = [s*t for s, t in pairs]
                predicted = (chi[-1]*(-1)**(n//d)*prod(Fraction(-1, p-2) for p in ps if n % p)
                             if n % d == 0 else 0)
                missing_three = int(odd % 3 == 0 and n % 3 != 0)
                zero = n % (d*base) == 0 and chi[-1]*(-1)**(n//d+missing_three) == -1
                if (Fraction(sum(signs), len(signs)) != predicted or (predicted == -1) != zero
                        or (not zero and 1+predicted < Fraction(2, 3))):
                    raise AssertionError(("exceptional character class", q, chi[-1], n))
                if n == 0 and predicted != chi[-1]:
                    raise AssertionError(("conductor multiple", q))
                local_mean = 2*prod(Fraction(p, p-1) if n % p == 0 else Fraction(p*(p-2), (p-1)**2)
                                    for p in ps)
                if local_mean != Fraction(period*len(pairs), phi**2):
                    raise AssertionError(("progression singular-series mean", q, n))
                if zero:
                    # Coefficients of (1-s*z)(1-t*z) for each admissible ordered pair.
                    if any(s+t != 0 or s*t != -1 for s, t in pairs):
                        raise AssertionError(("secondary prime-pair term", q, n))
                    small = [p for p in (3, 5, 7, 11, 13) if n % p]
                    local_product = prod(Fraction(p-2, p-1) for p in small if q % p)
                    positive = sum(first == 1 for first, _ in pairs)
                    expected = prod(Fraction(p-2, p-1) for p in small)
                    if 2*Fraction(positive, phi)*local_product != expected:
                        raise AssertionError(("oriented sieve normalization", q, n))
                    for divisor in (3, 5, 7, 15, 35):
                        if gcd(divisor, period) != 1:
                            continue
                        lifted_n = divisor * (n * pow(divisor, -1, q) % q)
                        modulus = q*divisor
                        admissible = sum(gcd(a*(lifted_n-a), modulus) == 1 for a in range(modulus))
                        phi_divisor = prod(p-1 for p in factors(divisor))
                        if admissible != len(pairs)*phi_divisor:
                            raise AssertionError(("divisible sum in lifted class", q, n, divisor))
                        lifts += 1
                    vanishing.add(n)
                checked += 1
            zero_classes += len(vanishing)
            if chi[-1] == -1:
                witness = 2*q**12
            elif two_part > 1:
                witness = 2*q**12 + q//2
            elif odd % 3 == 0:
                witness = 2*q**12 + 2*q//3
            else:
                if vanishing:
                    raise AssertionError(("positive in every even class", q))
                continue
            if witness % period not in vanishing:
                raise AssertionError(("zero-free witness", q, witness))
    print(f"Verified the character and singular-series factors on {checked} even classes "
          f"and the secondary term on {zero_classes} vanishing classes, with {lifts} CRT lifts.")


def check_exceptional_pair_moment():
    checked = 0
    for period, residue, p1, p2 in [(6, 0, 11, 41), (8, 4, 13, 37), (30, 0, 17, 101)]:
        for ell in (2, 3, 5, 7, 11, 13):
            roots = sum((residue + i*period - p1)*(residue + i*period - p2) % ell == 0
                        for i in range(ell))
            if period % ell == 0:
                expected = 0
            elif (p1-p2) % ell == 0:
                expected = 1
            else:
                expected = 2
            if roots != expected:
                raise AssertionError(("partner sieve", period, p1, p2, ell))
            checked += 1
    for n in range(1, 320):
        for period in (6, 8, 30):
            ps = sorted(set(p for p in factors(n) if period % p))
            divisors = [(1, 1)]
            for p in ps:
                divisors += [(d*p, -mu) for d, mu in divisors]
            reciprocal = sum(Fraction(mu, prod(p-1 for p in factors(d))) for d, mu in divisors)
            if reciprocal != prod(Fraction(p-2, p-1) for p in ps):
                raise AssertionError(("reciprocal singular series", n, period))
            checked += 1
    print(f"Verified {checked} partner-sieve and reciprocal singular-series identities.")


def check_oriented_rough_partners():
    limit = 3600
    prime_factors = [factors(n) for n in range(limit)]
    tested = marked = prime_pairs = 0
    for modulus, positive, negative, zero_residue in [
        (3, {1}, {2}, 0), (4, {1}, {3}, 0), (8, {1, 7}, {3, 5}, 4)
    ]:
        for n in range(300, limit, 2):
            if n % modulus != zero_residue:
                continue
            ordered = oriented_primes = 0
            for p in range(5*n//12+1, (7*n-1)//12+1):
                if len(prime_factors[p]) != 1 or p == n-p:
                    continue
                partner = prime_factors[n-p]
                ordered += len(partner) == 1
                if p % modulus not in positive or min(partner) <= 5:
                    continue
                if (n-p) % modulus not in negative:
                    raise AssertionError(("rough partner character", modulus, n, p))
                oriented_primes += len(partner) == 1
                small_positive = {r for r in partner if r <= 25 and r % modulus in positive}
                if bool(small_positive) != any((n-p) % r == 0 and r % modulus in positive
                                               for r in (7, 11, 13, 17, 19, 23)):
                    raise AssertionError(("marked rough partner", modulus, n, p))
                marked += bool(small_positive)
                tested += 1
            if ordered != 2*oriented_primes:
                raise AssertionError(("ordered prime-pair orientation", modulus, n))
            prime_pairs += oriented_primes
    if not (0 < marked < tested and 0 < prime_pairs < tested):
        raise AssertionError("missing rough-partner cases")
    print(f"Verified orientation on {tested} rough samples, including {prime_pairs} prime "
          f"partners and {marked} samples with a marked positive factor.")


def check_switched_logarithmic_sieve():
    # gamma < H_m - log(m). Bound exp(H_m) by its Taylor series
    # with a geometric tail, keeping every operation rational.
    harmonic = sum(Fraction(1, j) for j in range(1, 65))
    exp_upper = (sum(harmonic**j/factorial(j) for j in range(37))
                 + harmonic**37/(factorial(37)*(1-harmonic/38)))
    e_gamma_upper = Fraction(9, 5)
    tolerance = Fraction(1, 10**6)
    if exp_upper/64 >= e_gamma_upper or 2*e_gamma_upper/(10*factorial(9)) >= tolerance:
        raise AssertionError("linear sieve function enclosure")
    a, b = Fraction(9, 10), Fraction(1, 2)
    x = 1/a-1
    log_upper = x-x**2/2+x**3/3
    choices = [(Fraction(121, 200), Fraction(1, 50), Fraction(1, 3000)),
               (Fraction(31, 50), Fraction(1, 220), Fraction(1, 600))]
    for beta, eta, target in choices:
        switch = b-a*eta
        lower = ((1-b)*(1-tolerance) - 2*e_gamma_upper*eta*log_upper
                 - (2/b)*(1+tolerance)*(beta-switch))
        if not (eta < b-eta < switch < beta and min(b/eta, (1-beta)/eta-1) > 10
                and lower > target):
            raise AssertionError(("switched logarithmic mass", beta, eta, lower, target))
    if not 19 < (1-choices[0][0])/choices[0][1] < 20:
        raise AssertionError("switched cofactor multiplicity")
    print("Certified both switched logarithmic mass bounds and the 19-factor cofactor limit.")


def check_joint_sieve():
    beta, eps = Fraction(121, 200), Fraction(1, 100000)
    for eta, target in [(Fraction(1, 800), Fraction(1, 50)),
                        (Fraction(1, 220), Fraction(1, 5000))]:
        ratio = (Fraction(1, 2)-eta)/(1-beta-2*eta)
        v = (ratio-1)/(ratio+1)
        # log(ratio) = 2 atanh(v), with a geometric majorant on the tail.
        terms = 6
        log_upper = 2*(sum(v**(2*j+1)/(2*j+1) for j in range(terms))
                       + v**(2*terms+1)/((2*terms+1)*(1-v*v)))
        if not (0 < v < 1 and Fraction(1, 2)-2*log_upper-2*eps > target):
            raise AssertionError(("joint sieve logarithmic margin", eta, target))
    if not 86 < (1-beta)*220 < 87:
        raise AssertionError("cofactor multiplicity cutoff")

    ps = [factors(n) for n in range(97)]
    squarefree = [n for n in range(1, 97) if len(ps[n]) == len(set(ps[n]))]
    phi = {n: prod(p-1 for p in ps[n]) for n in squarefree}
    checked = 0
    for n in range(48, 101, 2):
        for y in (3, 5, 7, 11):
            eligible = {p for p in (3, 5, 7, 11) if p <= y and n % p}
            for cutoff in (12, 37, 96):
                direct = Fraction(0)
                opened = Fraction(0)
                for d in squarefree:
                    if d > cutoff:
                        break
                    direct += prod(Fraction(2, p-2) if p in eligible else Fraction(1, p-1)
                                   for p in ps[d])
                    if not eligible.issuperset(ps[d]):
                        continue
                    u = prod(Fraction(p, (p-1)*(p-2)) for p in ps[d])
                    inner = sum(Fraction(1, phi[e]) for e in squarefree
                                if e*d <= cutoff and gcd(e, d) == 1)
                    opened += u*inner
                if direct != opened:
                    raise AssertionError(("joint Selberg denominator", n, y, cutoff))
                checked += 1
    print(f"Certified both raised cutoffs and {checked} joint Selberg denominator identities.")


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
    check_marked_divisors()
    check_twist_profile()
    check_upper_mark_sieve()
    check_presifted_large_factor()
    check_joint_sieve()
    check_switched_logarithmic_sieve()
    check_interval_proportions()
    check_exceptional_character_classes()
    check_exceptional_pair_moment()
    check_oriented_rough_partners()


if __name__ == "__main__":
    main()
