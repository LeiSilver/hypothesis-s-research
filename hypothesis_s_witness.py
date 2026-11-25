"""Find and check a rational trial weight for a single even modulus.

Floating point selects a direction. The enrichment to a rational piecewise
linear weight is checked separately through integer arithmetic, correctly
rounded Decimal logarithms and interval bounds for the Hardy norm.
"""

import argparse
import json
from bisect import bisect_right
from decimal import Decimal, localcontext
from fractions import Fraction
from math import ceil, floor, gcd, log
from pathlib import Path

import numpy as np
from mpmath import iv
from scipy.linalg import eigh

from hypothesis_s_boundary import prime_factors
from hypothesis_s_compression import arithmetic_matrix, hardy_gram, model_matrix, prime_powers, sieve, singular_series


SCALE = 10**18
POSITION_SCALE = 10**8
WEIGHT_SCALE = 10**12


def rounded_bounds(x):
    numerator, denominator = x.numerator * SCALE, x.denominator
    return numerator // denominator, -((-numerator) // denominator)


def square_bounds(low, high):
    return (0 if low <= 0 <= high else min(low * low, high * high), max(low * low, high * high))


def multiply_bounds(first, second):
    endpoints = [a * b for a in first for b in second]
    return min(endpoints), max(endpoints)


def trial_weight(modulus, upper, dimension, primes):
    knots = np.linspace(log(2.5), log(upper), dimension + 2)
    powers = prime_powers(primes, upper)
    odd = primes[primes > 2].astype(float)
    twin_constant = 2 * np.exp(np.log1p(-1 / (odd - 1)**2).sum())
    _, densities = singular_series(modulus, 2 * upper // modulus, primes, twin_constant)
    arithmetic = arithmetic_matrix(modulus, knots, ((primes, None), powers))
    model = model_matrix(modulus, knots, densities, 16)
    gram, _ = hardy_gram(modulus, knots, 16)
    eigenvalues, eigenvectors = eigh(arithmetic - model, gram)
    k = int(np.argmax(abs(eigenvalues)))
    positions = np.exp(knots)
    values = np.r_[0, eigenvectors[:, k], 0] / np.sqrt(positions)
    nodes = [int(round(p * POSITION_SCALE)) for p in positions]
    values = [int(round(v * WEIGHT_SCALE)) for v in values]
    return nodes, values


def weight_at(twice_x, knots, values):
    # twice_x is twice the position in scaled units, which includes midpoints.
    cell = min(bisect_right(knots, twice_x // 2) - 1, len(knots) - 2)
    a, b = knots[cell : cell + 2]
    left, right = values[cell : cell + 2]
    numerator = left * (2 * b - twice_x) + right * (twice_x - 2 * a)
    return Fraction(numerator, 2 * WEIGHT_SCALE * (b - a))


def arithmetic_bounds(modulus, knots, values, primes):
    residues = [[0, 0] for _ in range(modulus // 2)]
    diagonal_low = diagonal_high = 0
    last = knots[-1] // POSITION_SCALE
    with localcontext() as ctx:
        ctx.prec = 42
        for p in primes[primes <= last]:
            p = int(p)
            if gcd(p, modulus) > 1:
                continue
            # At this precision the rounded Decimal logarithm differs by
            # much less than one unit on the integer scale used below.
            middle = int(Decimal(p).ln() * SCALE)
            value = p
            while value <= last:
                scaled_x = POSITION_SCALE * value
                if scaled_x >= knots[0]:
                    weight = weight_at(2 * scaled_x, knots, values)
                    endpoints = [(middle - 1) * weight, (middle + 2) * weight]
                    lower = floor(min(endpoints))
                    upper = ceil(max(endpoints))
                    left, right = square_bounds(lower, upper)
                    diagonal_low += left
                    diagonal_high += right
                    a = value % modulus
                    if a > modulus // 2:
                        a = modulus - a
                        lower, upper = -upper, -lower
                    residues[a][0] += lower
                    residues[a][1] += upper
                value *= p

    squared = [square_bounds(low, high) for low, high in residues]
    return sum(pair[0] for pair in squared) - diagonal_high, sum(pair[1] for pair in squared) - diagonal_low


def twin_constant_bounds(primes, limit):
    low = high = 2 * SCALE
    for p in primes[(primes > 2) & (primes <= limit)]:
        p = int(p)
        numerator, denominator = p * (p - 2), (p - 1)**2
        low = low * numerator // denominator
        high = -((-high * numerator) // denominator)
    # Product of the omitted factors is at least 1 - sum_{n >= limit} 1/n^2.
    return low * (limit - 2) // (limit - 1), high


def density_bounds(n, twin):
    factor = Fraction(1)
    for prime, _ in prime_factors(n):
        if prime > 2:
            factor *= Fraction(prime - 1, prime - 2)
    low = floor(twin[0] * factor)
    high = ceil(twin[1] * factor)
    return low, high


def continuous_line_bounds(h, direction, knots, values):
    mapped = [direction * (y - h) for y in knots]
    left = max(knots[0], min(mapped[0], mapped[-1]))
    right = min(knots[-1], max(mapped[0], mapped[-1]))
    if left >= right:
        return 0, 0
    cuts = sorted({left, right, *(x for x in knots if left < x < right),
                   *(x for x in mapped if left < x < right)})
    low = high = 0
    for a, b in zip(cuts, cuts[1:]):
        samples = (2 * a, a + b, 2 * b)
        integrand = [weight_at(x, knots, values) * weight_at(2 * h + direction * x, knots, values)
                     for x in samples]
        # The product of the two linear pieces is quadratic, so Simpson is exact.
        integral = Fraction(b - a, 6 * POSITION_SCALE) * (integrand[0] + 4 * integrand[1] + integrand[2])
        lower, upper = rounded_bounds(integral)
        low += lower
        high += upper
    return low, high


def model_bounds(modulus, knots, values, twin):
    low = high = 0
    for k in range(1, 2 * knots[-1] // (modulus * POSITION_SCALE) + 1):
        n = k * modulus
        shifted = continuous_line_bounds(n * POSITION_SCALE, 1, knots, values)
        reflected = continuous_line_bounds(n * POSITION_SCALE, -1, knots, values)
        signed = 2 * shifted[0] - reflected[1], 2 * shifted[1] - reflected[0]
        lower, upper = multiply_bounds(signed, density_bounds(n, twin))
        low += lower
        high += upper
    return low, high


def as_interval(fraction):
    return iv.mpf(fraction.numerator) / fraction.denominator


def hardy_norm_upper(modulus, knots, values):
    bound = iv.mpf(0)
    alpha = 1 / iv.ln(modulus)
    for a, b, left, right in zip(knots, knots[1:], values, values[1:]):
        slope = Fraction(right - left, WEIGHT_SCALE * (b - a))
        f_left = Fraction(left, 2 * WEIGHT_SCALE) - a * slope
        f_right = Fraction(right, 2 * WEIGHT_SCALE) - b * slope
        integral = Fraction(b - a, 3 * POSITION_SCALE) * (f_left**2 + f_left * f_right + f_right**2)
        log_right = iv.ln(iv.mpf(b) / POSITION_SCALE)
        weight_upper = 1 / (iv.exp(-2 * alpha * log_right) + iv.exp(-log_right / 4))
        bound += as_interval(integral) * weight_upper
    return bound / (2 * iv.pi)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--modulus", type=int, default=32762)
    parser.add_argument("--upper-ratio", type=int, default=64)
    parser.add_argument("--dimension", type=int, default=255)
    parser.add_argument("--weight-file", type=Path, help="check an existing rational weight")
    parser.add_argument("--save-weight", type=Path, help="save the rational weight as JSON")
    args = parser.parse_args()
    n = args.modulus
    if args.weight_file:
        data = json.loads(args.weight_file.read_text(encoding="utf-8"))
        if (data["position_scale"], data["weight_scale"]) != (POSITION_SCALE, WEIGHT_SCALE):
            parser.error("the input weight uses unsupported fixed-point scales")
        n, knots, values = data["modulus"], data["knots"], data["values"]
        if (len(knots) < 3 or len(knots) != len(values) or knots[0] <= 0
                or any(a >= b for a, b in zip(knots, knots[1:])) or values[0] or values[-1]):
            parser.error("use at least three positive increasing knots and zero endpoint weights")
        upper = (knots[-1] + POSITION_SCALE - 1) // POSITION_SCALE
    else:
        upper = args.upper_ratio * n
    if n % 2 or n <= np.exp(10) or args.upper_ratio <= 0 or args.dimension <= 0:
        parser.error("use an even modulus greater than exp(10) and positive ratio and dimension")
    primes = sieve(max(upper, 100000))
    if not args.weight_file:
        knots, values = trial_weight(n, upper, args.dimension, primes)
    if args.save_weight:
        data = {
            "modulus": n, "position_scale": POSITION_SCALE, "weight_scale": WEIGHT_SCALE,
            "knots": knots, "values": values,
        }
        args.save_weight.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    twin = twin_constant_bounds(primes, 100000)
    arithmetic = arithmetic_bounds(n, knots, values, primes)
    model = model_bounds(n, knots, values, twin)
    lower, upper = arithmetic[0] - model[1], arithmetic[1] - model[0]
    signed_lower = max(0, lower, -upper)

    iv.dps = 36
    norm_upper = hardy_norm_upper(n, knots, values)
    rayleigh_lower = (iv.mpf(signed_lower) / SCALE**2 / norm_upper.b).a
    singular_endpoints = density_bounds(n, twin)
    series = iv.mpf(singular_endpoints) / SCALE
    delta = iv.sqrt(series / n) * iv.ln(n)**iv.mpf("1.5")
    maximal_s_width_bound = 2 * delta / iv.sqrt(3)
    print(f"N={n}, fixed rational trial on {len(values)} knots")
    print("Arithmetic residual interval", iv.mpf([lower, upper]) / SCALE**2)
    print("Upper bound on squared Hardy norm", norm_upper.b)
    print("Lower bound on full operator norm, under GRH(N)", rayleigh_lower)
    print("R threshold", delta)
    print("S threshold for eta=1/4", maximal_s_width_bound)
    print("Exceeds R at this modulus:", bool(rayleigh_lower > delta.b))
    print("Exceeds S with eta=1/4 at this modulus:", bool(rayleigh_lower > maximal_s_width_bound.b))


if __name__ == "__main__":
    main()
