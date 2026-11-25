"""Certify the norm of the Li–Liu block on [N/3, 2N/3] under GRH(N)."""

import argparse
from dataclasses import dataclass
from fractions import Fraction
from math import exp, isfinite, isqrt

import numpy as np
from mpmath import iv

from hypothesis_s_compression import sieve
from hypothesis_s_critical_certificate import power_bases
from hypothesis_s_witness import SCALE, as_interval, density_bounds, twin_constant_bounds


@dataclass(frozen=True, slots=True)
class Cell:
    width: object
    lower: tuple
    upper: tuple
    min_derivative: object
    max_mass: object


def balanced_mesh(modulus, intervals, singular):
    """Use every Goldbach atom as a node, together with a uniform mesh."""
    lower = modulus // 3 + 1
    upper = modulus - lower
    primes = sieve(upper)
    powers = power_bases(primes[: np.searchsorted(primes, isqrt(upper), side="right")], lower, upper)
    active = np.zeros(upper + 1, dtype=bool)
    active[primes] = True
    for power in powers:
        active[power] = True
    partners = active[lower : upper + 1]
    positions = lower + np.flatnonzero(partners & partners[::-1])
    positions = positions[np.gcd(positions, modulus) == 1]

    # This common denominator represents both n/N and the uniform mesh exactly.
    denominator = 3 * modulus * intervals
    atoms = {}
    for n in map(int, positions):
        m = modulus - n
        weight = iv.ln(powers.get(n, n)) * iv.ln(powers.get(m, m))
        atoms[3 * intervals * n] = -weight / (modulus * singular)
    nodes = sorted(set(atoms) | {(intervals + j) * modulus for j in range(intervals + 1)})
    assert all(left + right == denominator for left, right in zip(nodes, reversed(nodes)))
    return denominator, nodes, [atoms.get(node, iv.mpf(0)) for node in nodes[1:-1]], len(atoms)


def hardy_cells(modulus, denominator, nodes):
    alpha = 1 / iv.ln(modulus)
    derivative, weight, slope = [], [], []
    for node in nodes:
        u = iv.mpf(node) / denominator
        nu = iv.ln(modulus * u)
        left, right = iv.exp(-2 * alpha * nu), iv.exp(-nu / 4)
        a = 1 / (2 * iv.pi * (left + right))
        derivative.append(u**2 * a)
        weight.append(a)
        slope.append((2 * alpha * left + right / 4) / (left + right))

    # The derivative coefficient increases, while the logarithmic slope decreases.
    cells = []
    last = len(nodes) - 1
    for i in range(last):
        j = last - i - 1
        lesser = (derivative[i], derivative[j],
                  weight[i] * (3 + 2 * slope[i + 1]) / 4,
                  weight[j] * (3 + 2 * slope[j + 1]) / 4)
        greater = (derivative[i + 1], derivative[j + 1],
                   weight[i + 1] * (3 + 2 * slope[i]) / 4,
                   weight[j + 1] * (3 + 2 * slope[j]) / 4)
        width = iv.mpf(nodes[i + 1] - nodes[i]) / denominator
        cells.append(Cell(width, lesser, greater, min(lesser[0].a, lesser[1].a),
                          max(lesser[2].b, lesser[3].b)))
    return cells


def element_matrices(cells, bound, use_lower):
    """Return diagonal and adjacent blocks of the piecewise linear form."""
    result = []
    for cell in cells:
        p_f, p_g, d_f, d_g = cell.lower if use_lower else cell.upper
        length = cell.width
        loss = 0
        if use_lower:
            # Complete the square against the residual vanishing at both nodes.
            length_squared = length**2
            denominator = 9 * bound * cell.min_derivative - length_squared
            if not denominator > 0:
                return None
            loss = length_squared * (1 + bound * cell.max_mass)**2 / denominator
        stiffness_f = bound * p_f / length
        stiffness_g = bound * p_g / length
        mass_f = length * (bound * d_f - loss) / 6
        mass_g = length * (bound * d_g - loss) / 6
        diagonal = (stiffness_f + 2 * mass_f, stiffness_g + 2 * mass_g, length / 3)
        adjacent = (-stiffness_f + mass_f, -stiffness_g + mass_g, length / 6)
        result.append((diagonal, adjacent))
    return result


def back_substitution(start, couplings, size):
    vector = [start]
    for a, b, c, d in reversed(couplings):
        f, g = vector[-1]
        vector.append((-a * f - b * g, -c * f - d * g))
    if not all(isfinite(value) for row in vector for value in row):
        return None
    scale = max(abs(value) for row in vector for value in row)
    result = [(f / scale, g / scale) for f, g in reversed(vector)]
    return result + [(0.0, 0.0)] * (size - len(result))


def positive(cells, atoms, bound, use_lower, trial=False):
    """Use a block LDL test. None means the sign was not certified."""
    blocks = element_matrices(cells, bound, use_lower)
    if blocks is None:
        return None
    xf = xg = cross = 0
    couplings = []

    def negative(f, g):
        return back_substitution((f, g), couplings, len(atoms)) if trial else False

    for index, atom in enumerate(atoms):
        a, b, c = blocks[index][0]
        u, v, w = blocks[index + 1][0]
        pivot_f, pivot_g, pivot_cross = a + u - xf, b + v - xg, c + w + atom - cross
        if pivot_f < 0:
            return negative(1.0, 0.0)
        if pivot_g < 0:
            return negative(0.0, 1.0)
        if not (pivot_f > 0 and pivot_g > 0):
            return None
        schur_f = pivot_f - pivot_cross**2 / pivot_g
        schur_g = pivot_g - pivot_cross**2 / pivot_f
        if schur_f < 0:
            return negative(1.0, -pivot_cross / pivot_g)
        if schur_g < 0:
            return negative(-pivot_cross / pivot_f, 1.0)
        if not (schur_f > 0 and schur_g > 0):
            return None
        if index + 1 < len(atoms):
            inv_f, inv_g = 1 / schur_f, 1 / schur_g
            inv_cross = -pivot_cross / (pivot_f * schur_g)
            u, v, w = blocks[index + 1][1]
            xf = u**2 * inv_f + 2 * u * w * inv_cross + w**2 * inv_g
            xg = w**2 * inv_f + 2 * w * v * inv_cross + v**2 * inv_g
            cross = u * w * inv_f + (u * v + w**2) * inv_cross + w * v * inv_g
            if trial:
                couplings.append((inv_f * u + inv_cross * w, inv_f * w + inv_cross * v,
                                  inv_cross * u + inv_g * w, inv_cross * w + inv_g * v))
    return True


def floating_search(cells, atoms, use_lower):
    lo, hi = 0.0, 1.0
    while positive(cells, atoms, hi, use_lower) is not True:
        hi *= 2
    for _ in range(30):
        candidate = (lo + hi) / 2
        if positive(cells, atoms, candidate, use_lower) is True:
            hi = candidate
        else:
            lo = candidate
    return hi if use_lower else lo


def trial_value(cells, atoms, bound, vector):
    knots = [(0, 0), *((iv.mpf(f), iv.mpf(g)) for f, g in vector), (0, 0)]
    total = iv.mpf(0)
    for cell, (f, g), (u, v) in zip(cells, knots, knots[1:]):
        p_f, p_g, d_f, d_g = cell.upper
        total += bound * (p_f * (u - f)**2 + p_g * (v - g)**2) / cell.width
        mass_f = bound * d_f * (f * f + f * u + u * u)
        mass_g = bound * d_g * (g * g + g * v + v * v)
        cross = 2 * f * g + f * v + u * g + 2 * u * v
        total += cell.width * (mass_f + mass_g + cross) / 3
    for atom, (f, g) in zip(atoms, knots[1:-1]):
        total += 2 * atom * f * g
    return total


def certify(cells, atoms):
    def midpoint(interval):
        return float(interval.mid)

    floats = [Cell(midpoint(c.width), tuple(map(midpoint, c.lower)), tuple(map(midpoint, c.upper)),
                   midpoint(c.min_derivative), midpoint(c.max_mass)) for c in cells]
    heights = list(map(midpoint, atoms))
    upper = Fraction.from_float(floating_search(floats, heights, use_lower=True))
    lower = Fraction.from_float(floating_search(floats, heights, use_lower=False))
    for attempt in range(16):
        margin = Fraction(1 << attempt, 1000)
        high = as_interval(upper + margin * max(upper, Fraction(1, 10**8)))
        if positive(cells, atoms, high, use_lower=True) is True:
            break
    else:
        raise ArithmeticError("Unable to certify the upper bracket.")
    vector = None
    for attempt in range(16):
        margin = Fraction(1 << attempt, 1000)
        candidate = max(0, lower - margin * max(lower, Fraction(1, 10**8)))
        low = as_interval(candidate)
        if candidate == 0:
            break
        if vector is None:
            trial = positive(floats, heights, float(candidate), use_lower=False, trial=True)
            if isinstance(trial, list):
                vector = trial
        if isinstance(vector, list) and trial_value(cells, atoms, low, vector) < 0:
            break
    else:
        low = iv.mpf(0)
    return iv.mpf([low.a, high.b])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modulus", nargs="+", type=int)
    parser.add_argument("--intervals", type=int, default=2048, help="Number of uniform cells added to the atom mesh.")
    args = parser.parse_args()
    if args.intervals < 1 or any(n <= exp(10) or n % 2 for n in args.modulus):
        parser.error("Use even moduli greater than exp(10) and a positive number of intervals.")

    iv.dps = 45
    twin_limit = 1_000_000
    twin = twin_constant_bounds(sieve(twin_limit), twin_limit)
    for n in args.modulus:
        singular = iv.mpf(list(density_bounds(n, twin))) / SCALE
        denominator, nodes, atoms, count = balanced_mesh(n, args.intervals, singular)
        print(f"N={n}, Goldbach atoms={count}, cells={len(nodes) - 1}", flush=True)
        cells = hardy_cells(n, denominator, nodes)
        print(f"Normalized balanced-window norm under GRH(N): {certify(cells, atoms)}", flush=True)


if __name__ == "__main__":
    main()
