"""Compute finite-window Ritz values for Li and Liu's Hypothesis S.

The integration and the singular series are evaluated in floating point.
The resulting values estimate lower bounds, conditional on the paper's GRH.
"""

import argparse
from math import isqrt, log

import numpy as np
from scipy.linalg import eigh


def sieve(limit):
    is_prime = np.ones(limit + 1, dtype=bool)
    is_prime[:2] = False
    for prime in range(2, isqrt(limit) + 1):
        if is_prime[prime]:
            is_prime[prime * prime :: prime] = False
    return np.flatnonzero(is_prime)


def prime_powers(primes, limit):
    integers = []
    weights = []
    for prime in primes[primes <= isqrt(limit)]:
        value = int(prime) ** 2
        while value <= limit:
            integers.append(value)
            weights.append(log(prime))
            value *= int(prime)
    order = np.argsort(integers)
    return np.asarray(integers, dtype=np.int64)[order], np.asarray(weights)[order]


def hat_coordinates(values, knots):
    position = (values - knots[0]) / (knots[1] - knots[0])
    index = np.clip(position.astype(np.int64), 0, len(knots) - 2)
    fraction = np.clip(position - index, 0, 1)
    return index, fraction


def arithmetic_matrix(modulus, knots, prime_lists):
    bounds = np.exp(knots[[0, -1]])
    odd_residues = np.zeros((modulus // 2, len(knots) - 2))
    diagonal = np.zeros((len(knots), len(knots)))
    for integers, weights in prime_lists:
        start, stop = np.searchsorted(integers, bounds)
        for chunk in range(start, stop, 262144):
            n = integers[chunk : min(chunk + 262144, stop)]
            coprime = np.gcd(n, modulus) == 1
            n = n[coprime]
            if weights is None:
                von_mangoldt = np.log(n)
            else:
                von_mangoldt = weights[chunk : min(chunk + 262144, stop)][coprime]
            cell, fraction = hat_coordinates(np.log(n), knots)
            weighted = von_mangoldt / np.sqrt(n)
            left = weighted * (1 - fraction)
            right = weighted * fraction
            residue = n % modulus
            representative = np.minimum(residue, modulus - residue)
            orientation = np.where(residue < modulus // 2, 1, -1)
            for index, coefficient in ((cell, left), (cell + 1, right)):
                interior = (index > 0) & (index < len(knots) - 1)
                address = representative[interior], index[interior] - 1
                np.add.at(odd_residues, address, (orientation * coefficient)[interior])
                np.add.at(diagonal, (index, index), coefficient * coefficient)
            np.add.at(diagonal, (cell, cell + 1), left * right)
            np.add.at(diagonal, (cell + 1, cell), left * right)
    return odd_residues.T @ odd_residues - diagonal[1:-1, 1:-1]


def singular_series(modulus, k_max, primes, twin_constant):
    factors = primes[(primes > 2) & (primes <= modulus)]
    factors = factors[modulus % factors == 0].astype(float)
    baseline = twin_constant * np.prod((factors - 1) / (factors - 2))
    densities = np.full(k_max, baseline)
    for prime in primes[(primes > 2) & (primes <= k_max)]:
        if modulus % prime:
            densities[prime - 1 :: prime] *= (prime - 1) / (prime - 2)
    return baseline, densities


def line_integral(shift, direction, knots, x_knots, nodes, weights, right_grid=None):
    """Integrate the products of hats on (x, shift + direction*x)."""
    y_knots, y_points = (knots, x_knots) if right_grid is None else right_grid
    a, b = x_knots[[0, -1]]
    transformed = direction * (y_points - shift)
    low = max(a, np.min(transformed))
    high = min(b, np.max(transformed))
    result = np.zeros((len(knots), len(y_knots)))
    if high <= low:
        return result

    x_breaks = x_knots[(low < x_knots) & (x_knots < high)]
    y_breaks = transformed[(low < transformed) & (transformed < high)]
    cuts = np.sort(np.concatenate(([low, high], x_breaks, y_breaks)))
    half_width = np.diff(cuts) / 2
    x = ((cuts[:-1] + half_width)[:, None] + half_width[:, None] * nodes).ravel()
    y = shift + direction * x
    measure = (half_width[:, None] * weights).ravel() / np.sqrt(x * y)
    row, frac_x = hat_coordinates(np.log(x), knots)
    col, frac_y = hat_coordinates(np.log(y), y_knots)
    for i, wx in ((row, 1 - frac_x), (row + 1, frac_x)):
        for j, wy in ((col, 1 - frac_y), (col + 1, frac_y)):
            np.add.at(result, (i, j), measure * wx * wy)
    return result


def model_matrix(modulus, knots, densities, quadrature):
    nodes, weights = np.polynomial.legendre.leggauss(quadrature)
    x_knots = np.exp(knots)
    result = np.zeros((len(knots), len(knots)))
    for k, density in enumerate(densities, start=1):
        h = k * modulus
        shifted = line_integral(h, 1, knots, x_knots, nodes, weights)
        reflected = line_integral(h, -1, knots, x_knots, nodes, weights)
        result += density * (shifted + shifted.T - reflected)
    result = (result + result.T) / 2
    return result[1:-1, 1:-1]


def hardy_gram(modulus, knots, quadrature):
    nodes, weights = np.polynomial.legendre.leggauss(quadrature)
    step = knots[1] - knots[0]
    alpha = 1 / log(modulus)
    fraction = (nodes + 1) / 2
    r = knots[:-1, None] + step * fraction
    metric = 1 / (np.exp(-2 * alpha * r) + np.exp(-r / 4))
    transformed = np.vstack((1 - fraction + 1 / step, fraction - 1 / step))
    measure = metric * weights * step / (4 * np.pi)
    cells = np.einsum("cq,iq,jq->cij", measure, transformed, transformed)
    gram = np.zeros((len(knots), len(knots)))
    for cell, block in enumerate(cells):
        gram[cell : cell + 2, cell : cell + 2] += block
    return gram[1:-1, 1:-1], cells


def compression(modulus, knots, prime_lists, primes, twin_constant, quadrature):
    k_max = int(2 * np.exp(knots[-1]) / modulus)
    baseline, densities = singular_series(modulus, k_max, primes, twin_constant)
    arithmetic = arithmetic_matrix(modulus, knots, prime_lists)
    model = model_matrix(modulus, knots, densities, quadrature)
    gram, cells = hardy_gram(modulus, knots, quadrature)
    eigenvalues, eigenvectors = eigh(arithmetic - model, gram)
    index = np.argmax(np.abs(eigenvalues))
    vector = np.r_[0, eigenvectors[:, index], 0]
    adjacent = np.column_stack((vector[:-1], vector[1:]))
    energy = np.einsum("ci,cij,cj->c", adjacent, cells, adjacent)
    assert abs(np.sum(energy) - 1) < 1e-9
    return eigenvalues[index] / baseline, energy


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("moduli", nargs="+", type=int)
    parser.add_argument("--lower-ratio", type=float, default=1 / 16)
    parser.add_argument("--upper-ratio", type=float, default=32)
    parser.add_argument("--dimension", type=int, default=95)
    parser.add_argument("--quadrature", type=int, default=16)
    args = parser.parse_args()
    if any(n <= np.exp(10) or n % 2 for n in args.moduli):
        parser.error("use even moduli greater than exp(10)")
    if not 0 < args.lower_ratio < args.upper_ratio:
        parser.error("use positive, increasing ratios")
    if args.dimension < 1 or args.quadrature < 2:
        parser.error("dimension and quadrature must be at least 1 and 2 respectively")

    limit = max(max(args.moduli), int(np.ceil(max(args.moduli) * args.upper_ratio)))
    primes = sieve(limit)
    powers = prime_powers(primes, limit)
    odd = primes[1:].astype(float)
    twin_constant = 2 * np.exp(np.log1p(-1 / (odd - 1) ** 2).sum())
    for modulus in args.moduli:
        offsets = np.linspace(log(args.lower_ratio), log(args.upper_ratio), args.dimension + 2)
        knots = log(modulus) + offsets
        eigenvalue, energy = compression(
            modulus, knots, ((primes, None), powers), primes, twin_constant, args.quadrature
        )
        peak = int(np.argmax(energy))
        quantiles = np.searchsorted(np.cumsum(energy), [0.1, 0.5, 0.9])
        peak_window = np.exp(knots[peak : peak + 2]) / modulus
        scales = np.exp((knots[quantiles] + knots[quantiles + 1]) / 2) / modulus
        print(f"N={modulus:<8} signed eigenvalue/S={eigenvalue:+.9f} "
              f"peak x/N=[{peak_window[0]:.3g}, {peak_window[1]:.3g}] "
              f"energy x/N (10%, 50%, 90%)={scales[0]:.3g}, {scales[1]:.3g}, {scales[2]:.3g}")


if __name__ == "__main__":
    main()
