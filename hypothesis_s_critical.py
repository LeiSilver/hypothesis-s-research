"""Compute Ritz lower estimates for unbalanced critical windows of Hypothesis S."""

import argparse
from math import log, pi, sinh, sqrt

import numpy as np
from scipy.linalg import cholesky, solve_triangular, svdvals

from hypothesis_s_compression import (
    hardy_gram,
    hat_coordinates,
    line_integral,
    prime_powers,
    sieve,
    singular_series,
)
from hypothesis_s_low_high import residue_terms


def rectangle_terms(modulus, low_start, high_start):
    low_primes = sieve(2 * low_start)
    powers, power_weights = prime_powers(low_primes, 2 * low_start)
    integers = np.concatenate((low_primes, powers))
    coefficients = np.concatenate((np.log(low_primes), power_weights))
    selected = (integers >= low_start) & (np.gcd(integers, modulus) == 1)
    integers, coefficients = integers[selected], coefficients[selected]
    residues = {r for n in map(int, integers) for r in (n, -n % modulus)}
    terms = residue_terms(modulus, residues, high_start, 2 * high_start)
    return integers, coefficients, terms


def signed_terms(modulus, residue, terms):
    positive, positive_weights = terms[residue]
    negative, negative_weights = terms[-residue % modulus]
    return np.concatenate((positive, negative)), np.concatenate((positive_weights, -negative_weights))


def arithmetic_rectangle(modulus, low_knots, high_knots, term_data):
    integers, coefficients, terms = term_data
    coefficients = coefficients / np.sqrt(integers)
    result = np.zeros((len(low_knots), len(high_knots)))
    rows, fractions = hat_coordinates(np.log(integers), low_knots)

    for n, weight, row, fraction in zip(integers, coefficients, rows, fractions):
        values, weights = signed_terms(modulus, n, terms)
        weights /= np.sqrt(values)
        columns, offsets = hat_coordinates(np.log(values), high_knots)
        high = np.bincount(columns, weights * (1 - offsets), minlength=len(high_knots))
        high += np.bincount(columns + 1, weights * offsets, minlength=len(high_knots))
        result[row] += weight * (1 - fraction) * high
        result[row + 1] += weight * fraction * high

    return result[1:-1, 1:-1]


def model_rectangle(modulus, low_knots, high_knots, densities, quadrature):
    nodes, weights = np.polynomial.legendre.leggauss(quadrature)
    low_points = np.exp(low_knots)
    high_grid = high_knots, np.exp(high_knots)
    result = np.zeros((len(low_knots), len(high_knots)))
    for k, density in enumerate(densities, start=1):
        shift = k * modulus
        difference = line_integral(shift, 1, low_knots, low_points, nodes, weights, high_grid)
        total = line_integral(shift, -1, low_knots, low_points, nodes, weights, high_grid)
        result += density * (difference - total)
    return result[1:-1, 1:-1]


def matrix_norm(matrix, low_factor, high_factor):
    reduced = solve_triangular(low_factor, matrix, lower=True)
    reduced = solve_triangular(high_factor, reduced.T, lower=True).T
    return float(svdvals(reduced)[0])


def green_arithmetic_norm(modulus, low_start, high_start, term_data):
    """Compute the arithmetic norm on the entire window in the auxiliary metric."""
    integers, coefficients, terms = term_data
    if not len(integers):
        return 0.0
    alpha = 1 / log(modulus)
    kappa = 1 + alpha
    width = log(2)
    green_factor = 2 * pi / (kappa * sinh(kappa * width))
    high_rows = []
    for n in integers:
        values, weights = signed_terms(modulus, n, terms)
        order = values.argsort()
        values, weights = values[order], weights[order]
        positions = np.log(values / high_start)
        rho = weights * values.astype(float) ** (-0.5 - alpha)
        left = rho * np.sinh(kappa * positions)
        right = rho * np.sinh(kappa * (width - positions))
        prefixes = np.r_[0, np.cumsum(left)]
        suffixes = np.r_[np.cumsum(right[::-1])[::-1], 0]
        high_rows.append((positions, left, right, prefixes, suffixes))

    high_gram = np.zeros((len(integers), len(integers)))
    for i, (positions, left, right, _, _) in enumerate(high_rows):
        for j, (other_positions, _, _, prefixes, suffixes) in enumerate(high_rows[: i + 1]):
            splits = np.searchsorted(other_positions, positions, side="right")
            entry = np.dot(right, prefixes[splits]) + np.dot(left, suffixes[splits])
            high_gram[i, j] = high_gram[j, i] = green_factor * entry

    positions = np.log(integers / low_start)
    earlier = np.minimum.outer(positions, positions)
    later = np.maximum.outer(positions, positions)
    low_gram = green_factor * np.sinh(kappa * earlier) * np.sinh(kappa * (width - later))
    eigenvalues, eigenvectors = np.linalg.eigh(low_gram)
    low_root = (eigenvectors * np.sqrt(np.maximum(eigenvalues, 0))) @ eigenvectors.T
    weighted = low_root * (coefficients * integers.astype(float) ** (-0.5 - alpha))
    squared_norm = np.linalg.eigvalsh(weighted @ high_gram @ weighted.T)[-1]
    return sqrt(max(0.0, squared_norm))


def green_window_bounds(modulus, low_start, high_start, term_data, densities):
    """Evaluate analytic model and metric bounds in floating point."""
    arithmetic_norm = green_arithmetic_norm(modulus, low_start, high_start, term_data)
    alpha = 1 / log(modulus)
    kappa = 1 + alpha
    first_shift = max(1, (high_start - 2 * low_start + modulus - 1) // modulus)
    indices = np.arange(first_shift, len(densities) + 1, dtype=np.int64)
    lower_endpoints = indices * modulus - 2 * low_start
    shift_norm = np.linalg.norm(densities[indices - 1] / lower_endpoints)
    exponent = 2 - 2 * alpha
    low_integral = sqrt(((2 * low_start) ** exponent - low_start**exponent) / exponent)
    model_bound = 2 * pi * sqrt(2) * low_integral * high_start**(-alpha) * shift_norm / kappa
    metric_exponent = -2 * (0.125 - alpha)
    low_ratio = 1 + max(low_start**metric_exponent, (2 * low_start) ** metric_exponent)
    high_ratio = 1 + max(high_start**metric_exponent, (2 * high_start) ** metric_exponent)
    return max(0.0, arithmetic_norm - model_bound), sqrt(low_ratio * high_ratio) * (arithmetic_norm + model_bound)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modulus", nargs="+", type=int)
    parser.add_argument("--exponent", type=float, default=0.5, help="Start the low window near N^exponent.")
    parser.add_argument("--dimension", type=int, default=31)
    parser.add_argument("--quadrature", type=int, default=8)
    parser.add_argument("--green", action="store_true", help="Also evaluate bounds over the full test spaces.")
    args = parser.parse_args()
    if not 0 < args.exponent < 1 or args.dimension < 1 or args.quadrature < 1:
        parser.error("Use an exponent between 0 and 1 and positive dimension and quadrature.")
    if any(n < 4 or n % 2 for n in args.modulus):
        parser.error("The moduli must be even integers of at least 4.")

    primes = sieve(max(1_000_000, *args.modulus))
    odd = primes[primes > 2].astype(float)
    twin_constant = 2 * np.exp(np.log1p(-1 / (odd - 1) ** 2).sum())
    for modulus in args.modulus:
        low = max(2, round(modulus**args.exponent))
        high = round(modulus**2 / low)
        if 2 * low >= modulus // 2 or high <= 2 * low:
            parser.error(f"N={modulus} requires disjoint windows and 2X < N/2.")
        low_knots = np.linspace(log(low), log(2 * low), args.dimension + 2)
        high_knots = np.linspace(log(high), log(2 * high), args.dimension + 2)
        baseline, densities = singular_series(modulus, (2 * high + 2 * low) // modulus, primes, twin_constant)
        term_data = rectangle_terms(modulus, low, high)
        arithmetic = arithmetic_rectangle(modulus, low_knots, high_knots, term_data)
        model = model_rectangle(modulus, low_knots, high_knots, densities, args.quadrature)
        low_gram, _ = hardy_gram(modulus, low_knots, args.quadrature)
        high_gram, _ = hardy_gram(modulus, high_knots, args.quadrature)
        factors = cholesky(low_gram, lower=True), cholesky(high_gram, lower=True)
        residual_norm = matrix_norm(arithmetic - model, *factors) / baseline
        model_norm = matrix_norm(model, *factors) / baseline
        print(f"N={modulus} X={low} Y={high} Ritz/S={residual_norm:.8f} model/S={model_norm:.8f}", flush=True)
        if args.green:
            lower, upper = green_window_bounds(modulus, low, high, term_data, densities)
            print(f"  Full-window bounds evaluated in float, divided by S: [{lower/baseline:.8f}, {upper/baseline:.8f}]", flush=True)


if __name__ == "__main__":
    main()
