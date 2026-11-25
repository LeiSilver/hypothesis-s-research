"""Enclose a full unbalanced block using interval arithmetic and exact integers."""

import argparse
from fractions import Fraction
from math import isqrt

import numpy as np
from mpmath import iv
from mpmath.libmp import round_ceiling, round_floor, to_int

from hypothesis_s_boundary import prime_factors
from hypothesis_s_compression import sieve
from hypothesis_s_critical import rectangle_terms
from hypothesis_s_witness import SCALE, as_interval, density_bounds, twin_constant_bounds


FIXED_SCALE = 1 << 70


def enclosing_integer(interval):
    low_bits, high_bits = (interval * FIXED_SCALE)._mpi_
    lower = int(to_int(low_bits, round_floor))
    upper = int(to_int(high_bits, round_ceiling))
    center = (lower + upper) // 2
    return center, upper - center


def power_bases(primes, lower, upper):
    result = {}
    for prime in map(int, primes):
        power = prime * prime
        if power > upper:
            break
        while power <= upper:
            if power >= lower:
                result[power] = prime
            power *= prime
    return result


class Window:
    """Dirichlet Green kernel for (2 pi)^-1 int w(r)|F'(r)|^2 dr."""

    def __init__(self, start, alpha):
        self.start = start
        self.rate = 2 * alpha
        self.start_power = iv.exp(-self.rate * iv.ln(start))
        self.start_root = 1 / iv.sqrt(iv.sqrt(start))
        self.length = self._position(iv.ln(2 * start), iv.sqrt(2 * start))
        self.factor = 2 * iv.pi / self.length

    def _position(self, logarithm, root):
        power = iv.exp(-self.rate * logarithm)
        return (self.start_power - power) / self.rate + 4 * (self.start_root - 1 / iv.sqrt(root))

    def coefficients(self, values, signs, bases):
        left, right = [], []
        left_error = right_error = 0
        for value, sign in zip(map(int, values), map(int, signs)):
            logarithm = iv.ln(value)
            base = bases.get(value)
            root = iv.sqrt(value)
            position = self._position(logarithm, root)
            weight = sign * (logarithm if base is None else iv.ln(base)) / root
            left_value, radius = enclosing_integer(weight * position)
            left.append(left_value)
            left_error += radius
            right_value, radius = enclosing_integer(weight * (self.length - position))
            right.append(right_value)
            right_error += radius
        return np.array(left, dtype=object), np.array(right, dtype=object), left_error, right_error

    def l2_metric_ratio(self):
        """Bound the squared Hardy norm divided by the derivative norm."""
        endpoint = 2 * self.start
        inverse_start = self.start_power + self.start_root
        inverse_end = iv.exp(-self.rate * iv.ln(endpoint)) + 1 / iv.sqrt(iv.sqrt(endpoint))
        # w'/w is a weighted mean of rate and 1/4, hence at most their sum.
        return 1 + (1 + self.rate + iv.mpf(1) / 4) * inverse_start / inverse_end * (iv.ln(2) / iv.pi) ** 2


def gram_entry(integer, error, green_factor):
    return enclosing_integer(green_factor * iv.mpf([int(integer) - error, int(integer) + error]) / FIXED_SCALE**2)


def low_gram(window, values, bases):
    left, right, left_error, right_error = window.coefficients(values, np.ones(len(values), dtype=int), bases)
    product_error = max(map(abs, left)) * right_error + max(map(abs, right)) * left_error + left_error * right_error
    matrix = np.empty((len(values), len(values)), dtype=object)
    error = 0
    for i in range(len(values)):
        for j in range(i + 1):
            entry, radius = gram_entry(left[j] * right[i], product_error, window.factor)
            matrix[i, j] = matrix[j, i] = entry
            error = max(error, radius)
    return matrix, error


def high_gram(modulus, window, residues, terms, bases):
    rows = []
    max_left = max_right = max_left_error = max_right_error = 0
    for n in residues:
        positive = terms[n][0]
        negative = terms[-n % modulus][0]
        values = np.concatenate((positive, negative))
        signs = np.concatenate((np.ones(len(positive), dtype=int), -np.ones(len(negative), dtype=int)))
        order = values.argsort()
        values, signs = values[order], signs[order]
        left, right, left_error, right_error = window.coefficients(values, signs, bases)
        max_left = max(max_left, sum(map(abs, left)))
        max_right = max(max_right, sum(map(abs, right)))
        max_left_error = max(max_left_error, left_error)
        max_right_error = max(max_right_error, right_error)
        rows.append((values, left, right, np.r_[0, np.cumsum(left)], np.r_[np.cumsum(right[::-1])[::-1], 0]))

    product_error = 2 * (max_left * max_right_error + max_right * max_left_error + max_left_error * max_right_error)
    matrix = np.empty((len(rows), len(rows)), dtype=object)
    error = 0
    for i, (values, left, right, _, _) in enumerate(rows):
        for j, (other, _, _, prefix, suffix) in enumerate(rows[: i + 1]):
            splits = np.searchsorted(other, values, side="right")
            dot = np.dot(right, prefix[splits]) + np.dot(left, suffix[splits])
            entry, radius = gram_entry(dot, product_error, window.factor)
            matrix[i, j] = matrix[j, i] = entry
            error = max(error, radius)
    return matrix, error


def matrix_product(left, right, left_error, right_error):
    error = left_error * max(np.abs(right).sum(axis=0)) + right_error * max(np.abs(left).sum(axis=1))
    error += len(left) * left_error * right_error
    return left @ right, error


def trace_square(matrix, error, scale):
    center = int((matrix * matrix.T).sum())
    radius = 2 * error * int(np.abs(matrix).sum()) + matrix.size * error**2
    return iv.mpf([max(0, center - radius), center + radius]) / scale**2


def arithmetic_bounds(low, high, low_error, high_error):
    # The eigenvalues of the Gram product are the squared singular values.
    product, error = matrix_product(low, high, low_error, high_error)
    second = trace_square(product, error, FIXED_SCALE**2)
    squared, error = matrix_product(product, product, error, error)
    fourth = trace_square(squared, error, FIXED_SCALE**4)
    if second.b == 0:
        return iv.mpf(0), iv.mpf(0)
    lower = iv.sqrt(iv.sqrt(fourth.a / second.b))
    upper = iv.sqrt(iv.sqrt(iv.sqrt(fourth.b)))
    return lower, upper


def continuous_upper(modulus, low, high, alpha):
    """Bound the normalized signed model via disjoint shift intervals."""
    first = max(1, (high - 2 * low + modulus - 1) // modulus)
    last = (2 * high + 2 * low) // modulus
    shift_square = iv.mpf(0)
    for k in range(first, last + 1):
        ratio = Fraction(1, k * modulus - 2 * low)
        for prime, _ in prime_factors(k):
            if prime > 2 and modulus % prime != 0:
                ratio *= Fraction(prime - 1, prime - 2)
        shift_square += as_interval(ratio) ** 2
    weight_low = iv.exp(-2 * alpha * iv.ln(low)) + 1 / iv.sqrt(iv.sqrt(low))
    weight_high = iv.exp(-2 * alpha * iv.ln(high)) + 1 / iv.sqrt(iv.sqrt(high))
    return 2 * iv.sqrt(3) * low * iv.ln(2) * iv.sqrt(weight_low * weight_high * shift_square)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modulus", nargs="?", type=int, default=2**22)
    parser.add_argument("--low-start", type=int)
    parser.add_argument("--high-start", type=int)
    args = parser.parse_args()
    modulus = args.modulus
    if modulus < 4 or modulus % 2:
        parser.error("The modulus must be an even integer of at least 4.")
    low = isqrt(modulus) if args.low_start is None else args.low_start
    if low < 2 or 4 * low >= modulus:
        parser.error("The low window needs 2 <= X < N/4.")
    high = (modulus**2 + low // 2) // low if args.high_start is None else args.high_start
    if not 4 * low < high < 2**62:
        parser.error("The high window needs 4X < Y < 2^62.")

    iv.dps = 45
    alpha = 1 / iv.ln(modulus)
    low_window, high_window = Window(low, alpha), Window(high, alpha)
    values, _, terms = rectangle_terms(modulus, low, high)
    values = np.sort(values)
    primes = sieve(isqrt(2 * high))
    print(f"N={modulus} X={low} Y={high}, low terms={len(values)}", flush=True)
    if len(values):
        low_matrix, low_error = low_gram(low_window, values, power_bases(primes, low, 2 * low))
        high_matrix, high_error = high_gram(modulus, high_window, values, terms, power_bases(primes, high, 2 * high))
        arithmetic_lower, arithmetic_upper = arithmetic_bounds(low_matrix, high_matrix, low_error, high_error)
    else:
        arithmetic_lower = arithmetic_upper = iv.mpf(0)

    twin = twin_constant_bounds(sieve(100_000), 100_000)
    singular_low, singular_high = density_bounds(modulus, twin)
    singular = iv.mpf([singular_low, singular_high]) / SCALE
    model = continuous_upper(modulus, low, high, alpha)
    ratio = iv.sqrt(low_window.l2_metric_ratio() * high_window.l2_metric_ratio())
    lower = arithmetic_lower / (ratio * singular) - model
    upper = arithmetic_upper / singular + model
    print(f"Normalized continuous model upper: {model.b}")
    print(f"Normalized full-window norm under GRH(N): {iv.mpf([max(0, lower.a), upper.b])}")


if __name__ == "__main__":
    main()
