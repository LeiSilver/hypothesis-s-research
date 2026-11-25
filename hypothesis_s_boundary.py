"""Numerically compress Li and Liu's residual kernel on the Hardy boundary.

The kernel uses Dirichlet L-functions, not a cutoff on the prime-pair sums.
Finite height, quadrature and the Euler products are approximations.
"""

import argparse
from math import ceil, factorial, gcd, log

import numpy as np
from scipy.linalg import eigh
from scipy.special import bernoulli, loggamma

from hypothesis_s_compression import sieve, singular_series


def prime_factors(n):
    factors = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            power = 1
            while n % p == 0:
                n //= p
                power *= p
            factors.append((p, power))
        p += 1 if p == 2 else 2
    if n > 1:
        factors.append((n, n))
    return factors


def powers_mod(generator, order, modulus):
    residues = np.empty(order, dtype=np.int64)
    residue = 1
    for i in range(order):
        residues[i] = residue
        residue = (residue * generator) % modulus
    return residues


def unit_coordinates(modulus, factors):
    """Arrange the units in CRT order and mask the odd Fourier characters."""
    units = np.array(0, dtype=np.int64)
    parity = np.array(0, dtype=np.int8)
    for prime, power in factors:
        if prime == 2:
            components = [(np.array([1, power - 1]), True)] if power > 2 else []
            if power >= 8:
                components.append((powers_mod(5, power // 4, power), False))
            if power == 2:
                components.append((np.array([1]), False))
        else:
            order = power - power // prime
            divisors = [p for p, _ in prime_factors(order)]
            generator = next(
                a for a in range(2, power)
                if gcd(a, power) == 1 and all(pow(a, order // p, power) != 1 for p in divisors)
            )
            components = [(powers_mod(generator, order, power), True)]

        local = np.array(1, dtype=np.int64)
        local_parity = np.array(0, dtype=np.int8)
        for residues, changes_sign in components:
            local = (local[..., None] * residues) % power
            indices = np.arange(len(residues), dtype=np.int64)
            local_parity = local_parity[..., None] ^ ((indices & 1) * changes_sign)
        quotient = modulus // power
        idempotent = quotient * pow(quotient, -1, power)
        flat_units = (units.reshape(-1, 1) + idempotent * local.ravel()) % modulus
        flat_parity = parity.reshape(-1, 1) ^ local_parity.ravel()
        units = flat_units.reshape(units.shape + local.shape)
        parity = flat_parity.reshape(units.shape)
    return units, parity.astype(bool)


class HurwitzGrid:
    """Euler–Maclaurin evaluation with derivatives in the first argument."""

    def __init__(self, offsets, terms, corrections):
        self.logs = np.log(np.arange(terms)[:, None] + offsets)
        self.edge = np.log(terms + offsets)
        numbers = bernoulli(2 * corrections)
        self.coefficients = [numbers[2 * k] / factorial(2 * k) for k in range(1, corrections + 1)]

    def evaluate(self, s, order):
        terms = np.exp(-s * self.logs)
        jet = [np.sum(terms, axis=0)]
        if order >= 1:
            jet.append(-np.sum(terms * self.logs, axis=0))
        if order == 2:
            jet.append(np.sum(terms * self.logs**2, axis=0))

        integral = np.exp((1 - s) * self.edge) / (s - 1)
        remainder = np.exp(-s * self.edge) / 2
        integral_derivative = -self.edge - 1 / (s - 1)
        jet[0] += integral + remainder
        if order >= 1:
            jet[1] += integral * integral_derivative - remainder * self.edge
        if order == 2:
            jet[2] += integral * (integral_derivative**2 + (s - 1)**-2) + remainder * self.edge**2

        rising = 1
        log_derivative = 0
        reciprocal_squares = 0
        index = 0
        for k, coefficient in enumerate(self.coefficients, start=1):
            while index < 2 * k - 1:
                factor = s + index
                rising *= factor
                log_derivative += 1 / factor
                reciprocal_squares += factor**-2
                index += 1
            term = coefficient * rising * np.exp((1 - s - 2 * k) * self.edge)
            derivative = log_derivative - self.edge
            jet[0] += term
            if order >= 1:
                jet[1] += term * derivative
            if order == 2:
                jet[2] += term * (derivative**2 - reciprocal_squares)
        return jet


def odd_log_derivatives(s, modulus, shape, odd, hurwitz):
    value, derivative = hurwitz.evaluate(0.5 + s, order=1)
    sums = np.fft.fftn(value.reshape(shape))[odd]
    derivative_sums = np.fft.fftn(derivative.reshape(shape))[odd]
    return derivative_sums / sums - log(modulus)


def diagonal_and_beta(w, modulus, primes, factors, series, zeta):
    logs = np.log(primes)
    r = np.exp(-(1 + w) * logs)
    z, dz, ddz = (a.item() for a in zeta.evaluate(1 + w, order=2))
    diagonal = ddz / z - (dz / z)**2 - np.sum((logs * r / (1 - r))**2)
    local_logs = np.log([p for p, _ in factors])
    local_r = np.exp(-(1 + w) * local_logs)
    diagonal -= np.sum(local_logs**2 * local_r / (1 - local_r))

    permitted = primes[(primes > 2) & (modulus % primes != 0)]
    p_to_w = np.exp(-w * np.log(permitted))
    adjustment = (2 * p_to_w - p_to_w**2) / (permitted * (permitted - 2))
    euler = series * np.prod(1 - local_r) * np.exp(np.log1p(adjustment).sum())
    reflected = zeta.evaluate(1 - w, order=0)[0].item()
    beta = np.exp(w * log(np.pi / modulus)) * z * reflected * euler
    return diagonal, beta


def boundary_matrix(modulus, height, max_step, primes, twin_constant, terms, corrections):
    factors = prime_factors(modulus)
    units, odd = unit_coordinates(modulus, factors)
    hurwitz = HurwitzGrid(units.ravel() / modulus, terms, corrections)
    zeta = HurwitzGrid(np.array([1.0]), terms, corrections)
    count = ceil(2 * height / max_step)
    step = 2 * height / count
    offsets = (np.arange(count) + 0.5) * step - height
    sides = (1 / log(modulus), 1 / 8)
    samples = np.repeat(sides, count) + 1j * np.tile(offsets, 2)
    g = np.stack([
        odd_log_derivatives(s, modulus, units.shape, odd, hurwitz) for s in samples
    ])
    kernel = g @ g.conj().T / np.count_nonzero(odd)

    series, _ = singular_series(modulus, 0, primes, twin_constant)
    gamma = np.exp(loggamma((1.5 - samples) / 2) - loggamma((1.5 + samples) / 2))
    w_index = (count - 1) + np.arange(count)[:, None] - np.arange(count)
    differences = np.arange(-count + 1, count) * step
    for i in range(2):
        for j in range(i, 2):
            data = np.array([
                diagonal_and_beta(sides[i] + sides[j] + 1j * t, modulus, primes, factors, series, zeta)
                for t in differences
            ])
            si = slice(i * count, (i + 1) * count)
            sj = slice(j * count, (j + 1) * count)
            block = data[w_index, 0] + data[w_index, 1] * np.outer(gamma[si], gamma[sj].conj())
            kernel[si, sj] -= block
            if i != j:
                kernel[sj, si] -= block.conj().T

    kernel *= step / np.outer(1 + samples, 1 + samples.conj())
    return (kernel + kernel.conj().T) / 2, samples, step, series


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("moduli", nargs="+", type=int)
    parser.add_argument("--height", type=float, default=8)
    parser.add_argument("--step", type=float, default=0.1)
    parser.add_argument("--prime-limit", type=int, default=200000)
    parser.add_argument("--terms", type=int)
    parser.add_argument("--corrections", type=int, default=12)
    args = parser.parse_args()
    if any(n <= np.exp(10) or n % 2 for n in args.moduli):
        parser.error("use even moduli greater than exp(10)")
    if args.height <= 0 or args.step <= 0 or args.corrections < 1:
        parser.error("height, step and corrections must be positive")
    terms = args.terms if args.terms is not None else ceil(2 * args.height) + 16
    if terms < 1 or args.prime_limit < 3:
        parser.error("use at least one Euler–Maclaurin summand and a prime limit of at least 3")

    primes = sieve(max(args.prime_limit, max(args.moduli)))
    odd_primes = primes[primes > 2].astype(float)
    twin_constant = 2 * np.exp(np.log1p(-1 / (odd_primes - 1)**2).sum())
    for modulus in args.moduli:
        matrix, samples, step, series = boundary_matrix(
            modulus, args.height, args.step, primes, twin_constant, terms, args.corrections
        )
        eigenvalues, vectors = eigh(matrix)
        extreme = np.argmax(np.abs(eigenvalues))
        direction = vectors[:, extreme]
        on_left = np.sum(np.abs(direction[:len(direction) // 2])**2)
        weighted_height = np.sum(np.abs(direction)**2 * abs(samples.imag))
        print(f"N={modulus:<8} points={len(samples):<5} step={step:.5g}  "
              f"min/S={eigenvalues[0]/series:+.8f}  max/S={eigenvalues[-1]/series:+.8f}  "
              f"left mass={on_left:.3f}  mean |height|={weighted_height:.3f}")


if __name__ == "__main__":
    main()
