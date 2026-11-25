"""Measure fixed-residue directions in the low-to-high block of Hypothesis S."""

import argparse
from math import gcd, isqrt, log, pi, prod, sinh, sqrt

import numpy as np

from hypothesis_s_boundary import prime_factors
from hypothesis_s_compression import prime_powers, sieve


def progression_primes(modulus, residue, lower, upper, inverse_steps):
    first = (lower - residue + modulus - 1) // modulus
    last = (upper - residue) // modulus
    candidates = np.ones(last - first + 1, dtype=bool)
    for prime, inverse in inverse_steps:
        offset = (-residue * inverse - first) % prime
        candidates[offset::prime] = False
    return (first + np.flatnonzero(candidates)) * modulus + residue


def residue_terms(modulus, residues, lower, upper):
    """Enumerate every nonzero von Mangoldt term in the requested unit classes."""
    if lower <= isqrt(upper):
        raise ValueError("The window must lie above its trial division primes.")
    if any(gcd(residue, modulus) != 1 for residue in residues):
        raise ValueError("The residue classes must be coprime to the modulus.")
    base_primes = sieve(isqrt(upper))
    inverse_steps = [
        (p, pow(modulus, -1, p)) for p in map(int, base_primes) if modulus % p
    ]
    powers, weights = prime_powers(base_primes, upper)
    start = powers.searchsorted(lower)
    powers, weights = powers[start:], weights[start:]
    power_residues = powers % modulus

    terms = {}
    for residue in residues:
        primes = progression_primes(modulus, residue, lower, upper, inverse_steps)
        matching_powers = power_residues == residue
        integers = np.concatenate((primes, powers[matching_powers]))
        weights_in_class = np.concatenate((np.log(primes), weights[matching_powers]))
        order = integers.argsort()
        terms[residue] = integers[order], weights_in_class[order]
    return terms


def dual_norm(modulus, terms, residue, lower, upper):
    """Compute the Dirichlet Green-kernel dual norm for one signed pair."""
    positive, positive_weights = terms[residue]
    negative, negative_weights = terms[-residue % modulus]
    integers = np.concatenate((positive, negative))
    weights = np.concatenate((positive_weights, -negative_weights))
    order = integers.argsort()
    integers, weights = integers[order], weights[order]
    alpha = 1 / log(modulus)
    kappa = 1 + alpha
    length = log(upper / lower)
    position = np.log(integers / lower)
    rho = weights * integers.astype(float) ** (-0.5 - alpha)

    left = rho * np.sinh(kappa * position)
    right = rho * np.sinh(kappa * (length - position))
    energy = np.sum(right * (2 * np.cumsum(left) - left))
    return sqrt(2 * pi * max(energy, 0.0) / (kappa * sinh(kappa * length)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modulus", nargs="+", type=int)
    parser.add_argument("--residues", nargs="+", type=int, default=[3, 5, 7, 11, 13])
    parser.add_argument("--scale", type=float, default=1.0, help="Window start divided by N^2.")
    args = parser.parse_args()
    if args.scale <= 0 or any(modulus < 3 for modulus in args.modulus):
        parser.error("The scale must be positive and the moduli at least 3.")

    for modulus in args.modulus:
        lower = round(modulus**2 * args.scale)
        upper = 2 * lower
        representatives = sorted({
            min(a % modulus, -a % modulus) for a in args.residues if gcd(a, modulus) == 1
        })
        residues = {r for a in representatives for r in (a, -a % modulus)}
        terms = residue_terms(modulus, residues, lower, upper)
        normalization = prod(p / (p - 1) for p, _ in prime_factors(modulus))
        values = " ".join(
            f"{a}={dual_norm(modulus, terms, a, lower, upper) / normalization:.8f}"
            for a in representatives
        )
        print(f"N={modulus} X={lower} dual/(N/phi(N)): {values}", flush=True)


if __name__ == "__main__":
    main()
