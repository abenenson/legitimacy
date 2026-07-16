"""Reconstruct the analytical adversarial-MI pathway from the 2026-04-23 2c probe.

Source report:

Original lost scripts referenced by the report:
- run_probe.py
- deep_probe.py
- final_probe.py

This reconstruction focuses on the exact closed-form Gaussian-channel path
(`final_probe.py`) named in the report. That path is fully reproducible from
the published formulas using only numpy + sympy, and it reproduces the report's
headline correlation table exactly.
"""

from __future__ import annotations

import pathlib
import sys

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from probes.scripts.archetypes import (
    all_archetypes_n5,
    all_archetypes_n7,
    cv_value,
    gaussian_channel_mi,
    headline_metrics,
    random_walk_matrix,
    sig,
    spearman,
    sympy_to_numpy,
)


def matrix_power_mi(weights, power: int, sigma_noise: float) -> float:
    m = sympy_to_numpy(random_walk_matrix(weights))
    mk = np.linalg.matrix_power(m, power)
    sigmas = np.linalg.svd(mk, compute_uv=False)
    snr = 1.0 / (sigma_noise * sigma_noise)
    return float(0.5 * np.sum(np.log1p(snr * sigmas * sigmas)))


def print_spectral_rows() -> None:
    print("# n = 5 spectral invariants")
    print()
    print("| archetype | lambda2(L) | lambda2(L_tilde) | cv | S_delta |")
    print("|---|---:|---:|---:|---:|")
    for archetype in all_archetypes_n5():
        metrics = headline_metrics(archetype)
        print(
            f"| {archetype.name} | {metrics['lambda2']:.4f} | {metrics['lambda2_tilde']:.4f} | "
            f"{metrics['cv_float']:.4f} | {metrics['S_delta']:.4f} |"
        )


def print_exact_model_d_tables() -> None:
    for n, family in ((5, all_archetypes_n5()), (7, all_archetypes_n7())):
        print()
        print(f"# n = {n}, exact Model-D Gaussian-channel MI at sigma = 0.1")
        print()
        print("| archetype | S_delta | lambda2(L_tilde) | I_exact |")
        print("|---|---:|---:|---:|")
        for archetype in family:
            metrics = headline_metrics(archetype)
            mi = gaussian_channel_mi(archetype.weights, 100.0)
            print(
                f"| {archetype.name} | {metrics['S_delta']:.4f} | "
                f"{metrics['lambda2_tilde']:.4f} | {mi:.4f} |"
            )


def print_correlation_table() -> None:
    family = all_archetypes_n5() + all_archetypes_n7()
    base = [headline_metrics(archetype) for archetype in family]
    s_delta = [row["S_delta"] for row in base]
    ltilde = [row["lambda2_tilde"] for row in base]
    hybrid = [row["lambda2_tilde"] * row["cv_float"] for row in base]

    print()
    print("# Combined n = 5 + 7 exact Spearman table")
    print()
    print("| sigma_noise | Spearman(S_delta, MI) | Spearman(lambda2(L_tilde), MI) | Spearman(lambda2(L_tilde) * cv, MI) |")
    print("|---:|---:|---:|---:|")
    for sigma in (0.01, 0.1, 1.0):
        snr = 1.0 / (sigma * sigma)
        mi = [gaussian_channel_mi(archetype.weights, snr) for archetype in family]
        hybrid_value = f"{spearman(hybrid, mi):.3f}" if sigma == 0.1 else "--"
        print(
            f"| {sigma:.2f} | {spearman(s_delta, mi):.3f} | "
            f"{spearman(ltilde, mi):.3f} | {hybrid_value} |"
        )


def print_model_notes() -> None:
    print()
    print("Analytical notes for the four adversary classes named in the report:")
    print("- Model A (partial observation): graph-independent by construction; no finite exact continuous-prior MI closed form without adding observation noise.")
    print("- Model B (corrupted raw observation): graph-independent closed form, I = (n/2) * log(1 + 1/sigma^2).")
    print("- Model C (delayed governance observation): exact Gaussian-channel MI is computed by replacing M with M^k.")
    print("- Models D and E: exact Gaussian-channel MI coincide because the MMSE estimate is a deterministic function of y = M s + eta.")

    print()
    print("Graph-independent Model-B baselines at sigma = 1.0:")
    print(f"- n = 5: {(5 / 2.0) * np.log(2.0):.4f} nats")
    print(f"- n = 7: {(7 / 2.0) * np.log(2.0):.4f} nats")

    print()
    print("Model-C delayed example at k = 2, sigma = 0.1:")
    for archetype in all_archetypes_n5():
        print(f"- {archetype.name}: {matrix_power_mi(archetype.weights, power=2, sigma_noise=0.1):.4f} nats")


def main() -> None:
    print_spectral_rows()
    print_exact_model_d_tables()
    print_correlation_table()
    print_model_notes()


if __name__ == "__main__":
    main()
