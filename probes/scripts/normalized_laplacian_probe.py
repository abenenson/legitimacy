"""Reproduce the normalized-Laplacian scaling tables from the 2026-04-23 report.

Source report:

"""

from __future__ import annotations

import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from probes.scripts.archetypes import (
    all_archetypes_scale,
    family_for_n,
    format_decimal,
    format_exact,
    gaussian_channel_mi,
    headline_metrics,
    sig,
    spearman,
)


TAU = 17.0 / 20.0
WELL_CONNECTED = {
    "uniK5": True,
    "asymK5": True,
    "nearPath5": True,
    "wheel5": True,
    "bottleneck5": False,
    "uniK7": True,
    "asymK7": True,
    "nearPath7": True,
    "bottleneck7_bi": False,
    "bottleneck7_tri": False,
    "hubSpokeHierarchy7": False,
    "nestedHierarchy7": False,
    "uniK9": True,
    "asymK9": True,
    "nearPath9": True,
    "bottleneck9_bi": False,
    "hubSpokeHierarchy9": False,
    "nestedHierarchy9": False,
    "wheel9": True,
    "uniK11": True,
    "asymK11": True,
    "nearPath11": True,
    "bottleneck11_bi": False,
    "hubSpokeHierarchy11": False,
    "nestedHierarchy11": False,
    "wheel11": True,
    "uniK13": True,
    "asymK13": True,
    "nearPath13": True,
    "bottleneck13_bi": False,
    "hubSpokeHierarchy13": False,
    "nestedHierarchy13": False,
    "wheel13": True,
}


def make_rows() -> list[dict[str, object]]:
    rows = []
    for archetype in all_archetypes_scale():
        metrics = headline_metrics(archetype)
        rows.append(
            {
                "n": archetype.n,
                "archetype": archetype.name,
                "lambda2": metrics["lambda2"],
                "lambda2_tilde": metrics["lambda2_tilde"],
                "cv_exact": metrics["cv_exact"],
                "cv_float": metrics["cv_float"],
                "S_delta": metrics["S_delta"],
                "wc": WELL_CONNECTED[archetype.name],
                "mi_proxy": gaussian_channel_mi(archetype.weights, 100.0),
            }
        )
    return rows


def print_full_table(rows: list[dict[str, object]]) -> None:
    print("# Normalized-Laplacian cross-scale table")
    print()
    print("| n | archetype | lambda2(L) | lambda2(L_tilde) | cv | S_delta | wc? | S_delta >= 17/20? |")
    print("|---:|---|---:|---:|---:|---:|:---:|:---:|")
    for row in rows:
        print(
            "| {n} | {archetype} | {l2:.4f} | {l2t:.4f} | {cv:.4f} | {sd:.4f} | {wc} | {pass_tau} |".format(
                n=row["n"],
                archetype=row["archetype"],
                l2=row["lambda2"],
                l2t=row["lambda2_tilde"],
                cv=row["cv_float"],
                sd=row["S_delta"],
                wc="yes" if row["wc"] else "no",
                pass_tau="yes" if row["S_delta"] >= TAU else "no",
            )
        )


def print_threshold_windows(rows: list[dict[str, object]]) -> None:
    print()
    print("| n | pos-floor | neg-ceiling | admissible window | separates? |")
    print("|---:|---:|---:|---|:---:|")
    for n in (5, 7, 9, 11, 13):
        sub = [row for row in rows if row["n"] == n]
        pos_floor = min(row["lambda2_tilde"] for row in sub if row["wc"])
        neg_ceiling = max(row["lambda2_tilde"] for row in sub if not row["wc"])
        if neg_ceiling < pos_floor:
            window = f"({neg_ceiling:.6f}, {pos_floor:.6f}]"
            separates = "yes"
        else:
            window = "--"
            separates = "no"
        print(f"| {n} | {pos_floor:.6f} | {neg_ceiling:.6f} | {window} | {separates} |")


def print_correlations(rows: list[dict[str, object]]) -> None:
    s_delta = [row["S_delta"] for row in rows]
    lambda2_tilde = [row["lambda2_tilde"] for row in rows]
    mi = [row["mi_proxy"] for row in rows]

    print()
    print("Full 33-archetype pool, Gaussian-channel MI proxy at SNR = 100:")
    print(f"- Spearman(S_delta, MI_proxy) = {spearman(s_delta, mi):.3f}")
    print(f"- Spearman(lambda2(L_tilde), MI_proxy) = {spearman(lambda2_tilde, mi):.3f}")

    print()
    print("| n | N | Spearman(S_delta, MI) | Spearman(lambda2(L_tilde), MI) |")
    print("|---:|---:|---:|---:|")
    for n in (5, 7, 9, 11, 13):
        sub = [row for row in rows if row["n"] == n]
        print(
            f"| {n} | {len(sub)} | "
            f"{spearman([row['S_delta'] for row in sub], [row['mi_proxy'] for row in sub]):.3f} | "
            f"{spearman([row['lambda2_tilde'] for row in sub], [row['mi_proxy'] for row in sub]):.3f} |"
        )


def print_mismatch(rows: list[dict[str, object]]) -> None:
    by_name = {row["archetype"]: row for row in rows}
    print()
    print("n = 7 MI-proxy mismatch highlighted in the report:")
    print(f"- nearPath7: lambda2(L_tilde) = {by_name['nearPath7']['lambda2_tilde']:.4f}, I_proxy = {by_name['nearPath7']['mi_proxy']:.2f}")
    print(f"- bottleneck7_bi: lambda2(L_tilde) = {by_name['bottleneck7_bi']['lambda2_tilde']:.4f}, I_proxy = {by_name['bottleneck7_bi']['mi_proxy']:.2f}")
    print(f"- hubSpokeHierarchy7: lambda2(L_tilde) = {by_name['hubSpokeHierarchy7']['lambda2_tilde']:.4f}, I_proxy = {by_name['hubSpokeHierarchy7']['mi_proxy']:.2f}")


def main() -> None:
    rows = make_rows()
    print_full_table(rows)
    print_threshold_windows(rows)
    print_correlations(rows)
    print_mismatch(rows)


if __name__ == "__main__":
    main()
