"""Reproduce the Kemeny-indicator table from the 2026-04-23 report.

Source report:

Original lost scripts referenced by the report:
- /tmp/probe/kemeny_full.py
- /tmp/probe/identity_tests.py
"""

from __future__ import annotations

import pathlib
import sys

import sympy as sp

ROOT = pathlib.Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from probes.scripts.archetypes import (
    all_archetypes_n5,
    cv_value,
    format_decimal,
    format_exact,
    kemeny_constant,
    remove_node,
    sig,
)


def fmt_optional(value: sp.Expr | None) -> str:
    if value is None:
        return "disconnected"
    if isinstance(value, sp.Rational):
        return f"{format_exact(value)} = {format_decimal(value)}"
    return format_decimal(value)


def fmt_delta(value: sp.Expr | None) -> str:
    if value is None:
        return "n/a"
    return format_decimal(value)


def main() -> None:
    signal = sig(5)
    base_rows: list[dict[str, object]] = []
    indicator_rows: list[dict[str, object]] = []

    for archetype in all_archetypes_n5():
        cv = sp.simplify(cv_value(archetype.weights, signal))
        k_full = kemeny_constant(archetype.weights)
        removed = [kemeny_constant(remove_node(archetype.weights, i)) for i in range(archetype.n)]
        kappas = [None if rk is None else sp.simplify(k_full - rk) for rk in removed]

        max_abs = max(abs(float(sp.N(v, 50))) for v in kappas if v is not None)
        ratio = float(sp.N(cv, 50)) / max_abs

        base_rows.append(
            {
                "archetype": archetype.name,
                "cv": cv,
                "k_full": k_full,
                "removed": removed,
            }
        )
        indicator_rows.append(
            {
                "archetype": archetype.name,
                "kappas": kappas,
                "max_abs": max_abs,
                "ratio": ratio,
            }
        )

    print("# Kemeny-indicator exact table")
    print()
    print("| archetype | cv(G, sig5) | K(P) | K(P^(-0)) | K(P^(-1)) | K(P^(-2)) | K(P^(-3)) | K(P^(-4)) |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|")
    for row in base_rows:
        removed = row["removed"]
        print(
            "| {archetype} | {cv} = {cv_dec} | {k_full} = {k_dec} | {r0} | {r1} | {r2} | {r3} | {r4} |".format(
                archetype=row["archetype"],
                cv=format_exact(row["cv"]),
                cv_dec=format_decimal(row["cv"]),
                k_full=format_exact(row["k_full"]),
                k_dec=format_decimal(row["k_full"]),
                r0=fmt_optional(removed[0]),
                r1=fmt_optional(removed[1]),
                r2=fmt_optional(removed[2]),
                r3=fmt_optional(removed[3]),
                r4=fmt_optional(removed[4]),
            )
        )

    print()
    print("| archetype | kappa_0 | kappa_1 | kappa_2 | kappa_3 | kappa_4 | max_k |kappa_k| | cv / max|kappa| |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|")
    for row in indicator_rows:
        kappas = row["kappas"]
        print(
            "| {archetype} | {k0} | {k1} | {k2} | {k3} | {k4} | {mx:.4f} | {ratio:.4f} |".format(
                archetype=row["archetype"],
                k0=fmt_delta(kappas[0]),
                k1=fmt_delta(kappas[1]),
                k2=fmt_delta(kappas[2]),
                k3=fmt_delta(kappas[3]),
                k4=fmt_delta(kappas[4]),
                mx=row["max_abs"],
                ratio=row["ratio"],
            )
        )

    print()
    print("Constant-signal obstruction: for sig_const = (1,1,1,1,1), cv(G, sig_const) = 0 for every archetype,")
    print("while K(P) and K(P^(-k)) remain graph-only and generally nonzero.")


if __name__ == "__main__":
    main()
