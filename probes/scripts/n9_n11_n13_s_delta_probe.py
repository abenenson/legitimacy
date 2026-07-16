"""Reproduce the S_delta scale-jump tables for n = 9, 11, 13.

Source reports:

- d1d1052 (n=9 report)
- 3a59ccb (n=11/n=13 report)
"""

from __future__ import annotations

import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from probes.scripts.archetypes import family_for_n, format_exact, headline_metrics


TAU = 17.0 / 20.0


def print_table(n: int) -> None:
    print(f"# n = {n}")
    print()
    print("| archetype | spectralGap(G) | cv(G) at sig_n | S_delta(G) = lambda2 * cv | 17/20 pass? |")
    print("|---|---:|---:|---:|:---:|")

    negatives = []
    positives = []
    for archetype in family_for_n(n):
        metrics = headline_metrics(archetype)
        s_delta = metrics["S_delta"]
        if s_delta >= TAU:
            positives.append(s_delta)
        else:
            negatives.append(s_delta)
        print(
            "| {name} | {gap:.4f} | {cv} = {cvd:.10f} | {sd:.10f} | {passed} |".format(
                name=archetype.name,
                gap=metrics["lambda2"],
                cv=format_exact(metrics["cv_exact"]),
                cvd=metrics["cv_float"],
                sd=s_delta,
                passed="yes" if s_delta >= TAU else "no",
            )
        )

    print()
    print(
        "Admissible threshold window: "
        f"{max(negatives):.10f} < tau <= {min(positives):.10f}"
    )
    print(f"17/20 = {TAU:.4f} lies inside that window.")


def main() -> None:
    for n in (9, 11, 13):
        print_table(n)
        if n != 13:
            print()


if __name__ == "__main__":
    main()
