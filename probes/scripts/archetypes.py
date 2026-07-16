"""Canonical archetype constructors and shared probe utilities.

Source reports:

The n=5 and n=7 families match the committed Lean definitions in
`lean/Legitimacy/Spectral/ConcreteGraphs.lean`. The n=9/11/13 odd-n families
follow the calibration rules documented in the scaling probe reports.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Iterable

import numpy as np
import sympy as sp


Q = sp.Rational
EPS_PATH = Q(1, 50)
EPS_BOTTLENECK = Q(1, 10_000)
WEAK_BRANCH = Q(1, 10)
MID_LINK = Q(1, 5)
MIDDLE_CLIQUE = Q(1, 2)
OUTER_LINK = Q(1, 20)


@dataclass(frozen=True)
class Archetype:
    name: str
    weights: sp.Matrix

    @property
    def n(self) -> int:
        return int(self.weights.rows)


def zero_matrix(n: int) -> sp.Matrix:
    return sp.Matrix.zeros(n, n)


def add_edge(mat: sp.Matrix, i: int, j: int, w: sp.Rational) -> None:
    mat[i, j] = w
    mat[j, i] = w


def add_clique(mat: sp.Matrix, nodes: Iterable[int], w: sp.Rational) -> None:
    nodes = list(nodes)
    for a, i in enumerate(nodes):
        for j in nodes[a + 1 :]:
            add_edge(mat, i, j, w)


def sig(n: int) -> sp.Matrix:
    return sp.Matrix([Q(i) for i in range(1, n + 1)])


def degrees(weights: sp.Matrix) -> sp.Matrix:
    return sp.Matrix([sum(weights[i, j] for j in range(weights.cols)) for i in range(weights.rows)])


def max_degree(weights: sp.Matrix) -> sp.Rational:
    deg = degrees(weights)
    return max(deg)


def laplacian(weights: sp.Matrix) -> sp.Matrix:
    deg = degrees(weights)
    return sp.diag(*deg) - weights


def gov(weights: sp.Matrix, signal: sp.Matrix, i: int) -> sp.Expr:
    deg = degrees(weights)[i]
    numer = sum(weights[i, j] * signal[j] for j in range(weights.cols))
    return sp.S.Zero if deg == 0 else sp.simplify(numer / deg)


def deg_removed(weights: sp.Matrix, k: int, i: int) -> sp.Expr:
    return sum(sp.S.Zero if j == k else weights[i, j] for j in range(weights.cols))


def gov_removed(weights: sp.Matrix, signal: sp.Matrix, k: int, i: int) -> sp.Expr:
    denom = deg_removed(weights, k, i)
    numer = sum(sp.S.Zero if j == k else weights[i, j] * signal[j] for j in range(weights.cols))
    return sp.S.Zero if denom == 0 else sp.simplify(numer / denom)


def cv_value(weights: sp.Matrix, signal: sp.Matrix) -> sp.Expr:
    values: list[sp.Expr] = []
    for k in range(weights.rows):
        for i in range(weights.rows):
            values.append(sp.simplify(abs(gov(weights, signal, i) - gov_removed(weights, signal, k, i))))
    return max(values, key=lambda x: sp.N(x, 50))


def support_connected(weights: sp.Matrix) -> bool:
    n = weights.rows
    seen = {0}
    stack = [0]
    while stack:
        i = stack.pop()
        for j in range(n):
            if i != j and weights[i, j] != 0 and j not in seen:
                seen.add(j)
                stack.append(j)
    return len(seen) == n


def remove_node(weights: sp.Matrix, k: int) -> sp.Matrix:
    keep = [i for i in range(weights.rows) if i != k]
    return weights.extract(keep, keep)


def stationary_row(weights: sp.Matrix) -> sp.Matrix:
    deg = degrees(weights)
    total = sum(deg)
    return sp.Matrix([[sp.simplify(d / total) for d in deg]])


def random_walk_matrix(weights: sp.Matrix) -> sp.Matrix:
    deg = degrees(weights)
    rows = []
    for i in range(weights.rows):
        if deg[i] == 0:
            rows.append([sp.S.Zero for _ in range(weights.cols)])
        else:
            rows.append([sp.simplify(weights[i, j] / deg[i]) for j in range(weights.cols)])
    return sp.Matrix(rows)


def kemeny_constant(weights: sp.Matrix) -> sp.Expr | None:
    if not support_connected(weights):
        return None
    p = random_walk_matrix(weights)
    n = weights.rows
    one_pi = sp.ones(n, 1) * stationary_row(weights)
    z = (sp.eye(n) - p + one_pi).inv()
    return sp.simplify(sp.trace(z) - 1)


def spectral_gap_numeric(weights: sp.Matrix) -> float:
    eigvals = np.linalg.eigvalsh(sympy_to_numpy(laplacian(weights)))
    eigvals = np.sort(np.real_if_close(eigvals))
    return float(eigvals[1])


def normalized_laplacian_numeric(weights: sp.Matrix) -> float:
    deg = np.array([float(d) for d in degrees(weights)], dtype=float)
    d_inv_sqrt = np.zeros_like(deg)
    positive = deg > 0
    d_inv_sqrt[positive] = 1.0 / np.sqrt(deg[positive])
    d_half = np.diag(d_inv_sqrt)
    w = sympy_to_numpy(weights)
    l = np.diag(deg) - w
    l_tilde = d_half @ l @ d_half
    eigvals = np.linalg.eigvalsh(l_tilde)
    eigvals = np.sort(np.real_if_close(eigvals))
    return float(eigvals[1])


def singular_values_numeric(weights: sp.Matrix) -> np.ndarray:
    return np.linalg.svd(sympy_to_numpy(random_walk_matrix(weights)), compute_uv=False)


def gaussian_channel_mi(weights: sp.Matrix, snr: float) -> float:
    sigmas = singular_values_numeric(weights)
    return float(0.5 * np.sum(np.log1p(snr * sigmas * sigmas)))


def sympy_to_numpy(mat: sp.Matrix) -> np.ndarray:
    return np.array(mat.evalf(), dtype=float)


def format_exact(value: sp.Expr) -> str:
    if isinstance(value, sp.Rational):
        if value.q == 1:
            return str(value.p)
        return f"{value.p}/{value.q}"
    return str(sp.simplify(value))


def format_decimal(value: sp.Expr | float, digits: int = 4) -> str:
    return f"{float(sp.N(value, 50)):.{digits}f}"


def ranks(values: list[float]) -> list[float]:
    pairs = sorted((value, idx) for idx, value in enumerate(values))
    out = [0.0] * len(values)
    pos = 0
    while pos < len(pairs):
        end = pos
        while end + 1 < len(pairs) and pairs[end + 1][0] == pairs[pos][0]:
            end += 1
        rank = (pos + end + 2) / 2.0
        for j in range(pos, end + 1):
            out[pairs[j][1]] = rank
        pos = end + 1
    return out


def pearson(xs: list[float], ys: list[float]) -> float:
    x = np.asarray(xs, dtype=float)
    y = np.asarray(ys, dtype=float)
    x = x - x.mean()
    y = y - y.mean()
    denom = np.sqrt((x * x).sum() * (y * y).sum())
    return float((x * y).sum() / denom)


def spearman(xs: list[float], ys: list[float]) -> float:
    return pearson(ranks(xs), ranks(ys))


def uniK_n(n: int) -> Archetype:
    mat = zero_matrix(n)
    add_clique(mat, range(n), Q(1))
    return Archetype(f"uniK{n}", mat)


def asymK_n(n: int) -> Archetype:
    mat = uniK_n(n).weights.copy()
    add_edge(mat, 0, 1, Q(2))
    return Archetype(f"asymK{n}", mat)


def nearPath_n(n: int) -> Archetype:
    mat = zero_matrix(n)
    for i in range(n):
        for j in range(i + 1, n):
            weight = Q(1) if j == i + 1 else EPS_PATH
            add_edge(mat, i, j, weight)
    return Archetype(f"nearPath{n}", mat)


def wheel_n(n: int) -> Archetype:
    if n < 5:
        raise ValueError("wheel_n requires n >= 5")
    mat = zero_matrix(n)
    hub = 0
    for j in range(1, n):
        add_edge(mat, hub, j, Q(1))
    rim = list(range(1, n))
    for idx, i in enumerate(rim):
        j = rim[(idx + 1) % len(rim)]
        add_edge(mat, i, j, WEAK_BRANCH)
    return Archetype(f"wheel{n}", mat)


def bottleneck_bi_n(n: int) -> Archetype:
    if n == 5:
        mat = zero_matrix(5)
        add_edge(mat, 0, 1, Q(1))
        add_edge(mat, 0, 2, EPS_BOTTLENECK)
        add_edge(mat, 1, 2, EPS_BOTTLENECK)
        add_edge(mat, 2, 3, EPS_BOTTLENECK)
        add_edge(mat, 2, 4, EPS_BOTTLENECK)
        add_edge(mat, 3, 4, Q(1))
        return Archetype("bottleneck5", mat)
    if n == 7:
        mat = zero_matrix(7)
        add_clique(mat, [0, 1, 2, 3], Q(1))
        add_clique(mat, [3, 4, 5, 6], Q(1))
        for i in [0, 1, 2]:
            for j in [4, 5, 6]:
                add_edge(mat, i, j, EPS_BOTTLENECK)
        return Archetype("bottleneck7_bi", mat)
    if n % 2 == 0 or n < 9:
        raise ValueError("bottleneck_bi_n is calibrated only for odd n in {5,7,9,11,13,...}")
    mat = zero_matrix(n)
    pivot = (n - 1) // 2
    left = list(range(pivot))
    right = list(range(pivot + 1, n))
    add_clique(mat, left, Q(1))
    add_clique(mat, right, Q(1))
    for node in left + right:
        add_edge(mat, pivot, node, EPS_BOTTLENECK)
    return Archetype(f"bottleneck{n}_bi", mat)


def bottleneck_tri_7() -> Archetype:
    mat = zero_matrix(7)
    add_clique(mat, [0, 1, 2], Q(1))
    add_clique(mat, [2, 3, 4], Q(1))
    add_clique(mat, [4, 5, 6], Q(1))
    for i in range(7):
        for j in range(i + 1, 7):
            if mat[i, j] == 0:
                add_edge(mat, i, j, EPS_BOTTLENECK)
    return Archetype("bottleneck7_tri", mat)


def hubSpokeHierarchy_n(n: int) -> Archetype:
    if n < 7 or n % 2 == 0:
        raise ValueError("hubSpokeHierarchy_n is calibrated for odd n >= 7")
    primary = (n - 1) // 2 + 1
    secondary_start = primary + 1
    mat = zero_matrix(n)
    for node in range(1, primary + 1):
        add_edge(mat, 0, node, Q(1))
    for node in range(secondary_start, n):
        add_edge(mat, 1, node, WEAK_BRANCH)
    return Archetype(f"hubSpokeHierarchy{n}", mat)


def nestedHierarchy_n(n: int) -> Archetype:
    if n == 7:
        inner_size = 3
        middle_size = 2
    elif n in (9, 11, 13):
        inner_size = {9: 3, 11: 4, 13: 5}[n]
        middle_size = {9: 3, 11: 4, 13: 4}[n]
    else:
        raise ValueError("nestedHierarchy_n is calibrated for n in {7,9,11,13}")
    outer_size = n - inner_size - middle_size
    mat = zero_matrix(n)
    inner = list(range(inner_size))
    middle = list(range(inner_size, inner_size + middle_size))
    outer = list(range(inner_size + middle_size, n))
    add_clique(mat, inner, Q(1))
    add_clique(mat, middle, MIDDLE_CLIQUE)
    for i in inner:
        for j in middle:
            add_edge(mat, i, j, MID_LINK)
    for i in middle:
        for j in outer:
            add_edge(mat, i, j, OUTER_LINK)
    if len(outer) != outer_size:
        raise AssertionError("outer partition mismatch")
    return Archetype(f"nestedHierarchy{n}", mat)


def all_archetypes_n5() -> list[Archetype]:
    return [uniK_n(5), asymK_n(5), nearPath_n(5), wheel_n(5), bottleneck_bi_n(5)]


def all_archetypes_n7() -> list[Archetype]:
    return [
        uniK_n(7),
        asymK_n(7),
        nearPath_n(7),
        bottleneck_bi_n(7),
        bottleneck_tri_7(),
        hubSpokeHierarchy_n(7),
        nestedHierarchy_n(7),
    ]


def all_archetypes_scale() -> list[Archetype]:
    out: list[Archetype] = []
    out.extend(all_archetypes_n5())
    out.extend(all_archetypes_n7())
    for n in (9, 11, 13):
        out.extend(
            [
                uniK_n(n),
                asymK_n(n),
                nearPath_n(n),
                bottleneck_bi_n(n),
                hubSpokeHierarchy_n(n),
                nestedHierarchy_n(n),
                wheel_n(n),
            ]
        )
    return out


def family_for_n(n: int) -> list[Archetype]:
    if n == 5:
        return all_archetypes_n5()
    if n == 7:
        return all_archetypes_n7()
    if n in (9, 11, 13):
        return [
            uniK_n(n),
            asymK_n(n),
            nearPath_n(n),
            bottleneck_bi_n(n),
            hubSpokeHierarchy_n(n),
            nestedHierarchy_n(n),
            wheel_n(n),
        ]
    raise ValueError(f"unsupported n={n}")


def headline_metrics(archetype: Archetype) -> dict[str, object]:
    signal = sig(archetype.n)
    cv = sp.simplify(cv_value(archetype.weights, signal))
    lambda2 = spectral_gap_numeric(archetype.weights)
    lambda2_tilde = normalized_laplacian_numeric(archetype.weights)
    return {
        "name": archetype.name,
        "n": archetype.n,
        "cv_exact": cv,
        "cv_float": float(sp.N(cv, 50)),
        "lambda2": lambda2,
        "lambda2_tilde": lambda2_tilde,
        "S_delta": lambda2 * float(sp.N(cv, 50)),
    }
