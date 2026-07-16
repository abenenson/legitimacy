# Probe Script Reconstruction

These scripts reconstruct the numerical probes cited by `papers/03-impossibility-theorem.md` §§5.2-5.4 and §6.7.

Dependencies:
- `python3`
- `sympy`
- `numpy`

Run each script from the repo root:

```bash
python3 probes/scripts/kemeny_indicator_probe.py
python3 probes/scripts/normalized_laplacian_probe.py
python3 probes/scripts/n9_n11_n13_s_delta_probe.py
python3 probes/scripts/adversarial_mi_probe.py
```

## Files

### `archetypes.py`

Canonical weight-matrix constructors and shared utilities for:
- `uniK_n`
- `asymK_n`
- `nearPath_n`
- `bottleneck_bi_n`
- `hubSpokeHierarchy_n`
- `nestedHierarchy_n`
- `wheel_n`
- `bottleneck7_tri`

Lean alignment:
- Exact n=5 and n=7 graphs match `lean/Legitimacy/Spectral/ConcreteGraphs.lean`.
- n=9/11/13 odd-`n` extensions follow the calibration rules documented in the scaling reports.

Spot-checks reproduced by the fixture:
- n=5: `cv`, `lambda2(L)`, and `lambda2(L_tilde)` rows from the 2c and normalized-Laplacian reports.
- n=7: `nearPath7`, `bottleneck7_bi`, `hubSpokeHierarchy7`, `nestedHierarchy7` match the published `cv` and spectral rows.
- n=9/11/13: `cv`, `lambda2(L)`, `lambda2(L_tilde)`, and `S_delta` values match the published scaling tables.

### `kemeny_indicator_probe.py`

Reconstructs the probe behind `papers/03-impossibility-theorem.md` §5.2.

Expected output:
- Exact n=5 table for `cv(G, sig5)`, `K(P)`, and every `K(P^{(-k)})`
- Exact/decimal `kappa_k = K(P) - K(P^{(-k)})` table
- The constant-signal obstruction note

### `normalized_laplacian_probe.py`

Reconstructs the probe behind `papers/03-impossibility-theorem.md` §5.2.

Expected output:
- Full 33-archetype table for `lambda2(L)`, `lambda2(L_tilde)`, `cv`, `S_delta`, and basin labels
- Per-scale admissible-window table for `lambda2(L_tilde)`
- Global and per-scale Spearman correlations against the Gaussian-channel MI proxy
- The n=7 `nearPath7` / `bottleneck7_bi` / `hubSpokeHierarchy7` MI mismatch summary

### `n9_n11_n13_s_delta_probe.py`

Reconstructs the probe behind `papers/03-impossibility-theorem.md` §5.2.

Expected output:
- n=9 table for `spectralGap`, `cv(sig9)`, `S_delta`, and `17/20` pass/fail
- n=11 and n=13 tables for the same quantities
- Admissible threshold window for each of `n in {9, 11, 13}`

### `adversarial_mi_probe.py`

Reconstructs the analytical pathway cited by `papers/03-impossibility-theorem.md` §5.3.

Expected output:
- n=5 spectral-invariant table
- Exact Gaussian-channel Model-D MI tables for n=5 and n=7 at `sigma = 0.1`
- The combined n=5+7 exact Spearman table from the report's `final_probe.py` discussion:
  - `sigma = 0.01`
  - `sigma = 0.1`
  - `sigma = 1.0`
- Analytical notes tying Models A/B/C/D/E to the formulas published in the report

## Notes

- Exact arithmetic uses `sympy.Rational` wherever the report gives rational values.
- Numerical spectral quantities use `numpy.linalg.eigvalsh` / `svd`, which reproduces the report decimals to the printed precision.
- No SciPy is required.
