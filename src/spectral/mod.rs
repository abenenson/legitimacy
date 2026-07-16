pub mod binary_decision_helpers;
pub mod coarse_grain;
pub mod concrete_graphs;
pub mod critical;
pub mod measure_theoretic;
pub mod noisy_threshold_closed_form;
pub mod non_peer_relative;
pub mod positive_procedure;
pub mod stackelberg;
#[cfg(test)]
mod tests;

use crate::{EdgeTransform, GovernanceGraph, NodeId};
use num_rational::Ratio;
use std::collections::BTreeMap;

pub type Rational = Ratio<i64>;
pub type SignalSignature = Vec<Rational>;
pub type Weights = Vec<Vec<Rational>>;

pub const SPECTRAL_WELL_CONNECTED_THRESHOLD: f64 = 17.0 / 20.0;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Partition {
    pub blocks: Vec<Vec<NodeId>>,
}

impl Partition {
    pub fn new(blocks: Vec<Vec<NodeId>>) -> Self {
        Self { blocks }
    }
}

pub fn capacity(graph: &GovernanceGraph, signal: &[Rational], epsilon: Rational) -> bool {
    let weighted = WeightedGovernanceGraph::from_graph(graph);
    signal_range(signal) * weighted.max_degree() <= epsilon * weighted.min_removed_degree()
}

pub fn capacity_bound(graph: &GovernanceGraph, signal: &[Rational]) -> Rational {
    let weighted = WeightedGovernanceGraph::from_graph(graph);
    safe_div(
        signal_range(signal) * weighted.max_degree(),
        weighted.min_removed_degree(),
    )
}

/// Cook (1977) gross-error sensitivity of the governance map.
///
/// Identifies `cv(G, s)` with the Hampel (1974) influence-function sup-norm
/// under single-node deletion on `gov = D^{-1} W`.
pub fn cv(graph: &GovernanceGraph, signal: &[Rational]) -> Rational {
    WeightedGovernanceGraph::from_graph(graph).cv(signal)
}

pub fn spectral_well_connected(graph: &GovernanceGraph, signal: &[Rational]) -> bool {
    let weighted = WeightedGovernanceGraph::from_graph(graph);
    let lambda_2 = spectral_gap(&weighted.weights);
    let cv = weighted.cv(signal);
    let s_delta = lambda_2 * ratio_to_f64(cv);
    s_delta + 1e-9 >= SPECTRAL_WELL_CONNECTED_THRESHOLD
}

pub fn weights(graph: &GovernanceGraph) -> Weights {
    WeightedGovernanceGraph::from_graph(graph).weights
}

/// Weighted unnormalized Laplacian gap `lambda_2(G)`.
pub fn spectral_gap(weights: &Weights) -> f64 {
    let laplacian = laplacian_matrix(weights);
    second_smallest_eigenvalue(laplacian)
}

/// Normalized-Laplacian gap `lambda_2(D^{-1/2} L D^{-1/2})`.
///
/// This is a separate invariant from `SpectralWellConnected`: it is an
/// ordinal adversarial-MI predictor, not a basin classifier.
pub fn normalized_spectral_gap(weights: &Weights) -> f64 {
    let normalized = normalized_laplacian_matrix(weights);
    second_smallest_eigenvalue(normalized)
}

pub fn connected_component_count(weights: &Weights) -> usize {
    let node_count = weights.len();
    if node_count == 0 {
        return 0;
    }

    let mut visited = vec![false; node_count];
    let mut count = 0;
    for start in 0..node_count {
        if visited[start] {
            continue;
        }
        count += 1;
        let mut stack = vec![start];
        visited[start] = true;
        while let Some(node) = stack.pop() {
            for (neighbor, weight) in weights[node].iter().enumerate() {
                if neighbor != node && *weight > Rational::from_integer(0) && !visited[neighbor] {
                    visited[neighbor] = true;
                    stack.push(neighbor);
                }
            }
        }
    }
    count
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WeightedGovernanceGraph {
    pub(crate) node_ids: Vec<NodeId>,
    pub(crate) index_by_node: BTreeMap<NodeId, usize>,
    pub(crate) weights: Weights,
}

impl WeightedGovernanceGraph {
    pub(crate) fn from_graph(graph: &GovernanceGraph) -> Self {
        let mut node_ids = graph.nodes.keys().cloned().collect::<Vec<_>>();
        node_ids.sort();
        let index_by_node = node_ids
            .iter()
            .cloned()
            .enumerate()
            .map(|(index, node_id)| (node_id, index))
            .collect::<BTreeMap<_, _>>();
        let mut weights = vec![vec![Rational::from_integer(0); node_ids.len()]; node_ids.len()];

        for edge in &graph.edges {
            let Some(&left) = index_by_node.get(&edge.from) else {
                continue;
            };
            let Some(&right) = index_by_node.get(&edge.to) else {
                continue;
            };
            let weight = edge_weight(&edge.transform);
            weights[left][right] += weight;
            weights[right][left] += weight;
        }

        Self {
            node_ids,
            index_by_node,
            weights,
        }
    }

    pub(crate) fn node_count(&self) -> usize {
        self.node_ids.len()
    }

    pub(crate) fn degree(&self, node: usize) -> Rational {
        self.weights[node].iter().cloned().sum()
    }

    #[allow(dead_code)]
    pub(crate) fn max_degree(&self) -> Rational {
        (0..self.node_count())
            .map(|node| self.degree(node))
            .max()
            .unwrap_or_else(|| Rational::from_integer(0))
    }

    pub(crate) fn degree_removed(&self, removed: usize, observer: usize) -> Rational {
        self.weights[observer]
            .iter()
            .enumerate()
            .filter(|(node, _)| *node != removed)
            .map(|(_, weight)| *weight)
            .sum()
    }

    #[allow(dead_code)]
    pub(crate) fn min_removed_degree(&self) -> Rational {
        let node_count = self.node_count();
        if node_count == 0 {
            return Rational::from_integer(0);
        }

        (0..node_count)
            .flat_map(|removed| (0..node_count).map(move |observer| (removed, observer)))
            .map(|(removed, observer)| self.degree_removed(removed, observer))
            .min()
            .unwrap_or_else(|| Rational::from_integer(0))
    }

    pub(crate) fn governance(&self, signal: &[Rational], observer: usize) -> Rational {
        safe_div(
            self.weights[observer]
                .iter()
                .zip(signal.iter())
                .map(|(weight, value)| weight * value)
                .sum(),
            self.degree(observer),
        )
    }

    pub(crate) fn governance_removed(
        &self,
        signal: &[Rational],
        removed: usize,
        observer: usize,
    ) -> Rational {
        safe_div(
            self.weights[observer]
                .iter()
                .zip(signal.iter())
                .enumerate()
                .filter(|(node, _)| *node != removed)
                .map(|(_, (weight, value))| weight * value)
                .sum(),
            self.degree_removed(removed, observer),
        )
    }

    pub(crate) fn perturbation(
        &self,
        signal: &[Rational],
        removed: usize,
        observer: usize,
    ) -> Rational {
        abs_ratio(
            self.governance(signal, observer) - self.governance_removed(signal, removed, observer),
        )
    }

    /// Cook (1977) gross-error sensitivity of the governance map.
    ///
    /// Identifies `cv(G, s)` with the Hampel (1974) influence-function sup-norm
    /// under single-node deletion on `gov = D^{-1} W`.
    pub(crate) fn cv(&self, signal: &[Rational]) -> Rational {
        let node_count = self.node_count();
        if node_count == 0 {
            return Rational::from_integer(0);
        }

        (0..node_count)
            .flat_map(|removed| (0..node_count).map(move |observer| (removed, observer)))
            .map(|(removed, observer)| self.perturbation(signal, removed, observer))
            .max()
            .unwrap_or_else(|| Rational::from_integer(0))
    }
}

pub(crate) fn abs_ratio(value: Rational) -> Rational {
    if value < Rational::from_integer(0) {
        -value
    } else {
        value
    }
}

pub(crate) fn edge_weight(transform: &EdgeTransform) -> Rational {
    match transform {
        EdgeTransform::PassThrough => Rational::from_integer(1),
        EdgeTransform::ClaimModification { delta } => rational_from_f64(delta.abs()),
    }
}

#[allow(dead_code)]
pub(crate) fn rational(numerator: i64, denominator: i64) -> Rational {
    Rational::new(numerator, denominator)
}

pub(crate) fn rational_from_f64(value: f64) -> Rational {
    if !value.is_finite() {
        return Rational::from_integer(0);
    }
    if value == 0.0 {
        return Rational::from_integer(0);
    }

    let sign = if value.is_sign_negative() { -1 } else { 1 };
    let value = value.abs();
    let tolerance = 1e-12;
    let max_denominator = 1_000_000i64;

    for denominator in 1..=max_denominator {
        let scaled = value * denominator as f64;
        let numerator = scaled.round() as i64;
        if (scaled - numerator as f64).abs() <= tolerance {
            return Rational::new(sign * numerator, denominator);
        }
    }

    Rational::approximate_float(sign as f64 * value).unwrap_or_else(|| Rational::from_integer(0))
}

pub(crate) fn safe_div(numerator: Rational, denominator: Rational) -> Rational {
    if denominator == Rational::from_integer(0) {
        Rational::from_integer(0)
    } else {
        numerator / denominator
    }
}

#[allow(dead_code)]
pub(crate) fn signal_range(signal: &[Rational]) -> Rational {
    signal
        .iter()
        .flat_map(|left| signal.iter().map(move |right| abs_ratio(*left - *right)))
        .max()
        .unwrap_or_else(|| Rational::from_integer(0))
}

fn laplacian_matrix(weights: &Weights) -> Vec<Vec<f64>> {
    let node_count = weights.len();
    let degrees = weights
        .iter()
        .map(|row| row.iter().map(|value| ratio_to_f64(*value)).sum::<f64>())
        .collect::<Vec<_>>();
    let mut laplacian = vec![vec![0.0_f64; node_count]; node_count];

    for row in 0..node_count {
        laplacian[row][row] = degrees[row];
        for col in 0..node_count {
            if row != col {
                laplacian[row][col] = -ratio_to_f64(weights[row][col]);
            }
        }
    }

    laplacian
}

fn normalized_laplacian_matrix(weights: &Weights) -> Vec<Vec<f64>> {
    let node_count = weights.len();
    let degrees = weights
        .iter()
        .map(|row| row.iter().map(|value| ratio_to_f64(*value)).sum::<f64>())
        .collect::<Vec<_>>();
    let mut normalized = vec![vec![0.0_f64; node_count]; node_count];

    for row in 0..node_count {
        let degree_row = degrees[row];
        if degree_row <= 1e-10 {
            continue;
        }
        normalized[row][row] = 1.0;
        for col in 0..node_count {
            if row == col {
                continue;
            }
            let degree_col = degrees[col];
            if degree_col <= 1e-10 {
                continue;
            }
            normalized[row][col] =
                -ratio_to_f64(weights[row][col]) / (degree_row.sqrt() * degree_col.sqrt());
        }
    }

    normalized
}

pub fn ratio_to_f64(value: Rational) -> f64 {
    *value.numer() as f64 / *value.denom() as f64
}

fn second_smallest_eigenvalue(matrix: Vec<Vec<f64>>) -> f64 {
    if matrix.len() < 2 {
        return 0.0;
    }

    let mut eigenvalues = jacobi_eigenvalues(matrix)
        .into_iter()
        .map(|value| {
            if value.abs() <= 1e-10 {
                0.0
            } else {
                value.max(0.0)
            }
        })
        .collect::<Vec<_>>();
    eigenvalues.sort_by(f64::total_cmp);
    eigenvalues.get(1).copied().unwrap_or(0.0)
}

fn jacobi_eigenvalues(mut matrix: Vec<Vec<f64>>) -> Vec<f64> {
    let n = matrix.len();
    if n == 0 {
        return Vec::new();
    }

    for _ in 0..(n * n * 16).max(16) {
        let mut max_value = 0.0_f64;
        let mut pivot = None;
        for (row, row_values) in matrix.iter().enumerate() {
            for (col, value) in row_values.iter().enumerate().skip(row + 1) {
                let candidate = value.abs();
                if candidate > max_value {
                    max_value = candidate;
                    pivot = Some((row, col));
                }
            }
        }

        let Some((p, q)) = pivot else {
            break;
        };
        if max_value <= 1e-12 {
            break;
        }

        let theta = (matrix[q][q] - matrix[p][p]) / (2.0 * matrix[p][q]);
        let t = if theta >= 0.0 {
            1.0 / (theta + (1.0 + theta * theta).sqrt())
        } else {
            -1.0 / (-theta + (1.0 + theta * theta).sqrt())
        };
        let c = 1.0 / (1.0 + t * t).sqrt();
        let s = t * c;

        let indices = (0..n).collect::<Vec<_>>();
        for index in indices {
            if index == p || index == q {
                continue;
            }
            let aip = matrix[index][p];
            let aiq = matrix[index][q];
            matrix[index][p] = c * aip - s * aiq;
            matrix[p][index] = matrix[index][p];
            matrix[index][q] = c * aiq + s * aip;
            matrix[q][index] = matrix[index][q];
        }

        let app = matrix[p][p];
        let aqq = matrix[q][q];
        let apq = matrix[p][q];
        matrix[p][p] = c * c * app - 2.0 * s * c * apq + s * s * aqq;
        matrix[q][q] = s * s * app + 2.0 * s * c * apq + c * c * aqq;
        matrix[p][q] = 0.0;
        matrix[q][p] = 0.0;
    }

    (0..n).map(|index| matrix[index][index]).collect()
}
