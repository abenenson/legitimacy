//! Spectral analysis of governance graphs.
//!
//! Computes the algebraic connectivity (Fiedler value, second-smallest
//! eigenvalue of the Laplacian) and derived bounds without external
//! linear algebra dependencies. Uses inverse iteration with deflation
//! of the trivial zero eigenvalue.

use crate::{
    GovernanceGraph, LegitimacyError, NodeId,
    spectral::{self as exact_spectral, Rational, critical},
};
use serde::Serialize;
use std::collections::BTreeMap;

/// Pipeline default for capacity saturation and C* diagnostics.
///
/// Matches the `delta = "1/10"` fixture default in
/// `tests/fixtures/spectral_expectations.toml`.
pub const CAPACITY_SATURATION_EPSILON: f64 = 0.1;
const RG_TRAJECTORY_DEPTH: usize = 3;

/// Spectral properties of a governance graph.
#[derive(Debug, Clone, Serialize)]
pub struct SpectralAnalysis {
    pub node_count: usize,
    pub edge_count: usize,
    pub connected_components: usize,
    pub is_connected: bool,
    /// True algebraic connectivity (lambda_2), including 0.0 for disconnected graphs.
    pub lambda_2: f64,
    /// Positive connected-carrier gap. None if disconnected or single-node.
    pub spectral_gap: Option<f64>,
    pub max_degree: usize,
    /// Minimum residual degree after a single-node removal.
    pub min_removed_deg: usize,
    pub signal_range: f64,
    /// Exact rational CV from the Lean-parity spectral stack.
    pub cv_exact: Option<String>,
    /// CV bound: signal_range * max_degree / lambda_2.
    pub cv_bound: Option<f64>,
    /// Structural capacity bound: signal_range * max_degree / min_removed_deg.
    pub capacity: Option<f64>,
    /// Capacity saturation verdict at CAPACITY_SATURATION_EPSILON.
    pub capacity_saturated: Option<bool>,
    /// Exact rational C*(G, delta) from the Lean-parity spectral stack.
    pub c_star: Option<String>,
    /// Delta used for C*(G, delta).
    pub c_star_delta: f64,
    /// SpectralWellConnected verdict at theta = 17/20.
    pub swc: Option<bool>,
    /// Greedy RG trajectory exact rational (cv, C*) pairs for k = 1..=3.
    pub rg_trajectory: Option<Vec<(String, String)>>,
    /// Localizability bound: 1.0 / (2.0 * cv_bound) from Cheeger tradeoff.
    pub localizability_bound: Option<f64>,
    /// Product of cv_bound and localizability_bound (should be >= 0.5).
    pub cv_times_localizability: Option<f64>,
}

impl SpectralAnalysis {
    /// Whether the capacity bound is saturated at caller-supplied tolerance `epsilon`.
    pub fn capacity_saturated_at(&self, epsilon: f64) -> bool {
        epsilon.is_finite() && epsilon >= 0.0 && self.capacity.is_some_and(|value| epsilon <= value)
    }
}

#[derive(Debug, Clone)]
pub struct PaperDiagnostics {
    pub signal_dimension: usize,
    pub connected_components: usize,
    pub lambda_2: f64,
    pub cv: Rational,
    pub c_star: Option<Rational>,
    pub s_delta: f64,
    pub spectral_well_connected: bool,
    pub normalized_lambda_2: f64,
    pub delta: f64,
}

pub fn paper_diagnostics(
    graph: &GovernanceGraph,
    delta: f64,
) -> Result<PaperDiagnostics, LegitimacyError> {
    if !delta.is_finite() || delta <= 0.0 {
        return Err(LegitimacyError::invalid_input(format!(
            "--delta must be finite and positive, got {delta}",
        )));
    }

    let signal = probe_signal(graph);
    let weights = exact_spectral::weights(graph);
    let cv = exact_spectral::cv(graph, &signal);
    let delta = Rational::approximate_float(delta).ok_or_else(|| {
        LegitimacyError::invalid_input("failed to represent --delta as a rational")
    })?;
    let lambda_2 = exact_spectral::spectral_gap(&weights);
    let connected_components = exact_spectral::connected_component_count(&weights);
    let c_star = if cv > Rational::from_integer(0) && lambda_2 > 1e-10 {
        Some(critical::c_star(graph, &signal, delta))
    } else {
        None
    };
    let s_delta = lambda_2 * exact_spectral::ratio_to_f64(cv);

    Ok(PaperDiagnostics {
        signal_dimension: signal.len(),
        connected_components,
        lambda_2,
        cv,
        c_star,
        s_delta,
        spectral_well_connected: exact_spectral::spectral_well_connected(graph, &signal),
        normalized_lambda_2: exact_spectral::normalized_spectral_gap(&weights),
        delta: exact_spectral::ratio_to_f64(delta),
    })
}

/// Compute spectral analysis for a governance graph with given synthetic claims.
pub fn spectral_analysis(
    graph: &GovernanceGraph,
    claims: &[crate::GovernanceClaim],
) -> SpectralAnalysis {
    let n = graph.nodes.len();
    if n == 0 {
        return SpectralAnalysis {
            node_count: 0,
            edge_count: 0,
            connected_components: 0,
            is_connected: false,
            lambda_2: 0.0,
            spectral_gap: None,
            max_degree: 0,
            min_removed_deg: 0,
            signal_range: 0.0,
            cv_exact: None,
            cv_bound: None,
            capacity: None,
            capacity_saturated: None,
            c_star: None,
            c_star_delta: CAPACITY_SATURATION_EPSILON,
            swc: None,
            rg_trajectory: None,
            localizability_bound: None,
            cv_times_localizability: None,
        };
    }

    // Map NodeId to dense index
    let mut node_ids = graph.nodes.keys().collect::<Vec<_>>();
    node_ids.sort();
    let node_index: BTreeMap<&NodeId, usize> = node_ids
        .into_iter()
        .enumerate()
        .map(|(i, id)| (id, i))
        .collect();

    // Build adjacency matrix (undirected, weighted for ClaimModification)
    let mut adjacency = vec![vec![0.0f64; n]; n];
    for edge in &graph.edges {
        if let (Some(&i), Some(&j)) = (node_index.get(&edge.from), node_index.get(&edge.to)) {
            let weight = match &edge.transform {
                crate::EdgeTransform::PassThrough => 1.0,
                crate::EdgeTransform::ClaimModification { delta } => delta.abs().max(1.0),
            };
            adjacency[i][j] = weight;
            adjacency[j][i] = weight;
        }
    }

    // Compute degree and Laplacian
    let mut degree = vec![0.0f64; n];
    let mut max_degree_val = 0usize;
    let mut min_removed_deg = usize::MAX;
    for i in 0..n {
        let deg: f64 = adjacency[i].iter().sum();
        degree[i] = deg;
        let int_deg = adjacency[i].iter().filter(|&&w| w > 0.0).count();
        if int_deg > max_degree_val {
            max_degree_val = int_deg;
        }

        for k in 0..n {
            let removed_deg = adjacency[i]
                .iter()
                .enumerate()
                .filter(|(j, w)| *j != k && **w > 0.0)
                .count();
            min_removed_deg = min_removed_deg.min(removed_deg);
        }
    }
    if min_removed_deg == usize::MAX {
        min_removed_deg = 0;
    }

    // L = D - A
    let mut laplacian = vec![vec![0.0f64; n]; n];
    for i in 0..n {
        for j in 0..n {
            if i == j {
                laplacian[i][j] = degree[i];
            } else {
                laplacian[i][j] = -adjacency[i][j];
            }
        }
    }

    // Signal range from claims
    let signal_range = if claims.is_empty() {
        0.0
    } else {
        let strengths: Vec<f64> = claims.iter().map(|c| c.strength).collect();
        let min = strengths.iter().cloned().fold(f64::INFINITY, f64::min);
        let max = strengths.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
        max - min
    };

    if n == 1 {
        return SpectralAnalysis {
            node_count: 1,
            edge_count: graph.edges.len(),
            connected_components: 1,
            is_connected: true,
            lambda_2: 0.0,
            spectral_gap: None,
            max_degree: max_degree_val,
            min_removed_deg,
            signal_range,
            cv_exact: None,
            cv_bound: None,
            capacity: None,
            capacity_saturated: None,
            c_star: None,
            c_star_delta: CAPACITY_SATURATION_EPSILON,
            swc: None,
            rg_trajectory: None,
            localizability_bound: None,
            cv_times_localizability: None,
        };
    }

    let connected_components = connected_component_count(&adjacency);

    // Find the true second-smallest Laplacian eigenvalue.
    let lambda_2 = fiedler_eigenvalue(&laplacian, n);

    let is_connected = connected_components == 1 && lambda_2 > 1e-10;
    let spectral_gap = if is_connected { Some(lambda_2) } else { None };

    let cv_bound = spectral_gap.and_then(|gap| {
        if gap > 1e-10 && max_degree_val > 0 {
            Some(signal_range * max_degree_val as f64 / gap)
        } else {
            None
        }
    });

    let capacity = if min_removed_deg > 0 && max_degree_val > 0 {
        Some(signal_range * max_degree_val as f64 / min_removed_deg as f64)
    } else {
        None
    };

    let localizability_bound = cv_bound.and_then(|cv| {
        if cv > 1e-10 {
            Some(1.0 / (2.0 * cv))
        } else {
            None
        }
    });

    let cv_times_localizability = match (cv_bound, localizability_bound) {
        (Some(cv), Some(loc)) => Some(cv * loc),
        _ => None,
    };
    let capacity_saturated = capacity.map(|value| {
        CAPACITY_SATURATION_EPSILON.is_finite()
            && CAPACITY_SATURATION_EPSILON >= 0.0
            && CAPACITY_SATURATION_EPSILON <= value
    });
    let diagnostics = paper_diagnostics(graph, CAPACITY_SATURATION_EPSILON).ok();
    let rg_trajectory = if is_connected {
        let probe_signal = probe_signal(graph);
        let delta = Rational::new(1, 10);
        Some(
            (1..=RG_TRAJECTORY_DEPTH)
                .map(|step| {
                    let (cv, c_star) = critical::rg_trajectory(graph, &probe_signal, delta, step);
                    (format_rational_exact(cv), format_rational_exact(c_star))
                })
                .collect(),
        )
    } else {
        None
    };

    SpectralAnalysis {
        node_count: n,
        edge_count: graph.edges.len(),
        connected_components,
        is_connected,
        lambda_2,
        spectral_gap,
        max_degree: max_degree_val,
        min_removed_deg,
        signal_range,
        cv_exact: diagnostics
            .as_ref()
            .map(|diagnostics| format_rational_exact(diagnostics.cv)),
        cv_bound,
        capacity,
        capacity_saturated,
        c_star: diagnostics
            .as_ref()
            .and_then(|diagnostics| diagnostics.c_star.map(format_rational_exact)),
        c_star_delta: diagnostics
            .as_ref()
            .map_or(CAPACITY_SATURATION_EPSILON, |diagnostics| diagnostics.delta),
        swc: diagnostics
            .as_ref()
            .map(|diagnostics| diagnostics.spectral_well_connected),
        rg_trajectory,
        localizability_bound,
        cv_times_localizability,
    }
}

fn probe_signal(graph: &GovernanceGraph) -> Vec<Rational> {
    let mut node_ids = graph.nodes.keys().collect::<Vec<_>>();
    node_ids.sort();
    node_ids
        .iter()
        .enumerate()
        .map(|(index, _)| Rational::from_integer((index + 1) as i64))
        .collect()
}

fn format_rational_exact(value: Rational) -> String {
    format!("{}/{}", value.numer(), value.denom())
}

fn connected_component_count(adjacency: &[Vec<f64>]) -> usize {
    let node_count = adjacency.len();
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
            for (neighbor, weight) in adjacency[node].iter().enumerate() {
                if neighbor != node && *weight > 0.0 && !visited[neighbor] {
                    visited[neighbor] = true;
                    stack.push(neighbor);
                }
            }
        }
    }
    count
}

/// Compute the second-smallest eigenvalue of a symmetric Laplacian matrix.
///
/// Uses shift-invert power iteration: finds the smallest eigenvalue of
/// (L + shift * vv^T) where v = [1,1,...,1]/sqrt(n) is the null-space
/// eigenvector. This deflates the zero eigenvalue so the smallest
/// eigenvalue of the shifted system is lambda_2.
fn fiedler_eigenvalue(laplacian: &[Vec<f64>], n: usize) -> f64 {
    if n <= 1 {
        return 0.0;
    }

    // For 2x2, compute directly
    if n == 2 {
        // Eigenvalues of [[a, b], [c, d]] Laplacian: 0 and a+d
        return laplacian[0][0] + laplacian[1][1];
    }

    if connected_component_count_from_laplacian(laplacian) > 1 {
        return 0.0;
    }

    // Deflate the zero eigenvalue by adding shift * vv^T where v = 1/sqrt(n)
    // This shifts the zero eigenvalue to `shift` without affecting others.
    let shift = trace(laplacian, n); // Use trace as a safe shift
    if shift < 1e-10 {
        return 0.0; // All-zero Laplacian means disconnected/empty
    }

    let inv_n = 1.0 / n as f64;
    let mut shifted = vec![vec![0.0f64; n]; n];
    for i in 0..n {
        for j in 0..n {
            shifted[i][j] = laplacian[i][j] + shift * inv_n;
        }
    }

    // Now find the smallest eigenvalue of the shifted system using inverse iteration.
    // The smallest eigenvalue of shifted = lambda_2 (the zero eigenvalue became `shift`).
    // Inverse iteration: repeatedly solve shifted * y = x, then x = y/||y||.
    // This converges to the eigenvector of the smallest eigenvalue.

    // Use Cholesky or LU to solve the system. For small matrices, use
    // Gaussian elimination with partial pivoting.
    let mut x: Vec<f64> = (0..n)
        .map(|i| if i % 2 == 0 { 1.0 } else { -1.0 })
        .collect();
    normalize(&mut x);

    // LU decomposition of shifted matrix (done once)
    let Some((lu_matrix, pivots)) = lu_decompose(&shifted, n) else {
        // Fallback: use Rayleigh quotient iteration
        return rayleigh_quotient_fallback(laplacian, n);
    };

    for _iter in 0..200 {
        let y = lu_solve(&lu_matrix, &pivots, &x, n);

        // Deflect from the constant vector
        let proj = dot(&y, &vec![inv_n.sqrt(); n]) * inv_n.sqrt();
        let mut deflected: Vec<f64> = y.to_vec();
        for item in deflected.iter_mut() {
            *item -= proj;
        }

        let norm = l2_norm(&deflected);
        if norm < 1e-15 {
            break;
        }
        for (xi, di) in x.iter_mut().zip(deflected.iter()) {
            *xi = *di / norm;
        }
    }

    // Rayleigh quotient: lambda = x^T L x / x^T x
    let lx = mat_vec(laplacian, &x, n);
    let numerator = dot(&x, &lx);
    let denominator = dot(&x, &x);
    if denominator < 1e-15 {
        return 0.0;
    }
    let lambda = numerator / denominator;
    lambda.max(0.0)
}

fn connected_component_count_from_laplacian(laplacian: &[Vec<f64>]) -> usize {
    let node_count = laplacian.len();
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
            for neighbor in 0..node_count {
                if neighbor != node && laplacian[node][neighbor].abs() > 1e-10 && !visited[neighbor]
                {
                    visited[neighbor] = true;
                    stack.push(neighbor);
                }
            }
        }
    }
    count
}

fn trace(matrix: &[Vec<f64>], n: usize) -> f64 {
    (0..n).map(|i| matrix[i][i]).sum()
}

fn normalize(v: &mut [f64]) {
    let norm = l2_norm(v);
    if norm > 1e-15 {
        for x in v.iter_mut() {
            *x /= norm;
        }
    }
}

fn l2_norm(v: &[f64]) -> f64 {
    v.iter().map(|x| x * x).sum::<f64>().sqrt()
}

fn dot(a: &[f64], b: &[f64]) -> f64 {
    a.iter().zip(b.iter()).map(|(x, y)| x * y).sum()
}

fn mat_vec(m: &[Vec<f64>], v: &[f64], n: usize) -> Vec<f64> {
    let mut result = vec![0.0; n];
    for i in 0..n {
        for j in 0..n {
            result[i] += m[i][j] * v[j];
        }
    }
    result
}

/// LU decomposition with partial pivoting.
/// Returns (LU matrix, pivot indices) or None if singular.
#[allow(clippy::needless_range_loop)]
fn lu_decompose(matrix: &[Vec<f64>], n: usize) -> Option<(Vec<Vec<f64>>, Vec<usize>)> {
    let mut lu = matrix.to_vec();
    let mut pivots: Vec<usize> = (0..n).collect();

    for k in 0..n {
        // Find pivot
        let mut max_val = lu[k][k].abs();
        let mut max_row = k;
        for i in (k + 1)..n {
            if lu[i][k].abs() > max_val {
                max_val = lu[i][k].abs();
                max_row = i;
            }
        }

        if max_val < 1e-14 {
            return None; // Singular
        }

        if max_row != k {
            lu.swap(k, max_row);
            pivots.swap(k, max_row);
        }

        for i in (k + 1)..n {
            lu[i][k] /= lu[k][k];
            for j in (k + 1)..n {
                lu[i][j] -= lu[i][k] * lu[k][j];
            }
        }
    }

    Some((lu, pivots))
}

/// Solve LU * x = b using forward/back substitution.
fn lu_solve(lu: &[Vec<f64>], pivots: &[usize], b: &[f64], n: usize) -> Vec<f64> {
    // Apply permutation
    let mut pb = vec![0.0; n];
    for i in 0..n {
        pb[i] = b[pivots[i]];
    }

    // Forward substitution (L * y = pb)
    for i in 1..n {
        for j in 0..i {
            pb[i] -= lu[i][j] * pb[j];
        }
    }

    // Back substitution (U * x = y)
    for i in (0..n).rev() {
        for j in (i + 1)..n {
            pb[i] -= lu[i][j] * pb[j];
        }
        pb[i] /= lu[i][i];
    }

    pb
}

/// Fallback: estimate lambda_2 using direct Rayleigh quotient minimization.
fn rayleigh_quotient_fallback(laplacian: &[Vec<f64>], n: usize) -> f64 {
    // Power method on L to find the LARGEST eigenvalue, then use
    // (trace - lambda_max) as an upper bound heuristic. But that's crude.
    // Instead, try a simple subspace iteration approach.

    let mut x: Vec<f64> = (0..n)
        .map(|i| if i % 2 == 0 { 1.0 } else { -1.0 })
        .collect();
    normalize(&mut x);

    let inv_sqrt_n = 1.0 / (n as f64).sqrt();
    let ones: Vec<f64> = vec![inv_sqrt_n; n];

    for _iter in 0..500 {
        let mut y = mat_vec(laplacian, &x, n);
        // Deflect from null space
        let proj = dot(&y, &ones);
        for yi in y.iter_mut() {
            *yi -= proj * inv_sqrt_n;
        }
        normalize(&mut y);

        // Also deflect x from null space
        let proj_x = dot(&y, &ones);
        for yi in y.iter_mut() {
            *yi -= proj_x * inv_sqrt_n;
        }
        normalize(&mut y);
        x = y;
    }

    let lx = mat_vec(laplacian, &x, n);
    let lambda = dot(&x, &lx) / dot(&x, &x);
    lambda.max(0.0)
}

#[cfg(test)]
mod tests {
    use super::spectral_analysis;
    use crate::{
        Decision, EdgeTransform, GateLogic, GovernanceClaim, GovernanceNode, GraphBuilder, NodeId,
    };
    use std::collections::BTreeMap;

    #[test]
    fn single_node_graph_has_no_spectral_gap() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(simple_node("a")))
            .and_then(GraphBuilder::build)
            .unwrap();

        let result = spectral_analysis(&graph, &[]);

        assert_eq!(result.node_count, 1);
        assert!(result.spectral_gap.is_none());
        assert!(result.is_connected);
    }

    #[test]
    fn two_node_connected_graph_has_positive_spectral_gap() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(simple_node("a")))
            .and_then(|builder| builder.add_node(simple_node("b")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("a").unwrap(),
                    NodeId::new("b").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap();
        let claims = vec![claim("x", 0.5), claim("y", 1.0)];

        let result = spectral_analysis(&graph, &claims);

        assert_eq!(result.node_count, 2);
        assert_eq!(result.edge_count, 1);
        assert!(result.is_connected);
        assert!(result.spectral_gap.is_some());
        let gap = result.spectral_gap.unwrap();
        assert!(gap > 1.5, "lambda_2 of K2 should be 2.0, got {gap}");
        assert_eq!(result.max_degree, 1);
        assert!((result.signal_range - 0.5).abs() < 0.01);
    }

    #[test]
    fn disconnected_graph_has_zero_spectral_gap() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(simple_node("a")))
            .and_then(|builder| builder.add_node(simple_node("b")))
            .and_then(GraphBuilder::build)
            .unwrap();

        let result = spectral_analysis(&graph, &[]);

        assert!(!result.is_connected);
        assert_eq!(result.connected_components, 2);
        assert_eq!(result.lambda_2, 0.0);
        assert!(result.spectral_gap.is_none());
        assert!(result.rg_trajectory.is_none());
    }

    #[test]
    fn linear_three_node_graph_spectral_gap() {
        // Path graph P3: a-b-c
        // Laplacian eigenvalues: 0, 1, 3 -> lambda_2 = 1
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(simple_node("a")))
            .and_then(|builder| builder.add_node(simple_node("b")))
            .and_then(|builder| builder.add_node(simple_node("c")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("a").unwrap(),
                    NodeId::new("b").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("b").unwrap(),
                    NodeId::new("c").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap();
        let claims = vec![claim("x", 0.1), claim("y", 0.9)];

        let result = spectral_analysis(&graph, &claims);

        assert!(result.is_connected);
        let gap = result.spectral_gap.unwrap();
        assert!(
            (gap - 1.0).abs() < 0.1,
            "lambda_2 of P3 should be ~1.0, got {gap}"
        );
        assert_eq!(result.max_degree, 2);
        assert_eq!(result.min_removed_deg, 0);
        assert!((result.signal_range - 0.8).abs() < 0.01);
        assert!(result.cv_bound.is_some());
        assert!(result.capacity.is_none());
        assert!(result.localizability_bound.is_some());
    }

    #[test]
    fn triangle_graph_has_finite_capacity() {
        let graph = GraphBuilder::new()
            .and_then(|builder| builder.add_node(simple_node("a")))
            .and_then(|builder| builder.add_node(simple_node("b")))
            .and_then(|builder| builder.add_node(simple_node("c")))
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("a").unwrap(),
                    NodeId::new("b").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("b").unwrap(),
                    NodeId::new("c").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(|builder| {
                builder.add_edge(
                    NodeId::new("a").unwrap(),
                    NodeId::new("c").unwrap(),
                    EdgeTransform::PassThrough,
                )
            })
            .and_then(GraphBuilder::build)
            .unwrap();
        let claims = vec![claim("x", 1.0), claim("y", 2.0), claim("z", 3.0)];

        let result = spectral_analysis(&graph, &claims);

        assert_eq!(result.max_degree, 2);
        assert_eq!(result.min_removed_deg, 1);
        assert_eq!(result.capacity, Some(4.0));
        assert!(result.capacity_saturated_at(1.0));
        assert!(!result.capacity_saturated_at(5.0));
    }

    fn simple_node(id: &str) -> GovernanceNode {
        GovernanceNode::Binary {
            id: NodeId::new(id).unwrap(),
            name: id.to_string(),
            gates: Vec::new(),
            default: Decision::Escalate,
            combination: GateLogic::FirstMatch,
        }
    }

    fn claim(id: &str, strength: f64) -> GovernanceClaim {
        GovernanceClaim {
            claimant_id: id.to_string(),
            strength,
            priority_class: None,
            path: None,
            action: None,
            content: None,
            metrics: BTreeMap::new(),
        }
    }
}
