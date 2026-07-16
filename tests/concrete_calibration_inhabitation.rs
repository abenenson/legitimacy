use std::{
    env, fs,
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

fn temp_lean_path(label: &str) -> std::path::PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time before UNIX_EPOCH")
        .as_nanos();
    env::temp_dir().join(format!("legitimacy-{label}-{nanos}.lean"))
}

#[test]
fn concrete_noisy_cstar_calibration_has_inhabitant() {
    let lean_file = "lean/Legitimacy/Spectral/Channels/ConcreteNoisyChannel.lean";
    let source = fs::read_to_string(lean_file).expect("read ConcreteNoisyChannel.lean");

    assert!(
        source.contains("noncomputable def concreteHalfNoisyCStarCalibration"),
        "expected a concrete ConcreteNoisyCStarCalibration inhabitant"
    );
    assert!(
        source.contains("ConcreteNoisyCStarCalibration uniTriGraph halfSig"),
        "expected the inhabitant to target the half-scale triangle fixture"
    );
    assert!(
        source.contains("theorem concreteHalfNoisyCStarCalibration_capacity_eq_true"),
        "expected a closed theorem exposing the inhabitant capacity equality"
    );
    assert!(
        source.contains("noncomputable def concreteAsymTriHalfNoisyCStarCalibration"),
        "expected an asymmetric-triangle ConcreteNoisyCStarCalibration inhabitant"
    );
    assert!(
        source.contains("ConcreteNoisyCStarCalibration asymTriGraph asymTriHalfSig"),
        "expected the asymmetric-triangle inhabitant to target the half-scale fixture"
    );
    assert!(
        source.contains("noncomputable def concreteNearPathHalfNoisyCStarCalibration"),
        "expected a near-path ConcreteNoisyCStarCalibration inhabitant"
    );
    assert!(
        source.contains("ConcreteNoisyCStarCalibration nearPathGraph nearPathHalfSig"),
        "expected the near-path inhabitant to target the half-scale fixture"
    );
    assert!(
        source.contains("noncomputable def concreteBottleneckHalfNoisyCStarCalibration"),
        "expected a bottleneck ConcreteNoisyCStarCalibration inhabitant"
    );
    assert!(
        source.contains("ConcreteNoisyCStarCalibration bottleneckGraph bottleneckHalfSig"),
        "expected the bottleneck inhabitant to target the half-scale fixture"
    );
    assert!(
        source.contains("noncomputable def concreteUniK5HalfNoisyCStarCalibration"),
        "expected a uniform-K5 ConcreteNoisyCStarCalibration inhabitant"
    );
    assert!(
        source.contains("ConcreteNoisyCStarCalibration uniK5 uniK5HalfSig"),
        "expected the uniform-K5 inhabitant to target the half-scale fixture"
    );
    assert!(
        source.contains("existsConcreteNoisyCStarCalibration_of_cv_pos_lt_log_two"),
        "expected the parametric erasure-channel calibration inhabitant"
    );

    let graph_status = Command::new("lake")
        .args(["build", "Legitimacy.Spectral.Core.ConcreteGraphs"])
        .current_dir("lean")
        .status()
        .expect("build concrete graph fixtures");
    assert!(
        graph_status.success(),
        "Concrete graph fixture build failed"
    );

    let status = Command::new("lake")
        .args([
            "env",
            "lean",
            "Legitimacy/Spectral/Channels/ConcreteNoisyChannel.lean",
        ])
        .current_dir("lean")
        .status()
        .expect("run Lean inhabitation check");
    assert!(status.success(), "Lean inhabitation check failed");
}

#[test]
fn parametric_calibration_constructs_adhoc_two_node_witness() {
    let lean_path = temp_lean_path("adhoc-calibration");
    let lean_source = r#"
import Legitimacy.Spectral.Channels.ConcreteNoisyChannel

set_option autoImplicit false

namespace Legitimacy

open GovernanceChannel

def adhocTwoNodeGraph : GovGraph Rat 2 where
  weights := !![0, 1; 1, 0]
  weight_symm := by decide
  weight_nonneg := by decide
  weight_self_zero := by decide

def adhocTwoNodeSignal : Fin 2 -> Rat := ![0, 1 / 3]

lemma adhocTwoNodeGraph_cv :
    adhocTwoNodeGraph.cv adhocTwoNodeSignal = 1 / 3 := by
  native_decide

example :
    Exists (fun _cal : ConcreteNoisyCStarCalibration adhocTwoNodeGraph adhocTwoNodeSignal =>
      True) :=
  existsConcreteNoisyCStarCalibration_of_cv_pos_lt_log_two
    adhocTwoNodeGraph
    adhocTwoNodeSignal
    (by
      rw [adhocTwoNodeGraph_cv]
      norm_num)
    (by
      rw [adhocTwoNodeGraph_cv]
      norm_num
      exact lt_trans (by norm_num : (1 / 3 : Real) < 0.6931471803) Real.log_two_gt_d9)

end Legitimacy
"#;

    fs::write(&lean_path, lean_source).expect("write ad-hoc Lean calibration check");

    let output = Command::new("lake")
        .args(["env", "lean", lean_path.to_str().expect("UTF-8 Lean path")])
        .current_dir("lean")
        .output()
        .expect("run ad-hoc Lean calibration check");

    let _ = fs::remove_file(&lean_path);

    assert!(
        output.status.success(),
        "ad-hoc parametric calibration check failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
