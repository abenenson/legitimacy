use clap::Args;
use legitimacy::{
    GovernanceGraph, LegitimacyError,
    extract::{AstTheoremWitness, ast_theorem_witness, verify_ast_theorem_witness},
};
use std::{
    fs,
    path::{Path, PathBuf},
    process::ExitCode,
};

use crate::{input::load_governance_graph, reporting::pretty_json};

#[derive(Args, Debug)]
pub(crate) struct VerifyWitnessCommand {
    /// The AST theorem witness JSON emitted by `extract --emit-theorem-witness`.
    pub(crate) witness: PathBuf,
    /// Source directory whose canonical parsed AST should match the witness.
    #[arg(long)]
    pub(crate) source_dir: PathBuf,
    /// Governance graph JSON whose canonical hash should match the witness.
    #[arg(long)]
    pub(crate) graph: PathBuf,
}

pub(crate) fn write_ast_theorem_witness(
    path: &Path,
    source_dir: &Path,
    graph: &GovernanceGraph,
    theorem_name: &str,
) -> Result<(), LegitimacyError> {
    let witness = ast_theorem_witness(source_dir, graph, theorem_name)?;
    fs::write(
        path,
        serde_json::to_vec_pretty(&witness).map_err(|source| LegitimacyError::Serialize {
            context: format!("AST theorem witness '{}'", path.display()),
            source,
        })?,
    )
    .map_err(|source| LegitimacyError::Io {
        context: format!("writing AST theorem witness '{}'", path.display()),
        source,
    })
}

pub(crate) fn run(command: VerifyWitnessCommand) -> Result<ExitCode, LegitimacyError> {
    let input = fs::read_to_string(&command.witness).map_err(|source| LegitimacyError::Io {
        context: format!(
            "reading AST theorem witness '{}'",
            command.witness.display()
        ),
        source,
    })?;
    let witness: AstTheoremWitness =
        serde_json::from_str(&input).map_err(|source| LegitimacyError::Json {
            context: format!("AST theorem witness '{}'", command.witness.display()),
            source,
        })?;
    let graph = load_governance_graph(&command.graph)?;
    let verification = verify_ast_theorem_witness(&witness, &command.source_dir, &graph)?;
    println!("{}", pretty_json(&verification)?);
    if verification.witness_valid {
        Ok(ExitCode::SUCCESS)
    } else {
        Ok(ExitCode::from(2))
    }
}
