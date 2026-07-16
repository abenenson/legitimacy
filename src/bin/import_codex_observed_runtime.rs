use clap::Parser;
use legitimacy::import_codex_oss_story_corpus_pack;
use std::{path::PathBuf, process::ExitCode};

#[derive(Parser, Debug)]
#[command(
    name = "import_codex_observed_runtime",
    about = "Import Codex oss-story.jsonl into an observed-runtime corpus pack"
)]
struct Cli {
    #[arg(long)]
    input: PathBuf,
    #[arg(long)]
    output: PathBuf,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match import_codex_oss_story_corpus_pack(&cli.input, &cli.output) {
        Ok(pack) => {
            println!("OBSERVED RUNTIME CORPUS PACK");
            println!("output: {}", cli.output.display());
            println!("claims: {}", pack.manifest.claim_count);
            println!("source: {}", pack.manifest.source_descriptor);
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("legitimacy: {error}");
            ExitCode::from(1)
        }
    }
}
