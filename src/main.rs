use std::path::PathBuf;

use clap::Parser;
use miette::{IntoDiagnostic, Result};
use veryl::incremental::OutputIntent;
use veryl::pipeline::{self, AnalyzeOptions};
use veryl_analyzer::ir::Ir;
use veryl_metadata::Metadata;
use veryl_rtlil::{Options, translate_ir};

/// Translate a Veryl project into Yosys RTLIL.
///
/// Run inside a Veryl project (where `Veryl.toml` is found).  Every module
/// of the project (and its dependencies) is translated; modules that use
/// constructs outside pure Veryl are reported and skipped.
#[derive(Parser, Debug)]
#[command(name = "veryl-rtlil", version, about)]
struct Opt {
    /// Target files (default: all project sources)
    files: Vec<PathBuf>,

    /// Output `.il` path (default: stdout)
    #[arg(short, long)]
    output: Option<PathBuf>,

    /// Only keep these top modules (Veryl names) and their children
    #[arg(long)]
    top: Vec<String>,

    /// Print a `STATUS <sv_name> <rtlil_name|-> [reason]` line per module
    /// to stderr
    #[arg(long)]
    report: bool,

    /// Largest array (bits) that may be written through a dynamic index
    #[arg(long, default_value_t = 1 << 24)]
    max_dynamic_bits: usize,
}

fn main() -> Result<()> {
    env_logger::init();
    let opt = Opt::parse();

    let metadata_path = Metadata::search_from_current().into_diagnostic()?;
    let mut metadata = Metadata::load(metadata_path).into_diagnostic()?;
    let paths = metadata
        .paths(&opt.files, true, true)
        .into_diagnostic()?;

    let options = AnalyzeOptions {
        defines: &[],
        output_intent: OutputIntent::Never,
        incremental: false,
        fail_fast: true,
    };
    let mut ir = Ir::default();
    let _ = pipeline::analyze(&metadata, &paths, options, Some(&mut ir), None)?;

    let topts = Options {
        omit_project_prefix: metadata.build.omit_project_prefix,
        build: metadata.build.clone(),
        max_dynamic_bits: opt.max_dynamic_bits,
    };
    let (mut design, report) = translate_ir(&ir, &topts);

    if !opt.top.is_empty() {
        let keep: std::collections::HashSet<String> = report
            .modules
            .iter()
            .filter(|m| opt.top.contains(&m.name))
            .filter_map(|m| m.rtlil_name.clone())
            .collect();
        // Keep the requested tops and everything they instantiate.
        let mut live = keep.clone();
        let mut changed = true;
        while changed {
            changed = false;
            for m in &design.modules {
                let n = m.name.trim_start_matches('\\').to_string();
                if !live.contains(&n) && !live.contains(&m.name) {
                    continue;
                }
                for c in &m.cells {
                    if c.kind.starts_with('$') && !c.kind.starts_with("$paramod") {
                        continue;
                    }
                    let cn = c.kind.trim_start_matches('\\').to_string();
                    if live.insert(cn) {
                        changed = true;
                    }
                }
            }
        }
        design.modules.retain(|m| {
            let n = m.name.trim_start_matches('\\').to_string();
            live.contains(&n) || live.contains(&m.name)
        });
    }

    if opt.report {
        for m in &report.modules {
            match (&m.rtlil_name, &m.error) {
                (Some(r), _) => eprintln!("OK {} {} {}", m.sv_name, r, m.project.as_deref().unwrap_or("-")),
                (None, Some(e)) => eprintln!("SKIP {} - {} {}", m.sv_name, m.project.as_deref().unwrap_or("-"), e),
                _ => {}
            }
        }
    }

    let il = design.to_il();
    match &opt.output {
        Some(p) => std::fs::write(p, il).into_diagnostic()?,
        None => print!("{il}"),
    }
    Ok(())
}
