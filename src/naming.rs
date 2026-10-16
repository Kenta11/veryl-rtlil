//! Names as the Veryl SystemVerilog emitter produces them, so that the
//! top-level ports and module names of the RTLIL match the SV path.

use veryl_analyzer::ir::{Signature, TypeKind};
use veryl_analyzer::symbol_table;
use veryl_metadata::{Build, ClockType, ResetType};
use veryl_parser::resource_table;

/// Project a module symbol belongs to (first namespace segment).
pub fn project_of(sig: &Signature) -> Option<String> {
    let symbol = symbol_table::get(sig.symbol)?;
    let first = symbol.namespace.paths.first()?;
    resource_table::get_str_value(*first)
}

/// Module name as emitted into SystemVerilog.
pub fn sv_module_name(sig: &Signature, name: &str, omit_project_prefix: bool) -> String {
    match project_of(sig).as_deref() {
        Some("std") | Some("$std") => format!("__std_{name}"),
        Some(prj) if !omit_project_prefix => format!("{prj}_{name}"),
        _ => name.to_string(),
    }
}

/// Prefix / suffix the emitter attaches to a default-kind clock or reset
/// signal name.
pub fn clock_reset_affix(kind: &TypeKind, build: &Build) -> (Option<String>, Option<String>) {
    match kind {
        TypeKind::Clock => match build.clock_type {
            ClockType::PosEdge => (
                build.clock_posedge_prefix.clone(),
                build.clock_posedge_suffix.clone(),
            ),
            ClockType::NegEdge => (
                build.clock_negedge_prefix.clone(),
                build.clock_negedge_suffix.clone(),
            ),
        },
        TypeKind::Reset => match build.reset_type {
            ResetType::AsyncHigh | ResetType::SyncHigh => (
                build.reset_high_prefix.clone(),
                build.reset_high_suffix.clone(),
            ),
            ResetType::AsyncLow | ResetType::SyncLow => (
                build.reset_low_prefix.clone(),
                build.reset_low_suffix.clone(),
            ),
        },
        _ => (None, None),
    }
}

pub fn apply_affix(name: &str, kind: &TypeKind, build: &Build) -> String {
    let (p, s) = clock_reset_affix(kind, build);
    format!(
        "{}{}{}",
        p.unwrap_or_default(),
        name,
        s.unwrap_or_default()
    )
}
