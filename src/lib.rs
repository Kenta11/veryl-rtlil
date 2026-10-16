//! veryl-rtlil: translate the Veryl analyzer IR into Yosys RTLIL.
//!
//! The spec for the translation is "functionally equivalent to the
//! SystemVerilog that Veryl emits, read by Yosys' `read_slang`".  Only pure
//! Veryl designs are handled; anything that reaches into SystemVerilog is
//! reported as unsupported.

pub mod error;
pub mod naming;
pub mod rtlil;
pub mod translate;

pub use error::TranslateError;
pub use translate::{Options, Report, translate_ir};
