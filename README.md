# veryl-rtlil

Translate [Veryl](https://veryl-lang.org/) designs into Yosys RTLIL so that
pure Veryl can be synthesized by [Yosys](https://github.com/YosysHQ/yosys)
directly, without going through the SystemVerilog that Veryl emits.

```
veryl-rtlil -o design.il          # inside a Veryl project
yosys -p 'read_rtlil design.il; synth_ice40 -top prj_top -json top.json'
```

Install it next to `veryl` and it also works as an external subcommand:

```
cargo install --path .
veryl rtlil -o design.il
```

## What it does

The Veryl analyzer already elaborates a design into a monomorphized IR
(`veryl_analyzer::ir`) that the native simulator and `veryl synth` consume.
This tool is one more consumer of that IR:

- every module body becomes one RTLIL module; instantiated copies of generic
  or parameterized modules get `$paramod`-style names,
- `always_comb` / `assign` / `always_ff` blocks become RTLIL processes whose
  switch/case trees the Yosys `proc` pass lowers to cells; `if_reset`
  becomes an asynchronous or synchronous reset according to the reset type,
- expressions become word-level cells (`$add`, `$mux`, `$shiftx`, ...)
  sized by the IEEE 1800 width and signedness rules, so the result matches
  what the emitted SystemVerilog means,
- functions are inlined, loops are unrolled (including loops whose bounds
  are computed by earlier statements), packed types follow the SystemVerilog
  packed layout, and unpacked arrays are flattened with element 0 at the
  MSB side, as `read_slang` does.

Only pure Veryl is handled.  Anything that reaches into SystemVerilog
(`$sv::` references, embedded SV modules), testbench constructs
(`initial` with assignments, hierarchical references), strings and floats
are reported with a reason and the module is skipped.  Uninstantiated
generic modules have no concrete body and are skipped as well.

## Specification: equivalence with the SystemVerilog path

The intended meaning of the translation is "functionally equivalent to the
SystemVerilog Veryl emits, as read by Yosys' `read_slang` (sv-elab)".  The
`scripts/` directory holds the harness that checks exactly that:

```
scripts/run_all.sh -C <veryl project> -f <project>.f -o summary.txt
```

For every module of the project it reads the emitted SystemVerilog with
`read_slang` and the generated RTLIL with `read_rtlil`, normalizes both
(`proc; flatten; async2sync; memory_map`) and proves them equivalent with
`equiv_make` / `equiv_simple` / `equiv_induct`.  `scripts/equiv.sh` checks a
single module; `scripts/one.sh` is a debugging helper that also prints a
counterexample.

Status on Veryl 0.22.0 (Yosys 0.70 from oss-cad-suite):

| project                         | equivalent | skipped (reason)                        | no SV counterpart |
|---------------------------------|-----------:|-----------------------------------------|------------------:|
| `veryl` repository `testcases/` | 150        | 31 (SV embedding, generics, floats, ...) | 40 |
| `crates/std/veryl` (std lib)    | 28         | 17 (test modules with `initial`)        | 4 (generic) |
| `tests/constructs` (this repo)  | 85         | 0                                       | 3 (interface port / generic) |

"No SV counterpart" are modules that sv-elab cannot read as a top (interface
ports, external SystemVerilog packages, generic modules).  `scripts/test_constructs.sh`
runs the construct suite.  One known limit of the prover rather than the
translation: a `**` with a non-constant exponent becomes a `$pow` cell on both
sides, which Yosys' SAT backend cannot model.

## Requirements

- Rust (edition 2024)
- the `veryl` crates, pinned to the exact Veryl release the tool is built
  for (`Cargo.toml`); the project must be built with that same Veryl
- Yosys 0.67 or newer with the sv-elab frontend for the equivalence scripts

## Layout

- `src/rtlil.rs`     - in-memory RTLIL model, writer and constant folding
- `src/translate.rs` - IR to RTLIL translation
- `src/naming.rs`    - names as the Veryl SystemVerilog emitter produces them
- `src/main.rs`      - command line
- `scripts/`         - equivalence harness

## License

MIT OR Apache-2.0
