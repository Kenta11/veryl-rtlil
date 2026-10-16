#!/usr/bin/env bash
# Debug helper: check one module of the Veryl testcase project and show the
# unproven signals.   one.sh <sv_module> [rtlil_module]
set -u
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PRJ="${PRJ:-/home/kenta/projects/veryl-elab/repos/veryl-0.22.0}"
export YOSYS="${YOSYS:-/home/kenta/projects/veryl-elab/tools/oss-cad-suite/bin/yosys}"
export FULL_FILELIST="$PRJ/veryl_testcase.f"
SC="${SC:-/tmp/claude-1000/-home-kenta-projects-veryl-elab/ddbb9152-b647-403e-a820-c27fba7bc8f6/scratchpad}"
m="$1"; r="${2:-$1}"
if [ -n "${VTOP:-}" ]; then
  (cd "$PRJ" && "$here/../target/release/veryl-rtlil" --top "$VTOP" -o "$SC/one.il" >/dev/null 2>&1)
elif [ ! -f "$SC/one.il" ] || [ -n "${RETRANSLATE:-}" ]; then
  (cd "$PRJ" && "$here/../target/release/veryl-rtlil" -o "$SC/one.il" >/dev/null 2>&1)
fi
out="$("$here/equiv.sh" -f "$SC/clean.f" -i "$SC/one.il" -g "$m" -r "$r" -k 2>&1)"
echo "$out" | grep -v '^work:'
W="$(echo "$out" | grep '^work:' | awk '{print $2}')"
echo "work: $W"
if [ -f "$W/equiv.log" ]; then /usr/bin/grep -A40 'Unproven' "$W/equiv.log" | /usr/bin/grep -E 'Unproven|\$equiv' | head -${N:-20}; fi
if [ -n "${CEX:-}" ] && [ -f "$W/gate.il" ]; then
  # Counterexample via a miter: comb only (seq 0) unless SEQ is given.
  "$YOSYS" -q -l "$W/cex.log" -p "read_rtlil $W/gold.il; read_rtlil $W/gate.il; miter -equiv -flatten -make_assert gold gate miter; hierarchy -top miter; sat -verify -prove-asserts -show-inputs -show-outputs -set-init-undef -seq ${SEQ:-1} miter" >/dev/null 2>&1
  /usr/bin/grep -E '^\s+(\\|Time|Signal Name|----)' "$W/cex.log" | /usr/bin/grep -v '^\s*$' | head -${NC:-60}
fi
