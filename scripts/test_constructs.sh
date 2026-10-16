#!/usr/bin/env bash
# Build the construct tests with Veryl and check every module against the
# SystemVerilog path.  Needs `veryl` (matching the pinned version) and
# `yosys` (or YOSYS=...) with read_slang.
set -eu
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
prj="$here/../tests/constructs"
(cd "$prj" && "${VERYL:-veryl}" build >/dev/null)
"$here/run_all.sh" -C "$prj" -f "$prj/constructs.f" -o "$prj/summary.txt" "$@"
if grep -q '^FAIL\|^GATE_FAIL' "$prj/summary.txt"; then
  grep '^FAIL\|^GATE_FAIL' "$prj/summary.txt"
  exit 1
fi
