#!/usr/bin/env bash
# Translate a Veryl project and check every translated module against the
# SystemVerilog Veryl emitted for it.
#
#   run_all.sh -C <project dir> -f <sv filelist> [-o <summary>] [-j <jobs>] [-s <seq>]
#
# The project must have been built with `veryl build` (so the .sv files and
# the filelist exist).  Writes one line per module to the summary:
#   PASS <sv_name> | FAIL <sv_name>: reason | GOLD_FAIL ... | GATE_FAIL ... |
#   SKIP <sv_name>: reason (translator rejected the module)

set -u
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERYL_RTLIL="${VERYL_RTLIL:-$here/../target/release/veryl-rtlil}"
jobs=16
seq=4
summary=""
while getopts "C:f:o:j:s:" opt; do
  case "$opt" in
    C) project="$OPTARG" ;;
    f) filelist="$OPTARG" ;;
    o) summary="$OPTARG" ;;
    j) jobs="$OPTARG" ;;
    s) seq="$OPTARG" ;;
    *) exit 1 ;;
  esac
done
: "${project:?-C required}" "${filelist:?-f required}"
filelist="$(cd "$(dirname "$filelist")" && pwd)/$(basename "$filelist")"
work="$(mktemp -d)"
[ -n "$summary" ] || summary="$work/summary.txt"

"$here/clean_filelist.sh" "$filelist" "$work/clean.f" 2>"$work/dropped.txt"
cat "$work/dropped.txt" >&2
# Every SystemVerilog file of the project (the filelist only names the
# files the project's own modules need).
{ cat "$filelist"; find "$project" -name '*.sv' -not -path '*/target/*' -not -path '*/.build/*' | sort; } | awk '!seen[$0]++' > "$work/full.f"
export FULL_FILELIST="$work/full.f"
filelist="$work/clean.f"
(cd "$project" && "$VERYL_RTLIL" --report -o "$work/design.il" 2>"$work/report.txt" >/dev/null)
grep -v '^\[INFO' "$work/report.txt" > "$work/report2.txt"

: > "$summary"
grep '^SKIP' "$work/report2.txt" | sed 's/^SKIP \([^ ]*\) - [^ ]* /SKIP \1: /' >> "$summary"

grep '^OK' "$work/report2.txt" | awk '{print $2, $3}' | \
  xargs -P "$jobs" -L 1 bash -c 'YOSYS="'"${YOSYS:-yosys}"'" "'"$here"'/equiv.sh" -f "'"$filelist"'" -i "'"$work"'/design.il" -g "$0" -r "$1" -s "'"$seq"'"' \
  >> "$summary" 2>/dev/null

echo "summary: $summary"
echo "PASS: $(grep -c '^PASS' "$summary")  FAIL: $(grep -c '^FAIL' "$summary")  GOLD_FAIL: $(grep -c '^GOLD_FAIL' "$summary")  GATE_FAIL: $(grep -c '^GATE_FAIL' "$summary")  SKIP: $(grep -c '^SKIP' "$summary")"
