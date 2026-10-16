#!/usr/bin/env bash
# Check that one module translated by veryl-rtlil is equivalent to the
# SystemVerilog emitted by Veryl, both read into Yosys.
#
#   equiv.sh -f <sv filelist> -i <design.il> -g <sv_top> -r <rtlil_top> [-s <seq>] [-k]
#
# -f  file with one SystemVerilog source path per line (Veryl's *.f)
# -i  RTLIL produced by veryl-rtlil
# -g  module name in the SystemVerilog (gold)
# -r  module name in the RTLIL (gate, without the leading backslash)
# -s  sequential depth for equiv_simple / equiv_induct (default 4)
# -k  keep the work directory and print its path
#
# Exit code: 0 equivalent, 1 not equivalent / failed, 2 gold could not be read,
# 3 gate could not be read.

set -u

YOSYS="${YOSYS:-yosys}"
seq=4
keep=0
while getopts "f:i:g:r:s:k" opt; do
  case "$opt" in
    f) filelist="$OPTARG" ;;
    i) il="$OPTARG" ;;
    g) gold="$OPTARG" ;;
    r) gate="$OPTARG" ;;
    s) seq="$OPTARG" ;;
    k) keep=1 ;;
    *) echo "bad option" >&2; exit 1 ;;
  esac
done
: "${filelist:?-f required}" "${il:?-i required}" "${gold:?-g required}" "${gate:?-r required}"

work="$(mktemp -d)"
cleanup() { if [ "$keep" = 0 ]; then rm -rf "$work"; else echo "work: $work" >&2; fi; }
trap cleanup EXIT

# Common normalisation applied to both sides.
norm='proc; flatten; async2sync; memory -nomap; memory_map; opt_clean; wreduce; opt_clean'

# The file defining the gold module; errors located in other files drop
# those files and retry.
cp "$filelist" "$work/files.f"
own="$(grep -l -E "^(module|interface) +$gold\b" $(cat "$work/files.f") 2>/dev/null | head -1)"
if [ -z "$own" ] && [ -n "${FULL_FILELIST:-}" ]; then
  # The module's file was dropped by the global cleaning; put it back.
  own="$(grep -l -E "^(module|interface) +$gold\b" $(cat "$FULL_FILELIST") 2>/dev/null | head -1)"
  [ -n "$own" ] && echo "$own" >> "$work/files.f"
fi
for _ in $(seq 1 40); do
  {
    echo "read_slang -f $work/files.f --top $gold"
    echo "hierarchy -top $gold"
    echo "$norm"
    echo "rename $gold gold"
    echo "write_rtlil $work/gold.il"
  } > "$work/gold.ys"
  if "$YOSYS" -q -l "$work/gold.log" -s "$work/gold.ys" >/dev/null 2>&1; then
    break
  fi
  bad="$(grep -m1 -E '^[^ ]+\.sv:[0-9]+: ERROR' "$work/gold.log" | sed -E 's/^([^:]+):.*/\1/')"
  if [ -z "$bad" ]; then
    bad="$(grep -B40 -m1 'ERROR' "$work/gold.log" | grep -oE '^[^ ]+\.sv:[0-9]+' | tail -1 | sed -E 's/:[0-9]+$//')"
  fi
  if [ -n "$bad" ] && [ "$bad" != "$own" ] && grep -q -F "$bad" "$work/files.f"; then
    grep -v -F "$bad" "$work/files.f" > "$work/files2.f"
    mv "$work/files2.f" "$work/files.f"
    continue
  fi
  echo "GOLD_FAIL $gold: $(grep -m1 'ERROR' "$work/gold.log" | cut -c1-200)"
  exit 2
done
if [ ! -f "$work/gold.il" ]; then
  echo "GOLD_FAIL $gold: $(grep -m1 'ERROR' "$work/gold.log" | cut -c1-200)"
  exit 2
fi

{
  echo "read_rtlil $il"
  echo "hierarchy -top $gate"
  echo "$norm"
  echo "rename $gate gate"
  echo "write_rtlil $work/gate.il"
} > "$work/gate.ys"
if ! "$YOSYS" -q -l "$work/gate.log" -s "$work/gate.ys" >/dev/null 2>&1; then
  echo "GATE_FAIL $gold: $(grep -m1 -i 'error' "$work/gate.log")"
  exit 3
fi

{
  echo "read_rtlil $work/gold.il"
  echo "read_rtlil $work/gate.il"
  echo "equiv_make gold gate equiv"
  echo "hierarchy -top equiv"
  echo "equiv_simple -seq $seq"
  echo "equiv_induct -seq $seq"
  echo "equiv_status -assert"
} > "$work/equiv.ys"
if "$YOSYS" -q -l "$work/equiv.log" -s "$work/equiv.ys" >/dev/null 2>&1; then
  echo "PASS $gold"
  exit 0
else
  reason="$(grep -m1 -E 'ERROR|Unproven|unproven' "$work/equiv.log" | head -c 300)"
  echo "FAIL $gold: $reason"
  exit 1
fi
