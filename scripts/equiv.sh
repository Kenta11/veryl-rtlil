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
norm='proc; flatten; async2sync; memory -nomap; memory_map; opt_clean; wreduce; opt_clean; setundef -undriven -undef'

# Gold is read from the smallest file set that elaborates: the module's own
# file, then whatever "unknown package/module/interface" errors ask for.
own="$(/usr/bin/grep -lzP "(^|\n)\s*(module|interface)(\s*//[^\n]*)?\s+$gold\b" $(cat "${FULL_FILELIST:-$filelist}") 2>/dev/null | head -1)"
if [ -z "$own" ]; then
  echo "GOLD_FAIL $gold: definition not found in the filelist"
  exit 2
fi
echo "$own" > "$work/files.f"
ok=0
for _ in $(seq 1 60); do
  {
    echo "read_slang -f $work/files.f --top $gold --unroll-limit 1000000"
    echo "hierarchy -top $gold"
    echo "$norm"
    echo "rename $gold gold"
    echo "write_rtlil $work/gold.il"
  } > "$work/gold.ys"
  if "$YOSYS" -q -l "$work/gold.log" -s "$work/gold.ys" >/dev/null 2>&1; then
    ok=1
    break
  fi
  missing="$(grep -m1 -oE "ERROR: unknown (class or package|package|module|interface|class) '[^']+'" "$work/gold.log" | sed -E "s/.*'([^']+)'/\1/")"
  if [ -z "$missing" ]; then
    break
  fi
  def="$(/usr/bin/grep -lzP "(^|\n)\s*(package|module|interface)(\s*//[^\n]*)?\s+$missing\b" $(cat "${FULL_FILELIST:-$filelist}") 2>/dev/null | head -1)"
  if [ -z "$def" ] || grep -q -F "$def" "$work/files.f"; then
    break
  fi
  echo "$def" >> "$work/files.f"
done
if [ "$ok" != 1 ]; then
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
  echo "equiv_simple -undef -seq $seq"
  echo "equiv_induct -undef -seq $seq"
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
