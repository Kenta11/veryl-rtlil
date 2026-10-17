#!/usr/bin/env bash
# Drop files that sv-elab (read_slang) cannot read from a filelist, so the
# remaining set elaborates.  Prints the dropped files to stderr.
#
#   clean_filelist.sh <in.f> <out.f>

set -u
YOSYS="${YOSYS:-yosys}"
in="$1"
out="$2"
grep -v '^\s*$' "$in" | grep -v '^+' > "$out"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
for _ in $(seq 1 60); do
  echo "read_slang -f $out" > "$work/t.ys"
  if "$YOSYS" -q -l "$work/t.log" -s "$work/t.ys" >/dev/null 2>&1; then
    exit 0
  fi
  bad="$(grep -m1 -E '^[^ ]+\.sv:[0-9]+: ERROR' "$work/t.log" | sed -E 's/^([^:]+):.*/\1/')"
  if [ -z "$bad" ]; then
    # Internal error: blame the last file mentioned before it.
    bad="$(grep -B40 -m1 'ERROR' "$work/t.log" | grep -oE '^[^ ]+\.sv:[0-9]+' | tail -1 | sed -E 's/:[0-9]+$//')"
  fi
  if [ -z "$bad" ]; then
    grep -m3 -i error "$work/t.log" >&2
    exit 1
  fi
  echo "drop $bad: $(grep -m1 -E "^$bad:[0-9]+" "$work/t.log" | cut -c1-160)" >&2
  # slang reports paths relative to the working directory; compare resolved paths.
  badabs="$(realpath -m "$bad")"
  : > "$work/next.f"
  while IFS= read -r line; do
    [ "$(realpath -m "$line")" = "$badabs" ] || echo "$line" >> "$work/next.f"
  done < "$out"
  if cmp -s "$out" "$work/next.f"; then
    echo "cannot drop $bad" >&2
    exit 1
  fi
  mv "$work/next.f" "$out"
done
exit 1
