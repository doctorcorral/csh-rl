#!/bin/bash
# Incremental workaround for the Agda 2.8.0 serialization bug:
# compile every module imported by All.agda individually (each compile
# is short and persists progress via .agdai), then check All.agda once.
cd "$(dirname "$0")" || exit 1
mods=$(grep -oE '^import [A-Za-z0-9._]+' src/All.agda | awk '{print $2}')
total=$(echo "$mods" | wc -l | tr -d ' ')
i=0
fail=0
for mod in $mods; do
  i=$((i+1))
  file="src/$(echo "$mod" | tr '.' '/').agda"
  echo "[$i/$total] $mod"
  agda "$file" > /tmp/agda_mod.log 2>&1
  if [ $? -ne 0 ]; then
    # Retry once: serialization crashes usually succeed on rerun
    agda "$file" > /tmp/agda_mod.log 2>&1
    if [ $? -ne 0 ]; then
      echo "  FAILED: $mod"
      tail -6 /tmp/agda_mod.log | sed 's/^/  | /'
      fail=1
    fi
  fi
done
if [ $fail -ne 0 ]; then
  echo "SOME MODULES FAILED"
  exit 1
fi
echo "all modules compiled; final All.agda check"
agda src/All.agda > /tmp/agda_all.log 2>&1
if [ $? -eq 0 ]; then
  echo "ALL_OK"
  exit 0
fi
# One retry for the serialization bug on All itself
agda src/All.agda > /tmp/agda_all.log 2>&1
if [ $? -eq 0 ]; then
  echo "ALL_OK (after retry)"
  exit 0
fi
echo "All.agda still failing:"
tail -12 /tmp/agda_all.log
exit 1
