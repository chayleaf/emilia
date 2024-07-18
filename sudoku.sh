#!/usr/bin/env bash
if [ "$1" = "minisat" ]; then
  echo "[$(python3 sudoku.py to_sat | minisat /dev/stdin /dev/stderr 2>&1 >/dev/null | tail -n1 | sed 's/ 0//;s/-[0-9]\+/false/g;s/[0-9]\+/true/g;s/ /, /g')]" | python3 sudoku.py from_sat
else
  python3 sudoku.py to_sat | cargo run /dev/stdin | python3 sudoku.py from_sat
fi
