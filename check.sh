#!/bin/bash
# Compile one file, showing only errors/warnings that matter; prints OK if clean.
export PATH=$HOME/.elan/bin:$PATH
cd "$(dirname "$0")"
out=$(lake env lean -Dlinter.unusedSectionVars=false -Dweak.linter.mathlibStandardSet=false "$@" 2>&1 | grep -v "deprecated\|^  .*̵\|^$\|^  • ")
if [ -z "$out" ]; then echo OK; else echo "$out"; fi
