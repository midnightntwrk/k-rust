#!/usr/bin/env bash
# Runs the regression-new conformance driver. Usage: run.sh [--jobs N] [--cases name...]
set -u
cd "$(dirname "$0")"
exec python3 run.py "$@"
