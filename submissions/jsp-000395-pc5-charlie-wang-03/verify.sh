#!/usr/bin/env bash
set -euo pipefail

lake exe cache get
lake build
lake env lean Audit.lean

printf '\nSHA-256 proof/toolchain manifest\n'
sha256sum \
  PC5488.lean \
  PC5488/Aggregate.lean \
  PC5488/Basic.lean \
  PC5488/Bonferroni.lean \
  PC5488/Final.lean \
  PC5488/Overlap.lean \
  Audit.lean \
  lakefile.lean \
  lake-manifest.json \
  lean-toolchain
