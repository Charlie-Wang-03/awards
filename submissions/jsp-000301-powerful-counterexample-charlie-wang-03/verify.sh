#!/usr/bin/env bash
set -euo pipefail

lake exe cache get
lake build
lake env lean Audit.lean

printf '\nSHA-256 proof/toolchain manifest\n'
sha256sum \
  JSP000301.lean \
  Audit.lean \
  lakefile.lean \
  lake-manifest.json \
  lean-toolchain
