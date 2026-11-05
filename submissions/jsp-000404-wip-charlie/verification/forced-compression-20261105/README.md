# Exact forced-compression obstruction

The nine-wire `witness.json` supplies a complete adjacent-swap refinement
at half-period 9/2. All arithmetic uses integer quarter units.

`scripts/check_forced_compression_obstruction.py` independently checks every
parent event and gap, all 512 colourings in twenty phase cases, and the
piecewise-affine threshold argument covering every real phase. The executed
output is in `check.log`. The certificate also gives a freely coloured
successful collapse, so the unrestricted unit-collapse candidate survives.

This is written and exact executable verification. Full Lean assembly is
pending. The mathematical argument and precise scope are in
`FORCED_INTERVAL_COMPRESSION_COUNTEREXAMPLE.md`. Source and data hashes are
in `source-sha256.json`.
