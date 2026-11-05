# Coherent nine-phase threshold verification

2026-11-05. This source follows the safely pushed research checkpoint
`0f1f14fbd6ef0261ce05443655b8a84293ba8de9`. It proves family B at n=4 and
the original lower bound for every 3<=N<=40. General B for n>=5 remains open.

- `lake build JSP000404Research.OriginalFortyCases`: exit 0, 3,272 jobs.
- `lake env lean verification/nine-phase-threshold-20261105/Audit.lean`:
  exit 0, **64 research modules / 1,088 declarations / zero failures**.
  Private declarations and all transitive dependencies are included.
  Only `propext`, `Classical.choice`, and `Quot.sound` occur.
- `lake env lean JSP000404Research.lean`: exit 0, empty output, after the
  new original-forty-cases import was added.
- `python -B scripts/check_nine_phase_capacity.py --output REPORT.json`:
  independent exhaustive finite check, PASS. This uses only the Python
  standard library. The actual geometric bridge is verified in Lean.
- All ten pinned dependency revisions and tracked trees pass; see
  `dependencies.json`. Lean is 4.34.0 and Mathlib is
  `5ed2965256430c3649e86755f9576b54eca72435`.

`generate_nine_phase_data.py`, `generate_nine_phase_boolean_certificate.py`,
and `generate_nine_phase_matching.py` in `../../scripts/` reproduce the
three generated Lean files byte-for-byte. Run from the project directory.
The Boolean generator constructs its own elementary search proof. The
generated proof uses only explicit Boolean cases and equality rewrites;
its axioms are `[propext]`. No SAT solver is required for reproduction.

The new Lean sources contain no `sorry`, `admit`, `native_decide`, or new
axiom. The historical admitted WIP stays outside this imported closure.
`../../NINE_PHASE_CAPACITY_PROOF.md` contains the complete written argument
and its exact scope. The initial user checkpoint `e2168310` is preserved.
All-N epsilon sharpness retains its previously recorded external attribution.
No upstream award record or catalog has been modified.

Committed logs are normalized to UTF-8/LF and trailing diagnostic whitespace
is trimmed. Raw logs remain in `artifacts/`. `source-sha256.json` records
canonical source/evidence hashes and raw-stream hashes. The historical
full-root audit is not represented as an audit of this checkpoint.
