# Critical-root clocks with no consecutive five-coordinate encoding

This checkpoint follows `8ab0ba13afca4e62ad92ee172dc341dd86b947ff`.
It excludes a proposed restriction in the remaining family-B investigation.
The complete family-A proof is recorded at `449be4d2f099c853ea1f1e052456101b4106ace6`.
Family B and the original all-N theorem remain open.

`witnesses.json` contains two coherent schedules, with `(N,q)=(11,11)` and
`(17,9)`, where q is the doubled half-period. The checker reconstructs every
consecutive and closing wire arc from the supplied adjacent-swap reversal.
It verifies every integer clock inequality, a zero-weight critical cycle,
and a tight path from every event to a root on that cycle.

These data certify more than feasibility. The positive winding of the
critical cycle bounds every feasible period below by q. The exhibited
clock attains q. After subtracting the clock value at the root, telescoping
the inequalities along any root path bounds its weight below by the event's
clock. The stored tight path attains that bound. The clock is consequently
the critical-root shortest-path potential for its fixed cyclic wire order.

For every consecutive block of five phase coordinates and either common
polarity, the checker enumerates the five maximal independent sets of the
core cycle and finds an incompatible row. This covers 22 choices for the
first witness and 18 for the second. A sparse core succeeds in both cases,
and the earlier positive-encoding checker verifies all distinct codes and
the complete graph families of 40 and 20 maximal independent sets.

Run from the research project directory with assertions enabled.

```powershell
python -B scripts/check_critical_clock_core_obstruction.py
```

The independent check passed under Python 3.12.13 with exit 0. Its output is
`check.log`. The search used Z3, while replay needs only the Python standard
library. The original search files remain in the ignored `artifacts/`
directory. The finite witnesses are outside the Lean proof chain, and their
Euclidean realizations are unverified.

The accompanying research note also proves a matching simplification in
ordinary mathematics. Any cyclic pair-deletion encoding can use matching
edges from the original coordinate cycle, with the same retained core.
Thus searching cores with odd cyclic gaps suffices. The general existence
of an appropriate core and selected retiming remains the open obligation.

Canonical UTF-8/LF source hashes are recorded in `source-sha256.json`.
