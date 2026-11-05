# Integral coding and cut-order verification

2026-11-05. This continuation starts after
`afe0cc61db8ba1b6c9c7235a88b5ade47146f0fe`, which was safely pushed with local,
tracking, and remote SHAs equal. The complete JSP-000404 goal remains open.

The focused build covers `IntegralWireCapacity` and `DirectionCutOrder` and
uses the pinned Lean 4.34.0 / Mathlib dependencies checked in the preceding
cyclic-wire checkpoint. Both modules are standalone at this stage. The
umbrella source has not gained these two imports, and its previous file check
continues to refer to the preceding imported closure.

`Audit.lean` prints three statements and eight transitive axiom lists.
The source payloads are recorded by canonical UTF-8/LF SHA-256 digests.
The source scan excludes executable `sorry`, `admit`, and new axioms.

The final focused build passed with exit 0 and 3,098 Lake jobs. The audit
passed with exit 0. Its eight queries report only `propext`, `Classical.choice`,
and `Quot.sound`. The logs contain the executed output. No full umbrella
rebuild was performed for these standalone additions.

The integer coding theorem retains the incident-time gap hypotheses and the
common event separating each pair of centres. The cut-order theorem retains
triangle betweenness. The actual cyclic event graph and its winding theorem
still have to be constructed, and family B remains open. The written route
and the remaining connections are in `CYCLIC_WIRE_RETIMING.md`.

Reproduce the focused checks from the research project directory with

```powershell
$env:LEAN_NUM_THREADS='2'
lake build JSP000404Research.IntegralWireCapacity JSP000404Research.DirectionCutOrder
lake env lean verification/integral-wire-20261105/Audit.lean
```
