# Narrow-observer research verification

2026-11-05, Windows. The original arbitrary-N problem remains incomplete.
This checkpoint extends the preserved source history starting at
`e2168310a609cdbc29e987da325856b7e23a87b0`. The file hashes in
`source-sha256.json` identify the source payload checked here. These checks were
run in the working tree before saving its checkpoint commit.

## Executed checks

- Lean 4.34.0 with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
  All ten dependency heads match their manifest pins and have clean tracked
  trees. The snapshot is in `dependencies.json`.
- Focused targets `TwoObserverGeometry` and `IntervalPrivateDirections` built
  successfully, exit 0, 3,215 Lake jobs. Their dependency closure includes the
  new `NarrowObserverDirections` and `UpperHalfPlaneDirections` modules.
  `focused-build.log` contains the build output.
- The research umbrella at the four-module narrow-observer stage built
  incrementally, exit 0, 9,937 Lake jobs.
  The four new modules are imported by that umbrella. The last lines are in
  `umbrella-build-tail.log`. The full local stream is retained at
  `artifacts/narrow-observer-umbrella-build.log`, SHA-256
  `3707fc99b08b9f04832f10b801cf2b65d36208c818dae7b94d0b7a4988dac2af`.
- Subsequently `AffineTraceBound` built separately, exit 0, 3,092 jobs, with
  three standard-axiom queries. Its log is in
  `../affine-partition-20261105/trace-build.log`. After adding that import,
  `lake env lean JSP000404Research.lean` passed, exit 0, with empty compiler
  output. This final import check uses the already built dependency modules.
- `lake env lean verification/narrow-observer-20261105/Audit.lean` passed,
  exit 0. `audit.log` contains the actual statements and thirteen transitive
  axiom queries. Each query reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- The four new source modules contain no executable `sorry`, `admit`, or
  axiom declaration. `git diff --check` passed. The earlier admitted WIP and
  the missing original lower theorem remain outstanding.

The new coordinate-geometric theorem retains the actual angle cap and two
narrow-viewpoint hypotheses. The private-direction weighted theorems retain
the finite private sets and their separation hypotheses. Their connection to
the canonical gap exponent is a written proof still awaiting Lean assembly.
The previous 10,619-declaration audit belongs to its earlier immutable source,
as documented in `../windows-20261105/README.md`; it was not rerun here.

The new affine-partition counterexample has its separate rational data and
checker under `../affine-partition-20261105/`. Its scalar trace bound is
kernel-checked. Its finite cover and full geometric argument currently have
exact executable and written verification, with full Lean assembly pending.

## Reproduction

From `D:\awards\submissions\jsp-000404-wip-charlie` with the pinned toolchain
and existing dependency cache, run

```powershell
$env:LEAN_NUM_THREADS='2'
lake build JSP000404Research.TwoObserverGeometry JSP000404Research.IntervalPrivateDirections
lake build JSP000404Research
lake env lean verification/narrow-observer-20261105/Audit.lean
```

## Solver observations

`scripts/probe_narrow_observer_directions.py` uses Z3 5.3.3.0, installed locally
under the ignored directory `artifacts/python-deps`. Its JSON outputs record
one-top upper-strip searches at delta=99/100. Sizes 4, 7, 13 for n=2,3,4
returned `unsat`. The n=4 size-12 instance returned rational directions.
The n=5 size-25 instance returned `unknown` after a 180-second timeout.

For example, rerun

```powershell
python -B scripts/probe_narrow_observer_directions.py 4 13 --timeout 120
```

These solver outputs are outside the Lean proof chain. They neither certify
the all-delta claim nor the arbitrary-n conjecture. The supplied size-12 data
describe an abstract array of directions, with planar realization unproved.

## Upstream scope

The current upstream rule revision was rechecked as
`f8801a856529dce27e738c6b305e46d76e7c387c`. Complete original-problem solutions
and the associated proof evidence are required. The current results remain
downstream research. Submission correspondence, a final complete theorem, and
an immutable full-scope replay remain future acceptance obligations.
