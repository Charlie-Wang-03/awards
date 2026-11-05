# Projection-separated retiming obstruction

This stage follows checkpoint `258ba2380d7eaf89e3f321009bcf19890fcaccff`.
It reuses the exact twenty integer points in the earlier affine-partition
certificate. The original parent strict cap at width 23/5 and the separate
affine-map obstruction retain their earlier verification.

The new checker proves a different finite obstruction. It first checks a
cyclic parent potential of width 9/2. It constructs a generic projection by
an integer rotation and scale, then sorts every pair event by its exact
rational slope. Every event swaps adjacent projection ranks. The sweep
reverses the original order and yields 190 unordered nontrivial partitions.

Every strict separating line is a threshold of some projection. Between
successive pair directions the projection order is constant, and each
adjacent swap changes just one prefix subset. A half-turn covers all such
partitions up to complement. This establishes the completeness of the finite
list checked by the script.

For each partition, the checker constructs the two induced consecutive-wire
graphs. At least one has an explicit negative cycle for width 18/5. It checks
each cycle's endpoint connectivity and its strictly negative total
constraint weight. Telescoping the inequalities therefore excludes every
real time potential at that width. The selected cycle ratios are 4 for 137
partitions and 9/2 for the other 53.

The same checker verifies an unrestricted ten-plus-ten partition with feasible
independent child potentials. That partition is absent from the separator
list. The original family-B problem and unrestricted retiming partition
remain open. The finite obstruction has written geometric justification and
exact executable checks. Its full Lean assembly is pending.

## Reproduction

Python 3.12.13, standard library only. The command passed with exit 0 and its
output is in `check.log`. Run from the research project directory.

```powershell
python -B scripts/check_projection_partition_retiming.py
```

`source-sha256.json` records canonical UTF-8/LF hashes for the checker, its
shared exact graph routines, the retained point certificate and this stage's
research records. The family-A proof remains at
`449be4d2f099c853ea1f1e052456101b4106ace6`.
