# A coherent schedule obstructing prescribed interval colours

2026-11-05. This finite counterexample concerns an intermediate partition
rule for abstract crossing schedules. It has nine wires and half-period
9/2. The original B(4) cardinality ceiling is twenty. A Euclidean realization
of this particular weak event schedule is not supplied.

The candidate rule chooses a unit interval, colours every crossing pair in
that interval differently, and collapses the interval to reduce the period
by one. The example below admits no such colouring at any phase. This also
excludes the stronger prescription that every active wire receive its
canonical source/sink movement bit. Allowing the two colours to be interchanged
separately in different active components does not repair the fixed schedule.

## Parent schedule

The exact input is `verification/forced-compression-20261105/witness.json`.
It contains nine labels, initial order

    8, 5, 3, 1, 7, 6, 4, 2, 0,

and thirty-six timed crossing events. Every unordered pair appears once.
The listed pairs are adjacent when swapped, and the final order is the reverse
of the initial order. This is an explicit coherent crossing refinement.

The times are measured in quarter units. The period is eighteen, every event
time is an odd integer strictly between zero and eighteen, and the unit delay
is four. Every ordered triple satisfies betweenness, middle separation at
least four, and endpoint differences at most fourteen. Thus the parent
satisfies all the weak period-9/2 direction inequalities.

The input arose from a different shortest-path potential of a previously
tested nine-wire arrangement. It therefore tests the dependence on the
chosen optimal retiming. The earlier canonical potential of that arrangement
had a successful forced-colour phase.

## Exact exclusion for every phase

At phase phi, rotate the crossing list and transport its starting order.
For each event, set

    theta = (time-phi) mod 18,
    child_time = max(0,theta-4).

The child period is fourteen quarter units. A triple is bad if its middle
separation is below four or either endpoint gap exceeds ten. A two-colouring
works precisely when each bad triple has both colours. The additional rule
requires the endpoints of every event with 0<=theta<4 to have different colours.

The independent standard-library checker exhausts all 512 colourings in each
of twenty phase cases. None meets both requirements. It separately checks
the canonical movement-bit prescription and obtains the same obstruction.

The cases cover every real phase. Break the interval [0,18) at the odd
integers and at its endpoints. Check each included boundary and each open
interval's midpoint. The parent order and active edge set can change only
when an event crosses theta=0 or theta=4, which happens at an odd-integer
phase. Inside each remaining interval, every child time is either zero or
an affine function with slope minus one. The difference of two child times
has slope zero, one, or minus one. The checker verifies that no root of any
comparison with plus or minus four or ten lies inside an open interval.
Consequently every colouring constraint is constant there.

With free colour choices, phase zero does work. One verified partition is

    {0,2,3,4,5,6,8} and {1,7}.

Thus a successful collapse of this schedule must allow some same-colour
crossing inside the collapsed interval. The child schedule retains those
events at the collapsed time, with its inherited crossing refinement.

## Verification and scope

Run from the research project directory

```powershell
python -B scripts/check_forced_compression_obstruction.py
```

The checker validates the parent refinement and all parent inequalities,
exhausts the finite colouring cases, checks the affine phase thresholds, and
verifies the displayed free-colour partition. The result has a written proof
and exact executable verification. Its full Lean assembly is pending.

The unrestricted unit-collapse conjecture in `UNIT_INTERVAL_RETIMING_RESEARCH.md`
remains open. A version that first chooses a favourable retiming also remains
open. The counterexample identifies a constraint that cannot be imposed on
every fixed coherent schedule.
