# JSP-000404 — Forward/reverse transport bridge-soft frontier (2026-10-12)

## Scope and verification status

Research branch: `research/jsp-000404-sharp-centre`.
Verified Lean umbrella: `JSP000404Research/VerifiedOverlapRewire.lean`.
Lean version/mathlib remain pinned by the repository.

**The award problem is NOT proven or disproven.**
The research-only `JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`
contains **one intentional, executable `sorry`**, and its `#print axioms`
reports `sorryAx`. It is **not imported** by the independent
`VerifiedOverlapRewire` entrypoint. The legacy monolithic root and
upper branch are not claimed to be closed.

### Starting certified background

The previous sorry-free chain had established:

- Every hard overlap carrier has its own full Boolean overlap face;
  distinct hard carriers do not share a vertex (a hard-carrier matching).
- Unpaid terminal rigid faces split **exactly** into strict-descending
  reverse-transportable faces and equal-target full-retained-incidence
  **twin** faces. These faces are disjoint, with exact twin dyadic mass.
- Both the outward forward map (all transportable hard faces) and the
  reverse strict-rigid full-face map are **separately globally injective**
  into already-COVERED singleton-or-soft Boolean words.
- Their cross-map intersection consists ONLY of SOFT completion overlap
  words. Any such collision forces a residual bridge
  `reverseLower < forwardUpper` with residual edge of the same two vertices.
- The earlier two-map capacity was
  `forwardMass + reverseMass <= singletonMass + 2*softMass`.
  This is a *covered sink* count, not a *true-hole* payment.

## New exact bridge owner and unique source provenance

**New module:** `JSP000404Research/ResidualForwardReverseBridgeSoftFaces.lean`.

Definitions:

```text
forwardReverseBridgeSoftCarriers C exponent
  = { (b,v) in softOverlapCarrierPairs C |
        exists p in transportableHardOverlapCarrierPairs C,
        exists q in netStrictDescentRigidCarriers C exponent,
          b = q.lower and v = p.upper }

forwardReverseBridgeSoftWords C exponent
  = UNION_((b,v) in bridgeSoftCarriers)
       (retainedCompletionWords C b INTER retainedCompletionWords C v)
```

Kernel-certified theorem
`forward_reverse_sink_collision_has_bridge_soft_owner` proves that
the **unique** ordered soft overlap carrier of a colliding output
word is EXACTLY `(reverseHard.lower, forwardHard.upper)`. The theorem
uses the verified residual bridge, hard-carrier matching, soft-only
classification and uniqueness of an ordered residual pair covering
one Boolean word.

In particular,

```text
forwardHardTransportSinkWords INTER reverseStrictRigidSinkWords
  SUBSET forwardReverseBridgeSoftWords
  SUBSET softOverlapCompletionWords.
```

This is not the claim that all candidate bridge faces actually
contain forward/reverse collisions. The candidate set may be larger.

Lean CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38208568882
(**3,209 jobs PASS**; three printed theorem axioms only
`propext`, `Classical.choice`, `Quot.sound`).

## Sharpened global joint capacity

**New module:** `JSP000404Research/ResidualForwardReverseBridgeCapacity.lean`.

Each global transport map is injective, and their image union lies in
the covered singleton-or-soft pool. The image intersection is within
the *bridge-soft* pool, not the whole soft pool. Finite-set
inclusion-exclusion therefore proves:

```text
card(ALL transportable hard overlap words)
+ card(strict-descending terminal rigid hard words)
<= card(singletonCompletionWords)
 + card(softOverlapCompletionWords)
 + card(forwardReverseBridgeSoftWords)
```

Also proven for the actually UNPAID forward hard subset, yielding:

```text
card(remainingUnpaidHardAfterMixedRigidWords)
<= singletonMass + softMass + bridgeSoftMass
 + SUM_(twinRigidCarrier p) 2 ^ exponent(p.upper).
```

The additional bridge-soft mass is bounded above by the full soft
mass. This is a (weakly) sharper structural inequality than the
earlier `singleton + 2*soft` estimate. **No numerical strictness
is claimed without knowing that the bridge pool is a proper subset.**

If the bridge pool is empty, a sorry-free conditional theorem yields
the one-copy `singleton + soft` joint capacity. Bridge emptiness
for genuine planar inputs is NOT proved.

Lean CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38208720172
(**3,210 jobs PASS**, five printed theorem axioms free of `sorryAx`).

## Exact dyadic weight of candidate bridge-soft faces

**New module:** `JSP000404Research/ResidualForwardReverseBridgeDyadicMass.lean`.

Different soft residual carriers have **disjoint** Boolean overlap
faces because a completion word determines its unique ordered
residual carrier. Each face has a certified cardinality
`2 ^ card(commonRetainedInactive C lower upper)`. Therefore:

```text
card(forwardReverseBridgeSoftWords C exponent)
 = SUM_(e in forwardReverseBridgeSoftCarriers C exponent)
      2 ^ card(commonRetainedInactive C e.lower e.upper).
```

Combining this equality with the capacity theorem:

```text
forwardMass + reverseStrictRigidMass
<= singletonMass + softMass
   + SUM_(e in bridgeSoftCarriers) 2 ^ commonInactiveDimension(e).
```

Likewise the entire unpaid hard remainder is at most this expression
plus the exact twin rigid target-weight sum.

**Important distinction:** the dyadic identity measures the total
POTENTIAL bridge-soft face union, **not** the number of actual
forward/reverse output collisions.

Lean CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38208876191
(**3,211 jobs PASS**, three new printed theorem axioms without `sorryAx`).

## Genuine planar AngleCap result and WIP linkage

**New module:** `JSP000404Research/PlanarForwardReverseBridgeDyadicCapacity.lean`.

Under actual injective planar input, `AngleCap p (pi/t)`,
`t = n + delta`, `0 <= delta < 1/2`, and the certified
`CentreProjectiveCycle` family, the theorem

`planar_mobile_hard_mass_le_singleton_soft_bridge_dyadic`

derives the exponent upper bound and one-layer projected-active
budget from geometry, and specializes the abstract dyadic inequality
to the **standard planar residual colouring** and
`centreExponent(cycle_i,t)`.

Kernel-certified CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38209545822
(**3,391 jobs PASS**, printed axioms only
`propext`, `Classical.choice`, `Quot.sound`).

Two earlier compilation failures on the planar module were purely
Lean interface problems, not mathematical counterexamples:

1. An attempted call to an undeclared `net_*_dyadic` theorem
   was replaced by the actual certified set-cardinality bound
   plus the independently certified dyadic mass equality
   (fix `e8021d7d6d165132ae693d89b71694eaaccd2258`).
2. The `rw` tactic did not unfold an outer chain of `let` binders;
   an explicit `change` of the planar target was added before
   the rewrite
   (fix `4dafbf69a2a49206205839ebc31e27578a059b02`).

The admitted WIP now introduces a certified local `hmobile` obtained
from this theorem, before the sole open global-payment subgoal.
This is an available valid auxiliary theorem **inside the WIP
context**, NOT a proof of its last inequality.

WIP regression:
https://github.com/Charlie-Wang-03/awards/actions/runs/38209708671
(**3,392 jobs PASS**, EXACTLY ONE executable `sorry`,
and expected `sorryAx`).

The independent umbrella imports the four new sorry-free files,
excluding WIP. Independent regression:
https://github.com/Charlie-Wang-03/awards/actions/runs/38209853255
(**3,470 jobs PASS**). A workflow preflight warning may mention
the intentionally admitted WIP; its axiom does not leak into the
sorry-free umbrella.

## Honest mathematical frontier

The admitted six-source net inequality is still:

```text
softOverlapMass
 + netForwardTransportableHardMass
 + netReverseStrictRigidHardMass
 + SUM_equalExponentTwinRigid 2^k(upper)
 + SUM_ascendingMixedRigid 2^k(lower)
 + SUM_descendingMixedRigid 2^k(upper)
 + projectedProfileLoss
<= TRUE Boolean holes
 + genuinely UNRESERVED profile surplus
   (after already-proved disjoint partial/full credits)
```

What remains genuinely unproved:

1. Convert the sharper covered-sink / bridge-soft capacity into a
   **valid true-hole or unreserved-surplus payment**. Such conversion
   is not a formal consequence of the present bound.
2. Exploit actual planar geometry to limit or pay the newly isolated
   oriented bridge-soft dyadic mass, without double counting sinks.
3. Control or rule out the exact equal-target fully twin rigid faces
   and the two earlier mixed-rigid target debts within the SAME
   final global budget.

**Do not infer** that narrow angles between residual directions
contradict `AngleCap`: here `AngleCap` is an UPPER bound
`angle <= pi - lambda`, not a lower bound. Thus residual
near-parallelism alone does not eliminate bridge carriers.

No arbitrary DirectionData Hall lemma has been assumed; no
nonstandard axiom was added; no global proof is claimed.
