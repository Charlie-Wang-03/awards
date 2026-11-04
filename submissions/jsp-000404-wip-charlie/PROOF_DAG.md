# JSP-000404 original-problem dependency ledger

Restoration date: 2026-11-05. Research only. The original problem is now stated
in Lean, but no theorem proving the full statement exists yet.

## Original statement and acceptance target

For every integer N >= 3, use N distinct points in the real Euclidean plane
and the unoriented angle in [0, pi] at the middle point of a pairwise distinct
triple. Let alpha(N) be the infimum, over those configurations, of their
maximum triple angle; equivalently it is the largest universally forced angle.
Collinear configurations are included. General position and convexity cannot
be added as hypotheses.

The target has BOTH faces:

1. Every configuration has a triple with angle >= a(N).
2. For every epsilon > 0 there is an injective N-point configuration with
   every triple angle < a(N) + epsilon.

Here a(3) = pi/3. For N >= 4 choose the unique n with
2^n < N <= 2^(n+1). The first interval ends at 2^n + 2^(n-2):

- N at or below that endpoint: a(N) = (1 - 2/(2*n+1))*pi.
- N above it: a(N) = (1 - 1/(n+1))*pi.

The power at n=1 must mean a real/integer-exponent power, not natural
subtraction: 2^(1-2) = 1/2. Thus N=4 is in the second interval; N=3 is
handled separately. Dyadic endpoints, both interval boundaries, and epsilon
sharpness must be checked. Attainment by ordinary points is not required.

Sources: upstream catalog at
`f8801a856529dce27e738c6b305e46d76e7c387c`,
[Erdos 504](https://www.erdosproblems.com/504), and Sendov,
*Minimax of the Angles in a Plane Configuration of Points*, Acta Math. Hungar.
69 (1995), 27–46, Theorem 4.1, printed p. 42
([digitized volume](https://real-j.mtak.hu/7467/)). The page image explicitly
has numerator 2. A formula assigned by definition to alpha is not a solution
of the geometric infimum problem.

## Mathematical DAG (statuses distinguish proof from conditional interfaces)

```text
Original all-N equality / lower + epsilon sharpness                  OPEN
|-- geometric extremum definition and exact finite-set correspondence LOCAL PASS
|-- arbitrary-N lower bound                                         OPEN
|   |-- actual cycles from injective planar points; order/cap transfer
|   |-- lower strip: t=n+delta, 0<=delta<1/2, sum 2^k <= 2^n          OPEN
|   |   |-- n=1, n=2; selected small-centre/exact-integer cases        PRESENT
|   |   `-- unrestricted geometric payment or equivalent capacity    OPEN
|   |       |-- genuine active choice for projected loss vertices
|   |       |-- terminal / twin / mixed / soft debts
|   |       |-- actual retained-edge covered blockers
|   |       |-- translated-loss duplicate debts
|   |       `-- disjoint payment into actual exterior holes plus
|   |           genuinely unreserved dyadic surplus                  OPEN
|   |-- upper strip: 1/2<=delta<1, sum 2^k <= 2^n+2^(n-2)            OPEN
|   `-- threshold inversion, endpoints, finite maximum               NOT ASSEMBLED
`-- ordinary matching constructions for all N and epsilon > 0        LOCAL PASS
```

`PRESENT` records a source result with historical focused evidence, not a
claim that the entire restored dependency closure currently builds locally.

The construction branch has a complete written ordinary-point proof in
[SHARPNESS_CONSTRUCTIONS.md](SHARPNESS_CONSTRUCTIONS.md). Its corresponding
all-N Lean theorem is now supplied by the pinned, attributed external upper
construction, transported in `OriginalUpperBound.lean`. Source commit
`3acbdd0ad52bebb3dd43dd86d380bf04a6eeb984` builds this target locally with
exit 0 (3,243 jobs). Its four printed statements use only the standard
three axioms. See [EXTERNAL_PROOF_ATTRIBUTION.md](EXTERNAL_PROOF_ATTRIBUTION.md).
The complete original statement is `OriginalProblem`; the proved equivalence
`originalProblem_iff_geometric_alpha_eq` ties it to the genuine geometric
supremum/infimum, without proving the remaining lower bound. The entire
research umbrella is still awaiting a successful build.

The exact remaining lower-strip premise is in
`PlanarLowerBranchActualEdgeCarrierFrontier.lean`:

```text
exists genuinely retained-active choice,
  terminalTwinOtherFiveDebt
  + card(actual same-colour covered blocker union)
  + translatedLossDuplicateDebt
  <= card(lossLedgerOutsideTranslatedTrueHoles)
     + terminalTwinAvailableSurplus.
```

The theorem `planar_lower_branch_capacity_of_actual_retainedEdge_payment`
only consumes this premise. The WIP theorem tries to supply it and leaves
the one executable sorry. `PlanarUpperBranchHardDefect` similarly consumes
an unproved hard-word payment bound with extra allowance 2^(n-2).
Neither conditional implication proves that geometry supplies the premise.

The original unweighted lower problem does not require proving the full
weighted statement for every generalized configuration. In a minimal
overweight induction, the historical unconditional-deletion counterexample
does not settle the issue: its mass is only 7<8. Its fixed-t geometric
realization has now been checked exactly at `t=17/5` (see Section 7 of
[the deletion audit](COMPENSATED_DELETION_HARD_STOP_2026-09-20.md)). A new
restricted deletion-or-capacity argument is still unproved; it must not be
inserted as an assumed induction step.

## Smaller sufficient targets for a replacement route

The weighted capacity route is sufficient, but the original lower bound can
also be obtained directly from the following two UNPROVED families, for every
integer n>=2 and every finite set of distinct planar points S:

    all triple angles < (1-2/(2*n+1))*pi  ==>  |S| <= 2^n;
    all triple angles < (1-1/(n+1))*pi    ==>  |S| <= 5*2^(n-2).

For the first interval of the classification, its N is greater than 2^n,
so the first implication gives the required angle by contraposition. For
the second interval, N>5*2^(n-2), and the second implication does the same.
The cases N=3,4 are treated separately. Conversely, the classification's
lower bound at the first integer above either threshold gives the displayed
implication, by taking a subset if |S| is larger. Thus these families isolate
the precise unweighted lower-bound problem; they are not new proved lemmas.

A strict finite cap at an endpoint can be lowered slightly while still
exceeding all finitely many angles. This is why an open lower strip
delta<1/2 suffices for the first family, and an open upper strip delta<1
for the second. Endpoint equality must not be inserted into an existing
strict-strip lemma. The sharpness constructions remain a separate obligation.

A direct proof of these two families would bypass the weighted payment DAG.
It is therefore unnecessary to insist on a false extremizer profile or on
a particular allocation mechanism if an unconditional geometric proof of
these exact cardinality thresholds can be found.

The proposed shortcut of choosing a common phase with at most one full
direction-band vertex is now FALSE, even for six ordinary integer points
and `t=349/100<7/2`. [The exact certificate](FULL_BAND_PHASE_COUNTEREXAMPLE.md)
checks all 60 angle conditions and every phase cell and endpoint. A second
integer witness also refutes the weaker universal claim that some phase has
full Hansel mass at least `2*|S|-1`: its mass is always between 8 and 10,
while `2*|S|-1=11`. Neither witness refutes the original lower bound.

## Source and public-proof audits

Sendov's Acta Lemma 4.1 (printed pp. 37–40) computes small cases, then states
maximizing exponent profiles for arbitrary s without deriving them from the
induction hypothesis. Independent inspection of pp. 39–40 confirms this
expository gap. Non-comb Kraft equality profiles alone do not disprove an
existential maximizing-profile claim; they only refute uniqueness or a
pointwise profile bound. A replacement capacity proof is still needed.

The assertion alpha(N(a))=a on printed p. 42 cannot hold for all real a:
an integer-valued N(a) is constant on the source's nontrivial intervals.
A generalized-inverse or epsilon argument is needed instead. This is separate
from the deeper geometric capacity gap.

- [#5131](https://github.com/TheJustinSunPrize/awards/pull/5131), aznikline,
  source `cbfbbef188f5f98eead6045d7c3548de3c1b701a`:
  independently read `Statement`, `SmallAngleLower`, `Induction`,
  `CertificateIntegration`, and `MainTheorem`. The final all-N lower theorem
  explicitly takes `GeometricCertificates`; that proposition quantifies the
  overweight deletion/emission certificate for all n>=3. The N<=8 result has
  no such premise. Its all-N upper constructions are attributed to
  superpilot69 and ChatGPT 6 Astra. This session has now independently built
  the 13-module upper closure, excluding `CertificateIntegration`, `Induction`,
  and `MainTheorem`; its lower results have not been independently replayed.
  API state is open, despite a maintainer comment saying
  it is being closed for partial scope; do not infer state from that comment.
- [#100](https://github.com/TheJustinSunPrize/awards/pull/100), zilan520:
  `d869ab901722fab0b2d980b38b7bd958cf52c128` claims exact N=5..10 and all
  dyadic values, including a kernel-checkable nine-point direction certificate.
- [#647](https://github.com/TheJustinSunPrize/awards/pull/647), hit1190100321:
  `2d0c118ba083a5a75609e8dd586e7a478b4a6dab` claims N=11..16 using a
  further finite certificate, with #100's geometric reduction and #42's upper
  constructions. These two claims were read, not independently kernel-replayed
  in this session. They cannot be promoted to arbitrary-n weighted capacity.
- [#300](https://github.com/TheJustinSunPrize/awards/pull/300),
  CollinYuanjieRen, `e80d0b209dc60257c1109ee8ea904ea0d7dd5ef4`, explicitly
  limits its theorem to small N, dyadic values, and all-N construction bounds.

No priority claim or new upstream submission is justified by this audit.

The additional public claim [#4684](https://github.com/TheJustinSunPrize/awards/pull/4684)
was rechecked on 2026-11-05: the PR is closed and unmerged, and its linked
`kunjunsong-code/jsp-000404-lean-proof` repository returns GitHub API 404 to
the available connection. Its stated proof is therefore unavailable for
independent inspection; no proof claim is inferred from its "zero sorry"
description. Fresh searches for JSP-000404 and Erdős 504 found no additional
unconditional all-N source among the returned relevant submissions.

## Excluded shortcuts

The retained historical witnesses rule out unconditional compensated deletion,
unique-comb or pointwise-comb assertions, coarse support-only capacity, arbitrary
local collision refunds, and unrestricted reuse of one opposite Boolean word.
An abstract bipartite K5 colouring can have active profile 3,3,2,2,2 and a
unique C4; a bad vertex can be pendant to that C4. A convex-C4 lemma cannot
therefore be applied without proving convexity and incidence. None of these
countermodels is itself a counterexample to the original planar statement.

The next proof attempt must derive a global geometric credit supply, or prove
weighted capacity directly. Rephrasing it as Hall, recording another fibre
ceiling, or adding finite cases does not close the unresolved DAG.

New exact geometric witness: [UPPER_FOUR_CENTRE_COUNTEREXAMPLE.md](UPPER_FOUR_CENTRE_COUNTEREXAMPLE.md)
rules out the stronger four-centre fixed-parameter upper bound 2^n+2^(n-3).
Unlike a merely abstract Kraft profile, it gives four rational points, all
actual triple angles, and every projective gap and floor. A separate written
two-level binary-circle construction gives a perfect GC with ten leaves and
exact GA=11*pi/15, refuting the source's printed four-centre maximum of nine.
Neither construction is Lean-certified yet; the full upper bound of ten is
respected, and the original classification is not refuted.

New recursion audit: [WIDTH_DROP_PARTITION_COUNTEREXAMPLE.md](WIDTH_DROP_PARTITION_COUNTEREXAMPLE.md)
gives five integer points at t=10/3 and t=15/4 for which no two-colouring produces two
unchanged subsets with AngleCap at t-1. All ten angle witnesses are checked
by strict integer dot-product inequalities. Any width-drop recursion would
need a genuinely new direction-changing construction and a proof that it
preserves the needed geometric invariants. The same note now proves failure
for every 3<t<4 by a five-point binary-family limit argument; restricting
the unchanged-subset recursion to the upper strip does not fix it.
