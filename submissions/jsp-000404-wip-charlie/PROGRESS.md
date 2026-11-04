# JSP-000404 progress

Status: **INCOMPLETE — goal active; no complete mathematical or Lean proof.**
Updated: 2026-11-05 (Asia/Shanghai).

- Workspace: `D:\awards`; branch `codex/jsp-000404-goal-20261105`.
- Baseline: `d7e5c780362d09057102c651427fc1203b9165f2`, from
  `origin/research/jsp-000404-connector-compiler-repair-20261024`.
- Upstream rules inspected at `f8801a856529dce27e738c6b305e46d76e7c387c`.
  Main was not merged, reset, or modified. Existing research branches preserved.
- Pins: Lean `v4.34.0`; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
  No tracked manifest existed at restoration; a complete manifest now records
  the resolved dependencies. Official Windows toolchain archive SHA-256:
  `c07e88d1fe4839ec96a79f54637b2a3a983ea6c5b7e82ff35afa22a7700a86b7`.
  `lake exe cache get` completed with exit 0 (8,908 files).
  Initial root build suffered file-read failures while Windows reported
  insufficient memory. Task-owned stale LSP processes were stopped; the root
  build was restarted with process-local `LEAN_NUM_THREADS=2`, then interrupted
  to prioritize the canonical-order compiler repair. No local root PASS is
  claimed. Incremental outputs are preserved.
- Last locally verified Lean source commit:
  `ac8a70e12193092ac04221999c5bcd5c4a9ea2b6`.
  `lake build JSP000404Research.ProjectionOrderCanonicalOrder` passed
  (3,213 jobs); all four printed declarations have only
  `propext`, `Classical.choice`, `Quot.sound`. The repair explicitly uses
  `projectionLinearOrder hp` and first substitutes equal y-coordinates on
  horizontal edges. This is a focused bridge result, not root PASS.
- Last verified remote evidence: baseline's focused run
  [40653990253](https://github.com/Charlie-Wang-03/awards/actions/runs/40653990253)
  passed; it checks local eighth-source results, not the whole problem.
  The admitted-root run
  [40330564100](https://github.com/Charlie-Wang-03/awards/actions/runs/40330564100)
  checks `4501f656ddf9357e69a256a2bb515659f2ca6f2f` and explicitly prints
  `sorryAx`. Its successful build is not a proof.
- Local lexical audit: one executable `sorry`, in
  `PlanarLowerBranchProofAdmittedWIP.lean:935`. Strict audit exits 1.
- Static import inventory: 1,684 project modules including the umbrella;
  952 reachable from the umbrella, 732 not reached. The admitted module is
  not reachable from the umbrella. Its own closure has 451 modules.
  `ResidualQTTTCanonicalOrderRigidity` originally imported nonexistent
  `GenericProjectionCanonicalOrder`; the working tree corrects this to
  `ProjectionOrderCanonicalOrder` and scopes the geometric order in its
  dependent binders. That repair's build is still pending.
- Mathematical DAG reduction this session: **none yet**. See [PROOF_DAG.md](PROOF_DAG.md).
  General lower payment, general upper capacity, and the final original-problem
  assembly remain open. No new admission or unproved assumption was introduced.
- A concrete rational four-centre AngleCap witness refutes the source-inspired
  stronger upper estimate 9 at n=3, delta=3/4: its genuine exponents are
  [2,2,0,0], mass 10. The full proposed capacity 10 is respected.
  [Exact proof and scope](UPPER_FOUR_CENTRE_COUNTEREXAMPLE.md); not Lean-certified yet.
  A symbolic four-point family extends this obstruction to every odd n>=3,
  with genuine profile [n-1,n-1,n-3,n-3] at delta=3/4.
- A new direct two-part width-drop route is false even at t=10/3 in the
  lower strip: five integer points have AngleCap 7*pi/10, while every triple
  has an angle >3*pi/5>4*pi/7, the required child cap. See
  [exact certificate](WIDTH_DROP_PARTITION_COUNTEREXAMPLE.md).
  The companion integer checker passes all ten triples and 32 colourings.
  This excludes unchanged-subset recursion; it is not a Lean result or a
  main-DAG reduction.
- Sendov Acta pp. 39–40 and 42 independently inspected as page images.
  The arbitrary-centre induction still lacks the claimed profile derivation.
  The first classification numerator is 2. The blanket inverse equality needs
  replacement by a threshold/epsilon argument.
- Public prior work: #5131 has an explicit `GeometricCertificates` premise;
  #100 and #647 additionally claim checked finite certificates through N=16.
  These finite results do not prove general weighted capacity. No code copied.
- Evidence: ignored `artifacts/restore-20261105/` holds primary-source PDF,
  extracted text/page images, and downloaded historical CI logs. Do not upload
  third-party source PDFs or treat their presence as proof verification.

Next: finish the full umbrella and admitted-root builds,
repair actual compiler errors without changing geometric meaning, then attack
the unconditional all-centre payment (or a genuinely equivalent geometric
capacity proof). A finite-certificate import alone is not the goal.
