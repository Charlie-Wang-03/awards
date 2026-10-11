import JSP000404Research.ResidualCompletionOverlapRewire
import JSP000404Research.PlanarCrossingHardOverlapRewire
import JSP000404Research.ResidualCompletionIntersectionMass
import JSP000404Research.ResidualSafeFlipDoubleMatching
import JSP000404Research.ResidualHardSoftOverlapPartition

/-!
# Verified local overlap-routing entrypoint for JSP-000404

Import this module to rebuild the actual kernel-checked local chain:
completion-cube accounting, exact global edge-owned Boolean-face overlap mass,
profile balance, safe-flip no-hole obstruction, triangular
exclusion, strict interior cube blocker, exact retained edge colour,
and genuine planar AngleCap retained-separated residual rewire.

The legacy all-modules entrypoint JSP000404Research.lean currently has
unrelated historical Lean failures and is not a proof certification target.
The admitted global-payment WIP theorem is deliberately NOT imported here.

The main lower-branch global payment obligation remains OPEN.
-/
