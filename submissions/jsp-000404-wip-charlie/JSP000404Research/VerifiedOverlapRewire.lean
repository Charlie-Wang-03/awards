import JSP000404Research.ResidualCompletionOverlapRewire
import JSP000404Research.PlanarCrossingHardOverlapRewire
import JSP000404Research.ResidualCompletionIntersectionMass
import JSP000404Research.ResidualSafeFlipDoubleMatching
import JSP000404Research.ResidualHardSoftOverlapPartition
import JSP000404Research.ResidualHardFaceGlobalTransport
import JSP000404Research.ResidualRigidPaidDefectReduction
import JSP000404Research.PlanarLowerBranchPaidRigidReduction
import JSP000404Research.DirectionDataRigidHardTransportRefutation

/-!
# Verified local overlap-routing entrypoint for JSP-000404

Import this module to rebuild the actual kernel-checked local chain:
completion-cube accounting, exact global edge-owned Boolean-face overlap mass,
profile balance, safe-flip no-hole obstruction, triangular
exclusion, strict interior cube blocker, exact retained edge colour,
genuine planar AngleCap retained-separated residual rewire,\nand the globally injective hard-overlap WHOLE-FACE transport (conditional\non an available outward/inactive colour at every hard carrier).

The legacy all-modules entrypoint JSP000404Research.lean currently has
unrelated historical Lean failures and is not a proof certification target.
The admitted global-payment WIP theorem is deliberately NOT imported here.

The new full-face transport proves a global singleton+soft overlap mass bound,\nbut does NOT prove that the transport-colour hypothesis always holds.\nIts destinations are still covered words.\nThe main lower-branch global payment obligation remains OPEN.
-/
